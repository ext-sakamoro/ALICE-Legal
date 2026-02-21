//! Smart contract-like deterministic contract execution.
//!
//! All monetary amounts are represented as `i128` fixed-point ticks to avoid
//! floating-point non-determinism. No external dependencies are used.

use crate::hash_utils::fnv1a;

/// Unique identifier for a contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContractId(pub u64);

/// Unique identifier for a contracting party.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PartyId(pub u64);

/// Lifecycle state of a contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractStatus {
    /// Not yet activated.
    Draft,
    /// All conditions met; obligations may be pending.
    Active,
    /// All obligations have been fulfilled.
    Fulfilled,
    /// At least one obligation is past due and unfulfilled.
    Breached,
    /// Terminated by mutual agreement before completion.
    Terminated,
    /// The contract's validity period has lapsed.
    Expired,
}

/// A precondition that must be satisfied for the contract to proceed.
#[derive(Debug, Clone)]
pub struct Condition {
    /// FNV-1a hash of the human-readable condition description.
    pub description_hash: u64,
    /// FNV-1a hash identifying the evaluation logic/oracle.
    pub evaluator_hash: u64,
    /// Whether this condition has been marked as met.
    pub met: bool,
}

/// A duty for one party to transfer value to another by a deadline.
#[derive(Debug, Clone)]
pub struct Obligation {
    /// The party who owes the obligation.
    pub debtor: PartyId,
    /// The party who is owed.
    pub creditor: PartyId,
    /// Fixed-point amount in ticks (no floating-point).
    pub amount_ticks: i128,
    /// Deadline expressed as Unix nanoseconds.
    pub due_ns: u64,
    /// Whether this obligation has been discharged.
    pub fulfilled: bool,
}

/// A deterministic, machine-verifiable contract.
#[derive(Debug, Clone)]
pub struct Contract {
    /// Unique contract identifier.
    pub id: ContractId,
    /// All parties to this contract.
    pub parties: Vec<PartyId>,
    /// Current lifecycle status.
    pub status: ContractStatus,
    /// Preconditions that must all be met before obligations become active.
    pub conditions: Vec<Condition>,
    /// All obligations within this contract.
    pub obligations: Vec<Obligation>,
    /// Creation timestamp in Unix nanoseconds.
    pub created_ns: u64,
    /// FNV-1a hash computed from the party IDs and creation timestamp.
    pub content_hash: u64,
}

impl Contract {
    /// Create a new contract in [`ContractStatus::Draft`] state.
    ///
    /// # Arguments
    ///
    /// * `id` — Numeric contract identifier.
    /// * `parties` — Slice of party numeric IDs.
    /// * `created_ns` — Creation timestamp in Unix nanoseconds.
    pub fn new(id: u64, parties: &[u64], created_ns: u64) -> Self {
        // Deterministic hash: party IDs concatenated as bytes + created_ns bytes
        let mut hash_input = Vec::with_capacity(parties.len() * 8 + 8);
        for &p in parties {
            hash_input.extend_from_slice(&p.to_le_bytes());
        }
        hash_input.extend_from_slice(&created_ns.to_le_bytes());

        Self {
            id: ContractId(id),
            parties: parties.iter().map(|&p| PartyId(p)).collect(),
            status: ContractStatus::Draft,
            conditions: Vec::new(),
            obligations: Vec::new(),
            created_ns,
            content_hash: fnv1a(&hash_input),
        }
    }

    /// Add a precondition and return its index.
    ///
    /// # Arguments
    ///
    /// * `description` — Human-readable description; stored as FNV-1a hash.
    /// * `evaluator` — Identifier of the evaluation logic; stored as FNV-1a hash.
    pub fn add_condition(&mut self, description: &str, evaluator: &str) -> usize {
        let idx = self.conditions.len();
        self.conditions.push(Condition {
            description_hash: fnv1a(description.as_bytes()),
            evaluator_hash: fnv1a(evaluator.as_bytes()),
            met: false,
        });
        idx
    }

    /// Add an obligation and return its index.
    ///
    /// # Arguments
    ///
    /// * `debtor` — Party ID of the obligor.
    /// * `creditor` — Party ID of the obligee.
    /// * `amount_ticks` — Fixed-point amount (no floating-point).
    /// * `due_ns` — Deadline in Unix nanoseconds.
    pub fn add_obligation(
        &mut self,
        debtor: u64,
        creditor: u64,
        amount_ticks: i128,
        due_ns: u64,
    ) -> usize {
        let idx = self.obligations.len();
        self.obligations.push(Obligation {
            debtor: PartyId(debtor),
            creditor: PartyId(creditor),
            amount_ticks,
            due_ns,
            fulfilled: false,
        });
        idx
    }

    /// Mark an obligation as fulfilled.
    ///
    /// Returns `true` if the index was valid and the obligation was not already
    /// fulfilled; `false` otherwise.
    pub fn fulfill_obligation(&mut self, idx: usize) -> bool {
        match self.obligations.get_mut(idx) {
            Some(ob) if !ob.fulfilled => {
                ob.fulfilled = true;
                true
            }
            _ => false,
        }
    }

    /// Mark a condition as met.
    ///
    /// Returns `true` if the index was valid and the condition was not already
    /// met; `false` otherwise.
    pub fn meet_condition(&mut self, idx: usize) -> bool {
        match self.conditions.get_mut(idx) {
            Some(cond) if !cond.met => {
                cond.met = true;
                true
            }
            _ => false,
        }
    }

    /// Automatically update the contract status based on the current time.
    ///
    /// Rules (evaluated in priority order):
    ///
    /// 1. If any obligation is past `due_ns` and unfulfilled → [`ContractStatus::Breached`].
    /// 2. Else if all obligations are fulfilled → [`ContractStatus::Fulfilled`].
    /// 3. Else if status is [`ContractStatus::Terminated`] or
    ///    [`ContractStatus::Expired`] → no change.
    ///
    /// The status will not be downgraded from `Terminated` or `Expired`.
    pub fn check_status(&mut self, now_ns: u64) {
        // Do not override terminal states set externally
        if matches!(
            self.status,
            ContractStatus::Terminated | ContractStatus::Expired
        ) {
            return;
        }

        // Priority 1: Breached
        let any_breached = self.obligations.iter().any(|ob| {
            !ob.fulfilled && now_ns > ob.due_ns
        });
        if any_breached {
            self.status = ContractStatus::Breached;
            return;
        }

        // Priority 2: Fulfilled (only if there is at least one obligation)
        if !self.obligations.is_empty() && self.obligations.iter().all(|ob| ob.fulfilled) {
            self.status = ContractStatus::Fulfilled;
            return;
        }

        // Otherwise remain Active (if it was Draft, promote it)
        if self.status == ContractStatus::Draft {
            self.status = ContractStatus::Active;
        }
    }

    /// Sum of all obligation amounts in fixed-point ticks.
    pub fn total_obligation(&self) -> i128 {
        self.obligations.iter().map(|ob| ob.amount_ticks).sum()
    }

    /// Number of obligations that have not yet been fulfilled.
    pub fn unfulfilled_count(&self) -> usize {
        self.obligations.iter().filter(|ob| !ob.fulfilled).count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const NS: u64 = 1_000_000_000;

    #[test]
    fn test_create_contract_with_two_parties() {
        let c = Contract::new(1, &[10, 20], 0);
        assert_eq!(c.id, ContractId(1));
        assert_eq!(c.parties.len(), 2);
        assert_eq!(c.parties[0], PartyId(10));
        assert_eq!(c.parties[1], PartyId(20));
        assert_eq!(c.status, ContractStatus::Draft);
    }

    #[test]
    fn test_add_and_fulfill_obligation() {
        let mut c = Contract::new(2, &[1, 2], 0);
        let idx = c.add_obligation(1, 2, 1_000_000, 100 * NS);
        assert_eq!(c.unfulfilled_count(), 1);

        let ok = c.fulfill_obligation(idx);
        assert!(ok);
        assert_eq!(c.unfulfilled_count(), 0);

        // Fulfilling again returns false
        assert!(!c.fulfill_obligation(idx));
    }

    #[test]
    fn test_status_becomes_fulfilled_when_all_obligations_met() {
        let mut c = Contract::new(3, &[1, 2], 0);
        let i1 = c.add_obligation(1, 2, 500, 100 * NS);
        let i2 = c.add_obligation(2, 1, 200, 100 * NS);

        c.fulfill_obligation(i1);
        c.fulfill_obligation(i2);
        c.check_status(50 * NS); // well before due date

        assert_eq!(c.status, ContractStatus::Fulfilled);
    }

    #[test]
    fn test_status_becomes_breached_when_obligation_past_due() {
        let mut c = Contract::new(4, &[1, 2], 0);
        c.add_obligation(1, 2, 999, 10 * NS); // due at 10s
        // Not fulfilled, check at 11s
        c.check_status(11 * NS);
        assert_eq!(c.status, ContractStatus::Breached);
    }

    #[test]
    fn test_i128_total_obligation_calculation() {
        let mut c = Contract::new(5, &[1, 2, 3], 0);
        c.add_obligation(1, 2, 1_000_000_000_000_i128, 100 * NS);
        c.add_obligation(2, 3, 2_000_000_000_000_i128, 100 * NS);
        c.add_obligation(3, 1, 500_000_000_000_i128, 100 * NS);

        assert_eq!(c.total_obligation(), 3_500_000_000_000_i128);
    }

    #[test]
    fn test_unfulfilled_count_decrements_on_fulfill() {
        let mut c = Contract::new(6, &[1, 2], 0);
        let i1 = c.add_obligation(1, 2, 100, 100 * NS);
        let i2 = c.add_obligation(1, 2, 200, 100 * NS);
        let i3 = c.add_obligation(2, 1, 50, 100 * NS);

        assert_eq!(c.unfulfilled_count(), 3);
        c.fulfill_obligation(i1);
        assert_eq!(c.unfulfilled_count(), 2);
        c.fulfill_obligation(i2);
        assert_eq!(c.unfulfilled_count(), 1);
        c.fulfill_obligation(i3);
        assert_eq!(c.unfulfilled_count(), 0);
    }

    #[test]
    fn test_add_condition_and_meet() {
        let mut c = Contract::new(7, &[1, 2], 0);
        let idx = c.add_condition("Regulatory approval obtained", "oracle-regulator");
        assert!(!c.conditions[idx].met);

        let ok = c.meet_condition(idx);
        assert!(ok);
        assert!(c.conditions[idx].met);

        // Meeting again returns false
        assert!(!c.meet_condition(idx));
    }

    #[test]
    fn test_content_hash_nonzero() {
        let c = Contract::new(10, &[1, 2], 1_000_000);
        assert_ne!(c.content_hash, 0);
    }

    #[test]
    fn test_content_hash_deterministic_same_inputs() {
        let c1 = Contract::new(11, &[5, 6, 7], 999_999);
        let c2 = Contract::new(11, &[5, 6, 7], 999_999);
        assert_eq!(c1.content_hash, c2.content_hash);
    }

    #[test]
    fn test_content_hash_differs_for_different_parties() {
        let c1 = Contract::new(12, &[1, 2], 0);
        let c2 = Contract::new(12, &[3, 4], 0);
        assert_ne!(c1.content_hash, c2.content_hash);
    }

    #[test]
    fn test_content_hash_differs_for_different_timestamps() {
        let c1 = Contract::new(13, &[1, 2], 0);
        let c2 = Contract::new(13, &[1, 2], 1);
        assert_ne!(c1.content_hash, c2.content_hash);
    }

    #[test]
    fn test_no_parties_contract() {
        // A zero-party contract is technically valid structurally
        let c = Contract::new(14, &[], 0);
        assert!(c.parties.is_empty());
        assert_eq!(c.status, ContractStatus::Draft);
    }

    #[test]
    fn test_single_party_contract() {
        let c = Contract::new(15, &[99], 0);
        assert_eq!(c.parties.len(), 1);
        assert_eq!(c.parties[0], PartyId(99));
    }

    #[test]
    fn test_total_obligation_zero_when_empty() {
        let c = Contract::new(16, &[1, 2], 0);
        assert_eq!(c.total_obligation(), 0);
    }

    #[test]
    fn test_total_obligation_with_negative_amounts() {
        // i128 allows negative ticks (e.g. credits/refunds)
        let mut c = Contract::new(17, &[1, 2], 0);
        c.add_obligation(1, 2, 1_000, 100 * NS);
        c.add_obligation(2, 1, -500, 100 * NS);
        assert_eq!(c.total_obligation(), 500);
    }

    #[test]
    fn test_fulfill_obligation_invalid_index_returns_false() {
        let mut c = Contract::new(18, &[1, 2], 0);
        // No obligations yet
        assert!(!c.fulfill_obligation(0));
        assert!(!c.fulfill_obligation(usize::MAX));
    }

    #[test]
    fn test_meet_condition_invalid_index_returns_false() {
        let mut c = Contract::new(19, &[1, 2], 0);
        assert!(!c.meet_condition(0));
        assert!(!c.meet_condition(999));
    }

    #[test]
    fn test_condition_hashes_nonzero() {
        let mut c = Contract::new(20, &[1, 2], 0);
        let idx = c.add_condition("payment cleared", "bank-oracle");
        assert_ne!(c.conditions[idx].description_hash, 0);
        assert_ne!(c.conditions[idx].evaluator_hash, 0);
    }

    #[test]
    fn test_condition_different_descriptions_differ() {
        let mut c = Contract::new(21, &[1, 2], 0);
        let idx1 = c.add_condition("condition A", "oracle-X");
        let idx2 = c.add_condition("condition B", "oracle-X");
        assert_ne!(
            c.conditions[idx1].description_hash,
            c.conditions[idx2].description_hash
        );
    }

    #[test]
    fn test_check_status_no_obligations_stays_draft_then_active() {
        let mut c = Contract::new(22, &[1, 2], 0);
        // No obligations: check_status promotes Draft -> Active
        c.check_status(0);
        assert_eq!(c.status, ContractStatus::Active);
    }

    #[test]
    fn test_check_status_does_not_override_terminated() {
        let mut c = Contract::new(23, &[1, 2], 0);
        c.add_obligation(1, 2, 100, 0); // already past due
        c.status = ContractStatus::Terminated;
        c.check_status(1_000 * NS); // would normally be Breached
        assert_eq!(c.status, ContractStatus::Terminated);
    }

    #[test]
    fn test_check_status_does_not_override_expired() {
        let mut c = Contract::new(24, &[1, 2], 0);
        c.add_obligation(1, 2, 100, 0);
        c.status = ContractStatus::Expired;
        c.check_status(1_000 * NS);
        assert_eq!(c.status, ContractStatus::Expired);
    }

    #[test]
    fn test_all_contract_status_variants_are_distinct() {
        // Ensure enum variants compare correctly
        let statuses = [
            ContractStatus::Draft,
            ContractStatus::Active,
            ContractStatus::Fulfilled,
            ContractStatus::Breached,
            ContractStatus::Terminated,
            ContractStatus::Expired,
        ];
        for i in 0..statuses.len() {
            for j in 0..statuses.len() {
                if i == j {
                    assert_eq!(statuses[i], statuses[j]);
                } else {
                    assert_ne!(statuses[i], statuses[j]);
                }
            }
        }
    }

    #[test]
    fn test_contract_id_and_party_id_wrap_values() {
        let c = Contract::new(55, &[100, 200], 0);
        assert_eq!(c.id, ContractId(55));
        assert_eq!(c.id.0, 55);
        assert_eq!(c.parties[0], PartyId(100));
        assert_eq!(c.parties[0].0, 100);
    }

    #[test]
    fn test_large_i128_obligation_does_not_overflow() {
        let mut c = Contract::new(60, &[1, 2], 0);
        c.add_obligation(1, 2, i128::MAX / 2, 100 * NS);
        c.add_obligation(2, 1, i128::MAX / 2, 100 * NS);
        // Should not panic; just check it sums
        let total = c.total_obligation();
        assert!(total > 0);
    }
}
