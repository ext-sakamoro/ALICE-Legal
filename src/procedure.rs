//! Administrative procedure modelled as a tamper-evident event stream.
//!
//! Each [`ProcedureStep`] chains to the previous via a hash of the prior
//! step's `content_hash` XOR `prev_hash`. This allows [`Procedure::verify_chain`]
//! to detect any post-hoc modification without an external database.

use crate::hash_utils::fnv1a;

/// Unique identifier for an administrative procedure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProcedureId(pub u64);

/// The type of action taken at each step of a procedure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepKind {
    /// Initial submission by a citizen or entity.
    Application,
    /// Examination by a competent authority.
    Review,
    /// Positive decision by the authority.
    Approval,
    /// Negative decision by the authority.
    Rejection,
    /// Modification of a prior submission or decision.
    Amendment,
    /// Formal communication to a party.
    Notification,
    /// Final closure of the procedure.
    Completion,
}

/// A single immutable step recorded in a procedure's event log.
#[derive(Debug, Clone)]
pub struct ProcedureStep {
    /// Zero-based position in the event stream.
    pub sequence: u32,
    /// The kind of administrative action taken.
    pub kind: StepKind,
    /// FNV-1a hash of the actor's identity string.
    pub actor_hash: u64,
    /// When this step occurred, in Unix nanoseconds.
    pub timestamp_ns: u64,
    /// FNV-1a hash of the step's content/payload string.
    pub content_hash: u64,
    /// Chain hash linking to the previous step for tamper detection.
    ///
    /// Computed as `fnv1a( prev.content_hash.to_le_bytes() ++ prev.prev_hash.to_le_bytes() )`
    /// for all steps except the first (where it is `0`).
    pub prev_hash: u64,
}

/// The overall lifecycle state of an administrative procedure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcedureStatus {
    /// Created but no steps recorded yet.
    Pending,
    /// At least one step has been recorded.
    InProgress,
    /// An approval step was the final action.
    Approved,
    /// A rejection step was the final action.
    Rejected,
    /// A completion step was recorded.
    Completed,
}

/// An administrative procedure represented as a tamper-evident event stream.
#[derive(Debug, Clone)]
pub struct Procedure {
    /// Unique procedure identifier.
    pub id: ProcedureId,
    /// Ordered list of steps (append-only in normal operation).
    pub steps: Vec<ProcedureStep>,
    /// Current lifecycle status.
    pub status: ProcedureStatus,
}

impl Procedure {
    /// Create a new, empty procedure in [`ProcedureStatus::Pending`] state.
    pub fn new(id: u64) -> Self {
        Self {
            id: ProcedureId(id),
            steps: Vec::new(),
            status: ProcedureStatus::Pending,
        }
    }

    /// Append a step to the procedure's event stream.
    ///
    /// The `prev_hash` of the new step is computed from the previous step's
    /// `content_hash` and `prev_hash`, creating a verifiable chain. For the
    /// first step the `prev_hash` is `0`.
    ///
    /// The procedure status is updated to reflect the new step kind:
    /// - [`StepKind::Approval`] → [`ProcedureStatus::Approved`]
    /// - [`StepKind::Rejection`] → [`ProcedureStatus::Rejected`]
    /// - [`StepKind::Completion`] → [`ProcedureStatus::Completed`]
    /// - Other kinds → [`ProcedureStatus::InProgress`] (unless already terminal)
    pub fn add_step(
        &mut self,
        kind: StepKind,
        actor: &str,
        content: &str,
        timestamp_ns: u64,
    ) {
        let sequence = self.steps.len() as u32;
        let content_hash = fnv1a(content.as_bytes());
        let actor_hash = fnv1a(actor.as_bytes());

        let prev_hash = match self.steps.last() {
            None => 0u64,
            Some(prev) => {
                let mut buf = [0u8; 16];
                buf[..8].copy_from_slice(&prev.content_hash.to_le_bytes());
                buf[8..].copy_from_slice(&prev.prev_hash.to_le_bytes());
                fnv1a(&buf)
            }
        };

        self.steps.push(ProcedureStep {
            sequence,
            kind,
            actor_hash,
            timestamp_ns,
            content_hash,
            prev_hash,
        });

        // Update status
        self.status = match kind {
            StepKind::Approval => ProcedureStatus::Approved,
            StepKind::Rejection => ProcedureStatus::Rejected,
            StepKind::Completion => ProcedureStatus::Completed,
            _ => {
                if self.status == ProcedureStatus::Pending {
                    ProcedureStatus::InProgress
                } else {
                    self.status
                }
            }
        };
    }

    /// Verify the integrity of the hash chain across all recorded steps.
    ///
    /// Returns `true` if every step's `prev_hash` matches the hash recomputed
    /// from the previous step's `content_hash` and `prev_hash`.
    pub fn verify_chain(&self) -> bool {
        for i in 1..self.steps.len() {
            let prev = &self.steps[i - 1];
            let current = &self.steps[i];

            let mut buf = [0u8; 16];
            buf[..8].copy_from_slice(&prev.content_hash.to_le_bytes());
            buf[8..].copy_from_slice(&prev.prev_hash.to_le_bytes());
            let expected = fnv1a(&buf);

            if current.prev_hash != expected {
                return false;
            }
        }
        true
    }

    /// Return a reference to the most recently recorded step, or `None` if
    /// the procedure has no steps yet.
    pub fn latest_step(&self) -> Option<&ProcedureStep> {
        self.steps.last()
    }

    /// Append a [`StepKind::Completion`] step and set status to
    /// [`ProcedureStatus::Completed`].
    pub fn complete(&mut self, actor: &str, timestamp_ns: u64) {
        self.add_step(StepKind::Completion, actor, "procedure-completed", timestamp_ns);
    }

    /// Append a [`StepKind::Rejection`] step with a reason payload and set
    /// status to [`ProcedureStatus::Rejected`].
    pub fn reject(&mut self, actor: &str, reason: &str, timestamp_ns: u64) {
        self.add_step(StepKind::Rejection, actor, reason, timestamp_ns);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const NS: u64 = 1_000_000_000;

    #[test]
    fn test_create_procedure_and_add_steps() {
        let mut proc = Procedure::new(1);
        assert_eq!(proc.status, ProcedureStatus::Pending);
        assert!(proc.steps.is_empty());

        proc.add_step(StepKind::Application, "citizen-001", "initial permit application", NS);
        proc.add_step(StepKind::Review, "officer-042", "documents reviewed", 2 * NS);

        assert_eq!(proc.steps.len(), 2);
        assert_eq!(proc.steps[0].sequence, 0);
        assert_eq!(proc.steps[1].sequence, 1);
        assert_eq!(proc.status, ProcedureStatus::InProgress);
    }

    #[test]
    fn test_hash_chain_verification_valid() {
        let mut proc = Procedure::new(2);
        proc.add_step(StepKind::Application, "alice", "step one", NS);
        proc.add_step(StepKind::Review, "bob", "step two", 2 * NS);
        proc.add_step(StepKind::Approval, "carol", "step three", 3 * NS);

        assert!(proc.verify_chain());
        // First step always has prev_hash == 0
        assert_eq!(proc.steps[0].prev_hash, 0);
    }

    #[test]
    fn test_tampered_chain_fails_verification() {
        let mut proc = Procedure::new(3);
        proc.add_step(StepKind::Application, "alice", "original content", NS);
        proc.add_step(StepKind::Review, "bob", "review ok", 2 * NS);
        proc.add_step(StepKind::Approval, "carol", "approved", 3 * NS);

        assert!(proc.verify_chain());

        // Tamper with the middle step's content_hash
        proc.steps[1].content_hash ^= 0xDEAD_BEEF_CAFE_1234;

        assert!(!proc.verify_chain());
    }

    #[test]
    fn test_complete_procedure() {
        let mut proc = Procedure::new(4);
        proc.add_step(StepKind::Application, "user", "application", NS);
        proc.add_step(StepKind::Review, "clerk", "reviewed", 2 * NS);
        proc.complete("director", 3 * NS);

        assert_eq!(proc.status, ProcedureStatus::Completed);
        let last = proc.latest_step().unwrap();
        assert_eq!(last.kind, StepKind::Completion);
        assert!(proc.verify_chain());
    }

    #[test]
    fn test_reject_procedure() {
        let mut proc = Procedure::new(5);
        proc.add_step(StepKind::Application, "user", "application", NS);
        proc.reject("officer", "missing documents", 2 * NS);

        assert_eq!(proc.status, ProcedureStatus::Rejected);
        let last = proc.latest_step().unwrap();
        assert_eq!(last.kind, StepKind::Rejection);
        assert!(proc.verify_chain());
    }

    #[test]
    fn test_latest_step() {
        let mut proc = Procedure::new(6);
        assert!(proc.latest_step().is_none());

        proc.add_step(StepKind::Application, "user", "first", NS);
        proc.add_step(StepKind::Review, "clerk", "second", 2 * NS);

        let latest = proc.latest_step().unwrap();
        assert_eq!(latest.sequence, 1);
        assert_eq!(latest.kind, StepKind::Review);
    }
}
