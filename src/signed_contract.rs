//! `SHA-256` + `Ed25519` signed contract records.
//!
//! Wraps the existing contract execution primitives with a cryptographically
//! anchored envelope suitable for regulatory audit: contracts are hashed
//! with `SHA-256`, signed with `Ed25519` by each participating party, and
//! aggregated into a hash-chain committed to via [`ContractLog`].
//!
//! Consumers can further anchor the chain into an external ledger by taking
//! its [`ContractLog::head`] hash and publishing it on
//! [`alice_blockchain::Blockchain`].

use alice_blockchain::{hash_data, Hash, KeyPair, MerkleTree, PublicKey, Signature};
use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// ContractRecord
// ---------------------------------------------------------------------------

/// A single contract event with structured fields plus arbitrary metadata.
#[derive(Debug, Clone)]
pub struct ContractRecord {
    pub id: String,
    pub kind: String,
    pub issuer_did: String,
    pub counterparty_did: String,
    pub effective_unix: u64,
    pub metadata: BTreeMap<String, String>,
}

impl ContractRecord {
    /// Convenience constructor.
    #[must_use]
    pub fn new(
        id: impl Into<String>,
        kind: impl Into<String>,
        issuer_did: impl Into<String>,
        counterparty_did: impl Into<String>,
        effective_unix: u64,
    ) -> Self {
        Self {
            id: id.into(),
            kind: kind.into(),
            issuer_did: issuer_did.into(),
            counterparty_did: counterparty_did.into(),
            effective_unix,
            metadata: BTreeMap::new(),
        }
    }

    /// Canonical byte serialisation used by hash and signature computation.
    #[must_use]
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(128);
        push_len(&mut buf, self.id.as_bytes());
        push_len(&mut buf, self.kind.as_bytes());
        push_len(&mut buf, self.issuer_did.as_bytes());
        push_len(&mut buf, self.counterparty_did.as_bytes());
        buf.extend_from_slice(&self.effective_unix.to_le_bytes());
        buf.extend_from_slice(&(self.metadata.len() as u64).to_le_bytes());
        for (k, v) in &self.metadata {
            push_len(&mut buf, k.as_bytes());
            push_len(&mut buf, v.as_bytes());
        }
        buf
    }

    /// `SHA-256` digest.
    #[must_use]
    pub fn digest(&self) -> Hash {
        hash_data(&self.canonical_bytes())
    }
}

// ---------------------------------------------------------------------------
// SignedContract
// ---------------------------------------------------------------------------

/// A contract record signed by one or more parties.
#[derive(Debug, Clone)]
pub struct SignedContract {
    pub record: ContractRecord,
    pub signatures: Vec<(PublicKey, Signature)>,
}

impl SignedContract {
    /// Empty signed contract skeleton.
    #[must_use]
    pub fn new(record: ContractRecord) -> Self {
        Self {
            record,
            signatures: Vec::new(),
        }
    }

    /// Attach a signature from the given key pair.
    pub fn sign(&mut self, kp: &KeyPair) {
        let sig = kp.sign(&self.record.canonical_bytes());
        self.signatures.push((kp.public(), sig));
    }

    /// Verify that every attached signature matches the recorded contract.
    #[must_use]
    pub fn verify(&self) -> bool {
        let payload = self.record.canonical_bytes();
        self.signatures
            .iter()
            .all(|(pk, sig)| pk.verify(&payload, sig))
    }

    /// Verify AND ensure at least `min_signers` distinct signers are present.
    #[must_use]
    pub fn verify_threshold(&self, min_signers: usize) -> bool {
        if !self.verify() {
            return false;
        }
        let mut seen = std::collections::HashSet::new();
        for (pk, _) in &self.signatures {
            seen.insert(pk.0);
        }
        seen.len() >= min_signers
    }
}

// ---------------------------------------------------------------------------
// ContractLog
// ---------------------------------------------------------------------------

/// Append-only hash-chain of signed contract events.
#[derive(Debug, Clone, Default)]
pub struct ContractLog {
    contracts: Vec<SignedContract>,
    chain: Vec<Hash>,
}

impl ContractLog {
    /// Empty log.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            contracts: Vec::new(),
            chain: Vec::new(),
        }
    }

    /// Append a contract and update the chain head.
    pub fn append(&mut self, contract: SignedContract) {
        let prev = self.chain.last().copied().unwrap_or_else(Hash::zero);
        let content_hash = contract.record.digest();
        let mut linked = Vec::with_capacity(64);
        linked.extend_from_slice(&prev.0);
        linked.extend_from_slice(&content_hash.0);
        let head = hash_data(&linked);
        self.contracts.push(contract);
        self.chain.push(head);
    }

    /// Current chain head, or the zero hash for an empty log.
    #[must_use]
    pub fn head(&self) -> Hash {
        self.chain.last().copied().unwrap_or_else(Hash::zero)
    }

    /// Full chain of hashes (position-aligned with [`Self::contracts`]).
    #[must_use]
    pub fn chain(&self) -> &[Hash] {
        &self.chain
    }

    /// The contracts, in insertion order.
    #[must_use]
    pub fn contracts(&self) -> &[SignedContract] {
        &self.contracts
    }

    /// Verify every attached signature and the chain linkage.
    #[must_use]
    pub fn verify(&self) -> bool {
        let mut prev = Hash::zero();
        for (c, expected) in self.contracts.iter().zip(self.chain.iter()) {
            if !c.verify() {
                return false;
            }
            let mut linked = Vec::with_capacity(64);
            linked.extend_from_slice(&prev.0);
            linked.extend_from_slice(&c.record.digest().0);
            let head = hash_data(&linked);
            if head != *expected {
                return false;
            }
            prev = head;
        }
        true
    }

    /// Compute a Merkle root over every contract digest, suitable for
    /// external anchoring.
    #[must_use]
    pub fn merkle_root(&self) -> Option<Hash> {
        if self.contracts.is_empty() {
            return None;
        }
        let leaves: Vec<Hash> = self.contracts.iter().map(|c| c.record.digest()).collect();
        Some(MerkleTree::build(&leaves).root())
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn push_len(buf: &mut Vec<u8>, bytes: &[u8]) {
    buf.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    buf.extend_from_slice(bytes);
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn record(id: &str) -> ContractRecord {
        ContractRecord::new(id, "sale", "did:issuer:1", "did:party:2", 1_720_000_000)
    }

    #[test]
    fn unsigned_contract_verifies_trivially() {
        let sc = SignedContract::new(record("C-1"));
        assert!(sc.verify());
    }

    #[test]
    fn single_signature_verifies() {
        let kp = KeyPair::from_seed([1u8; 32]);
        let mut sc = SignedContract::new(record("C-1"));
        sc.sign(&kp);
        assert!(sc.verify());
    }

    #[test]
    fn tampered_record_breaks_signature() {
        let kp = KeyPair::from_seed([1u8; 32]);
        let mut sc = SignedContract::new(record("C-1"));
        sc.sign(&kp);
        sc.record.id = "C-2".into();
        assert!(!sc.verify());
    }

    #[test]
    fn threshold_counts_distinct_signers() {
        let a = KeyPair::from_seed([1u8; 32]);
        let b = KeyPair::from_seed([2u8; 32]);
        let mut sc = SignedContract::new(record("C-1"));
        sc.sign(&a);
        sc.sign(&b);
        assert!(sc.verify_threshold(2));
        assert!(!sc.verify_threshold(3));
    }

    #[test]
    fn empty_log_head_is_zero_hash() {
        let log = ContractLog::new();
        assert_eq!(log.head(), Hash::zero());
        assert!(log.merkle_root().is_none());
    }

    #[test]
    fn log_head_advances_with_appends() {
        let a = KeyPair::from_seed([1u8; 32]);
        let mut log = ContractLog::new();
        let mut c1 = SignedContract::new(record("C-1"));
        c1.sign(&a);
        log.append(c1);
        let head1 = log.head();
        let mut c2 = SignedContract::new(record("C-2"));
        c2.sign(&a);
        log.append(c2);
        assert_ne!(head1, log.head());
        assert!(log.verify());
    }

    #[test]
    fn tampering_contract_breaks_log_verification() {
        let a = KeyPair::from_seed([1u8; 32]);
        let mut log = ContractLog::new();
        let mut c1 = SignedContract::new(record("C-1"));
        c1.sign(&a);
        log.append(c1);
        // Simulate an attacker mutating the stored record.
        log.contracts[0].record.id = "attacker".into();
        assert!(!log.verify());
    }

    #[test]
    fn merkle_root_matches_manual_build() {
        let a = KeyPair::from_seed([1u8; 32]);
        let mut log = ContractLog::new();
        for i in 0..4 {
            let mut c = SignedContract::new(record(&format!("C-{i}")));
            c.sign(&a);
            log.append(c);
        }
        let root = log.merkle_root().unwrap();
        let leaves: Vec<Hash> = log.contracts().iter().map(|c| c.record.digest()).collect();
        assert_eq!(root, MerkleTree::build(&leaves).root());
    }
}
