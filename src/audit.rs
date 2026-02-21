//! Immutable audit trail for all legal operations.
//!
//! Every significant event in the ALICE-Legal system (statute creation,
//! contract fulfilment, procedure completion, etc.) should be recorded via
//! [`AuditLog::append`]. The log is append-only and exposes read-only query
//! helpers for compliance reporting.

use std::collections::HashMap;

use crate::hash_utils::fnv1a;

/// The category of legal event recorded in the audit log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuditEventKind {
    /// A new statute was compiled and added to the legal tree.
    StatuteCreated,
    /// An existing statute was amended (version bumped).
    StatuteAmended,
    /// A new contract was created.
    ContractCreated,
    /// All obligations in a contract were fulfilled.
    ContractFulfilled,
    /// A contract entered the Breached state.
    ContractBreached,
    /// An administrative procedure was opened.
    ProcedureStarted,
    /// An administrative procedure reached Completed status.
    ProcedureCompleted,
    /// An administrative procedure was rejected.
    ProcedureRejected,
}

/// A single, immutable record in the audit log.
#[derive(Debug, Clone)]
pub struct AuditEntry {
    /// Monotonically increasing position in the log (starts at 0).
    pub sequence: u64,
    /// The category of event.
    pub kind: AuditEventKind,
    /// The numeric ID of the statute, contract, or procedure affected.
    pub entity_id: u64,
    /// FNV-1a hash of the actor's identity string.
    pub actor_hash: u64,
    /// When the event occurred, in Unix nanoseconds.
    pub timestamp_ns: u64,
    /// FNV-1a hash of the event's content/payload string.
    pub content_hash: u64,
}

/// Append-only, sequenced audit log for all legal operations.
///
/// An internal `HashMap<entity_id, Vec<index>>` index makes
/// [`entries_for_entity`](AuditLog::entries_for_entity) an O(1) lookup
/// instead of an O(n) linear scan.
#[derive(Debug, Clone)]
pub struct AuditLog {
    /// All recorded entries in append order.
    pub entries: Vec<AuditEntry>,
    /// The sequence number that will be assigned to the next entry.
    pub next_sequence: u64,
    /// HashMap index: entity_id -> list of indices into `entries`.
    entity_index: HashMap<u64, Vec<usize>>,
}

impl AuditLog {
    /// Create an empty audit log.
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            next_sequence: 0,
            entity_index: HashMap::new(),
        }
    }

    /// Append an audit entry and return the assigned sequence number.
    ///
    /// # Arguments
    ///
    /// * `kind` — Category of the legal event.
    /// * `entity_id` — Numeric ID of the affected statute, contract, or procedure.
    /// * `actor` — Identity of the initiating party; stored as FNV-1a hash.
    /// * `content` — Human-readable event description; stored as FNV-1a hash.
    /// * `timestamp_ns` — Event time in Unix nanoseconds.
    pub fn append(
        &mut self,
        kind: AuditEventKind,
        entity_id: u64,
        actor: &str,
        content: &str,
        timestamp_ns: u64,
    ) -> u64 {
        let seq = self.next_sequence;
        self.next_sequence += 1;
        let idx = self.entries.len();
        self.entries.push(AuditEntry {
            sequence: seq,
            kind,
            entity_id,
            actor_hash: fnv1a(actor.as_bytes()),
            timestamp_ns,
            content_hash: fnv1a(content.as_bytes()),
        });
        // Update the O(1) entity index.
        self.entity_index
            .entry(entity_id)
            .or_insert_with(Vec::new)
            .push(idx);
        seq
    }

    /// Return all entries that relate to a specific entity id.
    ///
    /// Uses the internal HashMap index for O(1) lookup instead of an O(n)
    /// linear scan.
    pub fn entries_for_entity(&self, entity_id: u64) -> Vec<&AuditEntry> {
        match self.entity_index.get(&entity_id) {
            None => Vec::new(),
            Some(indices) => indices.iter().map(|&i| &self.entries[i]).collect(),
        }
    }

    /// Return all entries whose timestamp falls within `[from_ns, to_ns)`.
    pub fn entries_in_range(&self, from_ns: u64, to_ns: u64) -> Vec<&AuditEntry> {
        self.entries
            .iter()
            .filter(|e| e.timestamp_ns >= from_ns && e.timestamp_ns < to_ns)
            .collect()
    }

    /// Total number of entries in the log.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if the log contains no entries.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Verify that sequence numbers are contiguous starting from 0.
    ///
    /// Returns `true` for an empty log or a log whose entries are numbered
    /// `0, 1, 2, …, n-1` in order.
    pub fn verify_sequence(&self) -> bool {
        for (i, entry) in self.entries.iter().enumerate() {
            if entry.sequence != i as u64 {
                return false;
            }
        }
        true
    }
}

impl Default for AuditLog {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const NS: u64 = 1_000_000_000;

    #[test]
    fn test_append_entries_and_verify_sequence() {
        let mut log = AuditLog::new();
        let s0 = log.append(AuditEventKind::StatuteCreated, 1, "admin", "Civil Code", 0);
        let s1 = log.append(AuditEventKind::ContractCreated, 100, "alice", "sales contract", NS);
        let s2 = log.append(AuditEventKind::ProcedureStarted, 42, "bob", "permit application", 2 * NS);

        assert_eq!(s0, 0);
        assert_eq!(s1, 1);
        assert_eq!(s2, 2);
        assert_eq!(log.len(), 3);
        assert!(log.verify_sequence());
    }

    #[test]
    fn test_filter_by_entity_id() {
        let mut log = AuditLog::new();
        log.append(AuditEventKind::StatuteCreated, 1, "admin", "Civil Code", 0);
        log.append(AuditEventKind::ContractCreated, 100, "alice", "contract A", NS);
        log.append(AuditEventKind::ContractFulfilled, 100, "alice", "contract A fulfilled", 2 * NS);
        log.append(AuditEventKind::ProcedureStarted, 200, "bob", "procedure B", 3 * NS);

        let for_100 = log.entries_for_entity(100);
        assert_eq!(for_100.len(), 2);
        assert!(for_100.iter().all(|e| e.entity_id == 100));

        let for_1 = log.entries_for_entity(1);
        assert_eq!(for_1.len(), 1);

        let for_999 = log.entries_for_entity(999);
        assert!(for_999.is_empty());
    }

    #[test]
    fn test_filter_by_time_range() {
        let mut log = AuditLog::new();
        // Events at 0s, 5s, 10s, 15s, 20s
        for i in 0u64..5 {
            log.append(
                AuditEventKind::StatuteCreated,
                i,
                "admin",
                "entry",
                i * 5 * NS,
            );
        }

        // Range [5s, 15s) should capture events at 5s and 10s
        let range = log.entries_in_range(5 * NS, 15 * NS);
        assert_eq!(range.len(), 2);
        assert!(range.iter().all(|e| e.timestamp_ns >= 5 * NS && e.timestamp_ns < 15 * NS));
    }

    #[test]
    fn test_verify_contiguous_sequence() {
        let mut log = AuditLog::new();
        assert!(log.verify_sequence()); // empty log is valid

        log.append(AuditEventKind::ContractCreated, 1, "a", "c", 0);
        log.append(AuditEventKind::ContractFulfilled, 1, "a", "f", NS);
        log.append(AuditEventKind::ProcedureStarted, 2, "b", "p", 2 * NS);
        assert!(log.verify_sequence());

        // Corrupt a sequence number
        log.entries[1].sequence = 99;
        assert!(!log.verify_sequence());
    }

    #[test]
    fn test_empty_log() {
        let log = AuditLog::new();
        assert!(log.is_empty());
        assert_eq!(log.len(), 0);
        assert!(log.verify_sequence());
        assert!(log.entries_for_entity(1).is_empty());
        assert!(log.entries_in_range(0, u64::MAX).is_empty());
    }
}
