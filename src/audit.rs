//! Audit trail for all legal operations, chained entry to entry.
//!
//! Every significant event in the ALICE-Legal system (statute creation,
//! contract fulfilment, procedure completion, document analysis, etc.) should be
//! recorded via [`AuditLog::append`]. Each [`AuditEntry`] carries a link
//! (`prev_hash`): the v2 identifier of the log id and the whole record of the entry
//! before it (sequence, kind, entity, actor, timestamp, content, its own link). The
//! first entry's link is the identifier of the log id and sequence 0.
//! [`AuditLog::head`] is the link the next entry would carry.
//!
//! # What [`AuditLog::verify_chain`] guarantees
//!
//! Given a head recorded earlier and kept outside the log (stored or signed by the
//! caller), `verify_chain(&head)` fails when, since then:
//!
//! - any field of any entry was changed;
//! - an entry was removed, inserted or moved, or the log was truncated or extended;
//! - entries were spliced in from another log (another log id).
//!
//! It does **not**:
//!
//! - detect truncation or extension against the head recomputed from the log
//!   itself: a truncated log verifies against its own head, so the head must be kept
//!   outside the log;
//! - protect the head: whoever can replace the stored head can rewrite the log;
//! - keep the actor or content text: only their identifiers are stored.

use std::collections::HashMap;

use crate::law_id::{self, Digest};

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
    /// A document was analyzed (its clauses, risk and issues computed).
    DocumentAnalyzed,
    /// A document was compiled from a template.
    TemplateCompiled,
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
    /// v2 identifier ([`crate::law_id`]) of the actor's identity string.
    pub actor_hash: Digest,
    /// When the event occurred, in Unix nanoseconds.
    pub timestamp_ns: u64,
    /// v2 identifier ([`crate::law_id`]) of the event's content/payload string.
    pub content_hash: Digest,
    /// Link to the entry before it: the v2 identifier of the log id and that entry's
    /// whole record (for the first entry, of the log id and sequence 0).
    pub prev_hash: Digest,
}

impl AuditEventKind {
    /// The kind's name in the chain link (and so in every link after an entry of this kind).
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::StatuteCreated => "statute-created",
            Self::StatuteAmended => "statute-amended",
            Self::ContractCreated => "contract-created",
            Self::ContractFulfilled => "contract-fulfilled",
            Self::ContractBreached => "contract-breached",
            Self::ProcedureStarted => "procedure-started",
            Self::ProcedureCompleted => "procedure-completed",
            Self::ProcedureRejected => "procedure-rejected",
            Self::DocumentAnalyzed => "document-analyzed",
            Self::TemplateCompiled => "template-compiled",
        }
    }
}

/// The link the first entry of log `log_id` carries: the log id and sequence 0
fn first_link(log_id: u64) -> Digest {
    law_id::hasher("alice-legal/audit/first-link/v1")
        .u64(log_id)
        .u64(0)
        .finish()
}

/// The link an entry carries to the entry before it: the log id and that entry's whole
/// record, each as a typed value
fn link(log_id: u64, prev: &AuditEntry) -> Digest {
    law_id::hasher("alice-legal/audit/link/v1")
        .u64(log_id)
        .u64(prev.sequence)
        .str(prev.kind.tag())
        .u64(prev.entity_id)
        .id(&prev.actor_hash)
        .u64(prev.timestamp_ns)
        .id(&prev.content_hash)
        .id(&prev.prev_hash)
        .finish()
}

/// Append-only, sequenced audit log for all legal operations.
///
/// An internal `HashMap<entity_id, Vec<index>>` index makes
/// [`entries_for_entity`](AuditLog::entries_for_entity) an O(1) lookup
/// instead of an O(n) linear scan.
#[derive(Debug, Clone)]
pub struct AuditLog {
    /// The identifier of this log, bound into every link (entries of another log do not
    /// verify here).
    pub log_id: u64,
    /// All recorded entries in append order.
    pub entries: Vec<AuditEntry>,
    /// The sequence number that will be assigned to the next entry.
    pub next_sequence: u64,
    /// `HashMap` index: `entity_id` -> list of indices into `entries`.
    entity_index: HashMap<u64, Vec<usize>>,
}

impl AuditLog {
    /// Create an empty audit log with the identifier `log_id`.
    #[must_use]
    pub fn new(log_id: u64) -> Self {
        Self {
            log_id,
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
    /// * `actor` — Identity of the initiating party; stored as its v2 identifier.
    /// * `content` — Human-readable event description; stored as its v2 identifier.
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
        self.push_entry(seq, kind, entity_id, actor, content, timestamp_ns);
        seq
    }

    /// Append an audit entry whose content is computed from the sequence it is assigned, and
    /// return that sequence.
    ///
    /// The log assigns the sequence and passes it to `content`, which computes the entry's content
    /// (for example a record whose id names the sequence); the content is then stored as with
    /// [`AuditLog::append`]. `content` is given the sequence only, not the log. If `content`
    /// panics, the log is left as it was: no sequence is consumed and no entry is added.
    pub fn append_with(
        &mut self,
        kind: AuditEventKind,
        entity_id: u64,
        actor: &str,
        timestamp_ns: u64,
        content: impl FnOnce(u64) -> String,
    ) -> u64 {
        let seq = self.next_sequence;
        let text = content(seq);
        self.push_entry(seq, kind, entity_id, actor, &text, timestamp_ns);
        seq
    }

    fn push_entry(
        &mut self,
        seq: u64,
        kind: AuditEventKind,
        entity_id: u64,
        actor: &str,
        content: &str,
        timestamp_ns: u64,
    ) {
        self.next_sequence = seq + 1;
        let idx = self.entries.len();
        let prev_hash = self.head();
        self.entries.push(AuditEntry {
            sequence: seq,
            kind,
            entity_id,
            actor_hash: law_id::text("alice-legal/audit-entry/actor/v1", actor),
            timestamp_ns,
            content_hash: law_id::text("alice-legal/audit-entry/content/v1", content),
            prev_hash,
        });
        // Update the O(1) entity index.
        self.entity_index.entry(entity_id).or_default().push(idx);
    }

    /// Return all entries that relate to a specific entity id.
    ///
    /// Uses the internal `HashMap` index for O(1) lookup instead of an O(n)
    /// linear scan.
    #[must_use]
    pub fn entries_for_entity(&self, entity_id: u64) -> Vec<&AuditEntry> {
        self.entity_index
            .get(&entity_id)
            .map_or_else(Vec::new, |indices| {
                indices.iter().map(|&i| &self.entries[i]).collect()
            })
    }

    /// Return all entries whose timestamp falls within `[from_ns, to_ns)`.
    #[must_use]
    pub fn entries_in_range(&self, from_ns: u64, to_ns: u64) -> Vec<&AuditEntry> {
        self.entries
            .iter()
            .filter(|e| e.timestamp_ns >= from_ns && e.timestamp_ns < to_ns)
            .collect()
    }

    /// Total number of entries in the log.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if the log contains no entries.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The link the next entry would carry: the link to the last entry's whole record, or
    /// for an empty log the link of the log id and sequence 0
    #[must_use]
    pub fn head(&self) -> Digest {
        self.entries
            .last()
            .map_or_else(|| first_link(self.log_id), |last| link(self.log_id, last))
    }

    /// Verify the chain against a head kept outside the log.
    ///
    /// Returns `true` when entry `i` has sequence `i`, every entry carries the link to the
    /// one before it (the first, the link of the log id and sequence 0), and the head
    /// recomputed from the last entry equals `expected_head`. What this does and does not
    /// detect is listed in the module documentation.
    #[must_use]
    pub fn verify_chain(&self, expected_head: &Digest) -> bool {
        let mut expected = first_link(self.log_id);
        for (i, entry) in self.entries.iter().enumerate() {
            if entry.sequence != i as u64 || entry.prev_hash != expected {
                return false;
            }
            expected = link(self.log_id, entry);
        }
        expected == *expected_head
    }

    /// Verify that sequence numbers are contiguous starting from 0.
    ///
    /// Returns `true` for an empty log or a log whose entries are numbered
    /// `0, 1, 2, …, n-1` in order.
    #[must_use]
    pub fn verify_sequence(&self) -> bool {
        for (i, entry) in self.entries.iter().enumerate() {
            if entry.sequence != i as u64 {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const NS: u64 = 1_000_000_000;

    #[test]
    fn test_append_entries_and_verify_sequence() {
        let mut log = AuditLog::new(1);
        let s0 = log.append(AuditEventKind::StatuteCreated, 1, "admin", "Civil Code", 0);
        let s1 = log.append(
            AuditEventKind::ContractCreated,
            100,
            "alice",
            "sales contract",
            NS,
        );
        let s2 = log.append(
            AuditEventKind::ProcedureStarted,
            42,
            "bob",
            "permit application",
            2 * NS,
        );

        assert_eq!(s0, 0);
        assert_eq!(s1, 1);
        assert_eq!(s2, 2);
        assert_eq!(log.len(), 3);
        assert!(log.verify_sequence());
    }

    #[test]
    fn test_filter_by_entity_id() {
        let mut log = AuditLog::new(1);
        log.append(AuditEventKind::StatuteCreated, 1, "admin", "Civil Code", 0);
        log.append(
            AuditEventKind::ContractCreated,
            100,
            "alice",
            "contract A",
            NS,
        );
        log.append(
            AuditEventKind::ContractFulfilled,
            100,
            "alice",
            "contract A fulfilled",
            2 * NS,
        );
        log.append(
            AuditEventKind::ProcedureStarted,
            200,
            "bob",
            "procedure B",
            3 * NS,
        );

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
        let mut log = AuditLog::new(1);
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
        assert!(range
            .iter()
            .all(|e| e.timestamp_ns >= 5 * NS && e.timestamp_ns < 15 * NS));
    }

    #[test]
    fn test_verify_contiguous_sequence() {
        let mut log = AuditLog::new(1);
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
        let log = AuditLog::new(1);
        assert!(log.is_empty());
        assert_eq!(log.len(), 0);
        assert!(log.verify_sequence());
        assert!(log.entries_for_entity(1).is_empty());
        assert!(log.entries_in_range(0, u64::MAX).is_empty());
    }

    #[test]
    fn test_content_hash_nonzero() {
        let mut log = AuditLog::new(1);
        log.append(
            AuditEventKind::StatuteCreated,
            1,
            "admin",
            "Civil Code enacted",
            0,
        );
        assert_ne!(log.entries[0].content_hash, crate::law_id::ZERO);
    }

    #[test]
    fn test_actor_hash_nonzero() {
        let mut log = AuditLog::new(1);
        log.append(
            AuditEventKind::ContractCreated,
            10,
            "alice",
            "contract created",
            0,
        );
        assert_ne!(log.entries[0].actor_hash, crate::law_id::ZERO);
    }

    #[test]
    fn test_content_hash_deterministic() {
        let mut log1 = AuditLog::new(1);
        let mut log2 = AuditLog::new(1);
        log1.append(
            AuditEventKind::ProcedureStarted,
            5,
            "user",
            "same content",
            1000,
        );
        log2.append(
            AuditEventKind::ProcedureStarted,
            5,
            "user",
            "same content",
            1000,
        );
        assert_eq!(log1.entries[0].content_hash, log2.entries[0].content_hash);
    }

    #[test]
    fn test_different_content_yields_different_hash() {
        let mut log = AuditLog::new(1);
        log.append(AuditEventKind::StatuteCreated, 1, "admin", "content A", 0);
        log.append(AuditEventKind::StatuteCreated, 1, "admin", "content B", 0);
        assert_ne!(log.entries[0].content_hash, log.entries[1].content_hash);
    }

    #[test]
    fn test_sequence_starts_at_zero() {
        let mut log = AuditLog::new(1);
        let seq = log.append(AuditEventKind::StatuteCreated, 1, "admin", "first", 0);
        assert_eq!(seq, 0);
        assert_eq!(log.entries[0].sequence, 0);
    }

    #[test]
    fn test_next_sequence_increments_correctly() {
        let mut log = AuditLog::new(1);
        assert_eq!(log.next_sequence, 0);
        log.append(AuditEventKind::ContractCreated, 1, "a", "b", 0);
        assert_eq!(log.next_sequence, 1);
        log.append(AuditEventKind::ContractCreated, 1, "a", "b", 0);
        assert_eq!(log.next_sequence, 2);
    }

    #[test]
    fn test_entries_in_range_exclusive_upper_bound() {
        let mut log = AuditLog::new(1);
        log.append(AuditEventKind::StatuteCreated, 1, "a", "b", 10 * NS);
        log.append(AuditEventKind::StatuteCreated, 2, "a", "b", 20 * NS);
        // [10*NS, 20*NS) — only the first entry qualifies
        let range = log.entries_in_range(10 * NS, 20 * NS);
        assert_eq!(range.len(), 1);
        assert_eq!(range[0].timestamp_ns, 10 * NS);
    }

    #[test]
    fn test_entries_in_range_empty_when_no_match() {
        let mut log = AuditLog::new(1);
        log.append(AuditEventKind::StatuteCreated, 1, "a", "b", 100 * NS);
        let range = log.entries_in_range(0, NS);
        assert!(range.is_empty());
    }

    #[test]
    fn test_new_is_empty_with_its_id() {
        let log = AuditLog::new(7);
        assert!(log.is_empty());
        assert_eq!(log.next_sequence, 0);
        assert_eq!(log.log_id, 7);
    }

    #[test]
    fn test_all_event_kinds_can_be_appended() {
        let mut log = AuditLog::new(1);
        let kinds = [
            AuditEventKind::StatuteCreated,
            AuditEventKind::StatuteAmended,
            AuditEventKind::ContractCreated,
            AuditEventKind::ContractFulfilled,
            AuditEventKind::ContractBreached,
            AuditEventKind::ProcedureStarted,
            AuditEventKind::ProcedureCompleted,
            AuditEventKind::ProcedureRejected,
        ];
        for (i, kind) in kinds.iter().enumerate() {
            log.append(*kind, i as u64, "actor", "content", i as u64 * NS);
        }
        assert_eq!(log.len(), 8);
        assert!(log.verify_sequence());
    }

    #[test]
    fn test_entries_for_entity_multiple_events() {
        let mut log = AuditLog::new(1);
        let entity = 42u64;
        log.append(
            AuditEventKind::ContractCreated,
            entity,
            "alice",
            "created",
            NS,
        );
        log.append(
            AuditEventKind::ContractFulfilled,
            entity,
            "alice",
            "fulfilled",
            2 * NS,
        );
        log.append(
            AuditEventKind::ContractBreached,
            entity,
            "bob",
            "breached",
            3 * NS,
        );
        // Unrelated entity
        log.append(
            AuditEventKind::StatuteCreated,
            99,
            "admin",
            "statute",
            4 * NS,
        );

        let for_entity = log.entries_for_entity(entity);
        assert_eq!(for_entity.len(), 3);
        assert!(for_entity.iter().all(|e| e.entity_id == entity));
    }

    #[test]
    fn test_audit_event_kind_variants_are_distinct() {
        let kinds = [
            AuditEventKind::StatuteCreated,
            AuditEventKind::StatuteAmended,
            AuditEventKind::ContractCreated,
            AuditEventKind::ContractFulfilled,
            AuditEventKind::ContractBreached,
            AuditEventKind::ProcedureStarted,
            AuditEventKind::ProcedureCompleted,
            AuditEventKind::ProcedureRejected,
        ];
        for i in 0..kinds.len() {
            for j in 0..kinds.len() {
                if i == j {
                    assert_eq!(kinds[i], kinds[j]);
                } else {
                    assert_ne!(kinds[i], kinds[j]);
                }
            }
        }
    }

    #[test]
    fn test_entries_in_range_zero_width_and_inverted() {
        // from_ns == to_ns は空範囲（下限と上限が等しい）
        let mut log = AuditLog::new(1);
        log.append(AuditEventKind::StatuteCreated, 1, "admin", "event", 10 * NS);
        let empty = log.entries_in_range(10 * NS, 10 * NS);
        assert!(empty.is_empty(), "from==to は空範囲のはず");

        // from_ns > to_ns も空を返すこと（フィルタが両条件を同時に満たせない）
        let also_empty = log.entries_in_range(20 * NS, 5 * NS);
        assert!(also_empty.is_empty(), "from>to は空範囲のはず");
    }

    #[test]
    fn test_clone_produces_independent_copy() {
        // clone したログへの追記が元ログに影響しないこと
        let mut original = AuditLog::new(1);
        original.append(AuditEventKind::ContractCreated, 1, "alice", "original", NS);

        let mut cloned = original.clone();
        cloned.append(
            AuditEventKind::ContractFulfilled,
            1,
            "alice",
            "clone-only",
            2 * NS,
        );

        assert_eq!(original.len(), 1, "元ログは変化しないこと");
        assert_eq!(cloned.len(), 2, "クローンは追記されていること");
        assert!(original.verify_sequence());
        assert!(cloned.verify_sequence());
    }

    #[test]
    fn test_large_number_of_entries_sequence_integrity() {
        // 大量エントリでもシーケンスが連続していること
        let mut log = AuditLog::new(1);
        for i in 0u64..256 {
            log.append(
                AuditEventKind::StatuteAmended,
                i % 10,
                "bulk",
                "entry",
                i * NS,
            );
        }
        assert_eq!(log.len(), 256);
        assert!(log.verify_sequence());
        assert_eq!(log.next_sequence, 256);
    }
}
