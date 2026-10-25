//! `AuditLog::append_with`: the log assigns the sequence and hands it to the closure that computes
//! the entry's content, so content that names its own sequence (a record id "<log>-<seq>") is
//! computed from the append itself. A closure that panics leaves the log as it was.

use alice_legal::law_id;
use alice_legal::{AuditEventKind, AuditLog};

const K: AuditEventKind = AuditEventKind::TemplateCompiled;

#[test]
fn the_closure_receives_the_sequence_the_entry_takes() {
    let mut log = AuditLog::new(3);
    log.append(AuditEventKind::DocumentAnalyzed, 0, "engine", "first", 1);
    for want in 1u64..5 {
        let mut seen = None;
        let seq = log.append_with(K, 9, "engine", 10 + want, |s| {
            seen = Some(s);
            format!("3-{s}")
        });
        assert_eq!(seen, Some(want));
        assert_eq!(seq, want);
        let e = log.entries.last().expect("an entry");
        assert_eq!(e.sequence, want);
        assert_eq!(
            e.content_hash,
            law_id::text("alice-legal/audit-entry/content/v1", &format!("3-{want}"))
        );
        assert_eq!(e.timestamp_ns, 10 + want);
        assert_eq!(e.entity_id, 9);
    }
    assert_eq!(log.next_sequence, 5);
    assert!(log.verify_chain(&log.head()));
}

/// `append` and `append_with` with the same content give the same entries and head
#[test]
fn append_is_append_with_a_fixed_content() {
    let mut a = AuditLog::new(1);
    let mut b = AuditLog::new(1);
    for i in 0..4u64 {
        let content = format!("event {i}");
        a.append(K, i, "alice", &content, i);
        b.append_with(K, i, "alice", i, |_| content.clone());
    }
    assert_eq!(a.head(), b.head());
    for (x, y) in a.entries.iter().zip(&b.entries) {
        assert_eq!(
            (x.sequence, x.content_hash, x.prev_hash, x.actor_hash),
            (y.sequence, y.content_hash, y.prev_hash, y.actor_hash)
        );
    }
    assert_eq!(b.entries_for_entity(2).len(), 1);
}

/// a closure that panics consumes no sequence and adds no entry; the next append takes the
/// sequence it would have taken and the chain verifies
#[cfg(panic = "unwind")]
#[test]
fn a_panicking_closure_leaves_the_log_unchanged() {
    use std::panic::{catch_unwind, AssertUnwindSafe};
    let mut log = AuditLog::new(5);
    log.append(K, 1, "engine", "one", 1);
    let head = log.head();
    let r = catch_unwind(AssertUnwindSafe(|| {
        log.append_with(K, 2, "engine", 2, |_| panic!("content failed"))
    }));
    assert!(r.is_err());
    assert_eq!(log.entries.len(), 1);
    assert_eq!(log.next_sequence, 1);
    assert_eq!(log.head(), head);
    assert!(log.entries_for_entity(2).is_empty());
    assert!(log.verify_chain(&head));
    let seq = log.append_with(K, 2, "engine", 3, |s| format!("5-{s}"));
    assert_eq!(seq, 1);
    assert!(log.verify_chain(&log.head()));
    assert_eq!(log.entries_for_entity(2).len(), 1);
}
