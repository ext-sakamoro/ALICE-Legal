//! What `AuditLog::verify_chain` detects, given the head kept outside the log, and what it cannot.
//!
//! Each entry's link covers the log id and the whole record of the entry before it; the first link
//! covers the log id and sequence 0. The head ([`AuditLog::head`]) is the link the next entry would
//! carry. Against a head recorded earlier, editing any field of any entry, removing, swapping or
//! inserting entries, truncating or extending the log, and splicing entries from another log are
//! all refused. Against the head recomputed from the log itself, only the links are checked: a
//! truncated log then verifies, which is why the head must be kept outside the log.

use alice_legal::{AuditEventKind, AuditLog};

const KINDS: [AuditEventKind; 10] = [
    AuditEventKind::StatuteCreated,
    AuditEventKind::StatuteAmended,
    AuditEventKind::ContractCreated,
    AuditEventKind::ContractFulfilled,
    AuditEventKind::ContractBreached,
    AuditEventKind::ProcedureStarted,
    AuditEventKind::ProcedureCompleted,
    AuditEventKind::ProcedureRejected,
    AuditEventKind::DocumentAnalyzed,
    AuditEventKind::TemplateCompiled,
];

fn log(id: u64) -> (AuditLog, [u8; 32]) {
    let mut log = AuditLog::new(id);
    log.append(
        AuditEventKind::DocumentAnalyzed,
        1,
        "engine",
        "analysis of document 1",
        10,
    );
    log.append(
        AuditEventKind::TemplateCompiled,
        2,
        "engine",
        "nda compiled",
        20,
    );
    log.append(
        AuditEventKind::ContractCreated,
        3,
        "alice",
        "contract 3",
        30,
    );
    let head = log.head();
    assert!(log.verify_chain(&head));
    (log, head)
}

fn refused(log: &AuditLog, head: &[u8; 32]) {
    assert!(!log.verify_chain(head));
}

#[test]
fn editing_any_field_of_any_entry_breaks_the_chain() {
    for i in 0..3 {
        let (mut l, head) = log(1);
        l.entries[i].sequence += 1;
        refused(&l, &head);
        let (mut l, head) = log(1);
        l.entries[i].kind = AuditEventKind::ProcedureRejected;
        refused(&l, &head);
        let (mut l, head) = log(1);
        l.entries[i].entity_id += 1;
        refused(&l, &head);
        let (mut l, head) = log(1);
        l.entries[i].actor_hash[0] ^= 1;
        refused(&l, &head);
        let (mut l, head) = log(1);
        l.entries[i].timestamp_ns += 1;
        refused(&l, &head);
        let (mut l, head) = log(1);
        l.entries[i].content_hash[0] ^= 1;
        refused(&l, &head);
        let (mut l, head) = log(1);
        l.entries[i].prev_hash[0] ^= 1;
        refused(&l, &head);
    }
}

#[test]
fn removing_swapping_or_truncating_entries_breaks_the_chain() {
    let (mut l, head) = log(1);
    l.entries.remove(0);
    refused(&l, &head);
    let (mut l, head) = log(1);
    l.entries.remove(1);
    refused(&l, &head);
    let (mut l, head) = log(1);
    l.entries.swap(0, 1);
    refused(&l, &head);
    let (mut l, head) = log(1);
    l.entries.pop();
    refused(&l, &head);
}

#[test]
fn extending_the_log_needs_the_new_head() {
    let (mut l, head) = log(1);
    l.append(
        AuditEventKind::ContractFulfilled,
        3,
        "alice",
        "fulfilled",
        40,
    );
    refused(&l, &head);
    let new_head = l.head();
    assert!(l.verify_chain(&new_head));
}

#[test]
fn entries_spliced_from_another_log_are_detected() {
    let (l1, head1) = log(1);
    let (l2, _) = log(2);
    // the same records under another log id carry other links
    assert_ne!(l1.entries[1].prev_hash, l2.entries[1].prev_hash);
    let mut spliced = AuditLog::new(1);
    spliced.entries = l2.entries.clone();
    spliced.next_sequence = 3;
    refused(&spliced, &head1);
    // nor does log 2's own head make its entries verify as log 1
    refused(&spliced, &l2.head());
}

#[test]
fn a_truncated_log_verifies_against_its_own_head() {
    // the limit: without a head kept outside, truncation is not detectable
    let (mut l, head) = log(1);
    l.entries.pop();
    l.next_sequence = 2;
    assert!(!l.verify_chain(&head));
    let own = l.head();
    assert!(l.verify_chain(&own));
}

#[test]
fn an_entry_out_of_its_position_is_refused_even_with_a_matching_head() {
    let (mut l, _) = log(1);
    l.entries[2].sequence = 9;
    let head = l.head();
    refused(&l, &head);
}

#[test]
fn an_empty_log_has_a_head_of_its_own() {
    let (a, b) = (AuditLog::new(1), AuditLog::new(2));
    assert!(a.verify_chain(&a.head()));
    assert_ne!(a.head(), b.head());
    assert!(!b.verify_chain(&a.head()));
}

#[test]
fn each_kind_gives_a_different_link() {
    let heads: Vec<[u8; 32]> = KINDS
        .iter()
        .map(|&k| {
            let mut l = AuditLog::new(1);
            l.append(k, 1, "a", "c", 1);
            l.head()
        })
        .collect();
    for i in 0..heads.len() {
        for j in i + 1..heads.len() {
            assert_ne!(heads[i], heads[j], "{:?} and {:?}", KINDS[i], KINDS[j]);
        }
    }
}
