//! Two different inputs must never get the same identifier.
//!
//! `A` and `B` below are two different 16-character strings with the same FNV-1a 64-bit hash
//! (`0x3ff74e522de530b1`), found by Pollard's rho on `fnv1a(hex16(x))` in about 4.2e9 steps. The
//! first test checks that collision itself, so the pair does not rest on trust. Every other test
//! builds the same record from `A` and from `B` and requires the two to be told apart: a record
//! whose identifier is a 64-bit FNV-1a hash cannot, because the collision is constructible.

use alice_legal::oracle::{OracleRegistry, OracleResponse, OracleType, OracleVerdict};
use alice_legal::prelude::*;

const A: &str = "c5bde799c2362419";
const B: &str = "a1a9a9bf38687075";

/// FNV-1a 64-bit, written out here so the collision is checked independently of the crate
fn fnv1a64(data: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in data {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

#[test]
fn the_two_inputs_differ_and_collide_under_fnv1a_64() {
    assert_ne!(A, B);
    assert_eq!(fnv1a64(A.as_bytes()), 0x3ff7_4e52_2de5_30b1);
    assert_eq!(fnv1a64(A.as_bytes()), fnv1a64(B.as_bytes()));
}

#[test]
fn an_oracle_response_for_one_payload_does_not_verify_another() {
    let response = OracleResponse {
        oracle_id: 1,
        verdict: OracleVerdict::Satisfied,
        timestamp_ns: 1,
        data_hash: alice_legal::oracle::compute_data_hash(A.as_bytes()),
        contract_id: ContractId(1),
        condition_index: 0,
    };
    assert!(OracleRegistry::verify_response(&response, A.as_bytes()));
    assert!(!OracleRegistry::verify_response(&response, B.as_bytes()), "payload B verified a response made over payload A");
}

#[test]
fn two_oracles_with_different_names_get_different_ids() {
    let mut reg = OracleRegistry::new();
    let a = reg.register(OracleType::PriceFeed, A, 50);
    let b = reg.register(OracleType::PriceFeed, B, 50);
    assert_ne!(a, b, "two names share one oracle id");
}

#[test]
fn audit_entries_with_different_content_get_different_hashes() {
    let mut log = AuditLog::new();
    log.append(AuditEventKind::StatuteCreated, 1, "actor", A, 1);
    log.append(AuditEventKind::StatuteCreated, 1, "actor", B, 2);
    assert_ne!(log.entries[0].content_hash, log.entries[1].content_hash);
    log.append(AuditEventKind::StatuteCreated, 1, A, "content", 3);
    log.append(AuditEventKind::StatuteCreated, 1, B, "content", 4);
    assert_ne!(log.entries[2].actor_hash, log.entries[3].actor_hash);
}

#[test]
fn statute_clauses_and_titles_with_different_text_get_different_hashes() {
    let mut tree = StatuteTree::new(1, A);
    let other = StatuteTree::new(1, B);
    assert_ne!(tree.title_hash, other.title_hash);
    tree.add_clause(ClauseKind::Obligation, A, None, 0);
    tree.add_clause(ClauseKind::Obligation, B, None, 0);
    assert_ne!(tree.clauses[0].content_hash, tree.clauses[1].content_hash);
}

#[test]
fn procedure_steps_with_different_content_get_different_hashes() {
    let mut a = Procedure::new(1);
    let mut b = Procedure::new(1);
    a.add_step(StepKind::Application, "actor", A, 1);
    b.add_step(StepKind::Application, "actor", B, 1);
    assert_ne!(a.steps[0].content_hash, b.steps[0].content_hash);
    // the chain: the next step's link covers the previous content, so the two chains differ too
    a.add_step(StepKind::Review, "actor", "same", 2);
    b.add_step(StepKind::Review, "actor", "same", 2);
    assert_ne!(a.steps[1].prev_hash, b.steps[1].prev_hash);
}

#[test]
fn contract_conditions_with_different_text_get_different_hashes() {
    let mut c = Contract::new(1, &[1, 2], 0);
    c.add_condition(A, "evaluator");
    c.add_condition(B, "evaluator");
    assert_ne!(c.conditions[0].description_hash, c.conditions[1].description_hash);
    c.add_condition("same", A);
    c.add_condition("same", B);
    assert_ne!(c.conditions[2].evaluator_hash, c.conditions[3].evaluator_hash);
}
