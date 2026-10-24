//! The link a step carries covers the whole record of the step before it: its sequence, kind,
//! actor, timestamp, content and its own link. Editing any one of them in a past step must make
//! `verify_chain` fail.

use alice_legal::prelude::*;

fn procedure() -> Procedure {
    let mut p = Procedure::new(1);
    p.add_step(StepKind::Application, "applicant", "filed", 10);
    p.add_step(StepKind::Review, "reviewer", "reviewed", 20);
    p.add_step(StepKind::Approval, "approver", "approved", 30);
    assert!(p.verify_chain());
    p
}

#[test]
fn editing_the_actor_of_a_past_step_breaks_the_chain() {
    let mut p = procedure();
    p.steps[0].actor_hash = p.steps[1].actor_hash;
    assert!(!p.verify_chain());
}

#[test]
fn editing_the_kind_of_a_past_step_breaks_the_chain() {
    let mut p = procedure();
    p.steps[0].kind = StepKind::Rejection;
    assert!(!p.verify_chain());
}

#[test]
fn editing_the_timestamp_of_a_past_step_breaks_the_chain() {
    let mut p = procedure();
    p.steps[0].timestamp_ns += 1;
    assert!(!p.verify_chain());
}

#[test]
fn editing_the_sequence_of_a_past_step_breaks_the_chain() {
    let mut p = procedure();
    p.steps[0].sequence += 1;
    assert!(!p.verify_chain());
}

#[test]
fn editing_the_content_or_link_of_a_past_step_breaks_the_chain() {
    let mut p = procedure();
    p.steps[0].content_hash[0] ^= 0x01;
    assert!(!p.verify_chain());
    let mut p = procedure();
    p.steps[1].prev_hash[0] ^= 0x01;
    assert!(!p.verify_chain());
}

#[test]
fn each_kind_gives_a_different_link() {
    let kinds = [
        StepKind::Application,
        StepKind::Review,
        StepKind::Approval,
        StepKind::Rejection,
        StepKind::Amendment,
        StepKind::Notification,
        StepKind::Completion,
    ];
    let links: Vec<_> = kinds
        .iter()
        .map(|&k| {
            let mut p = Procedure::new(1);
            p.add_step(k, "actor", "content", 1);
            p.add_step(StepKind::Review, "actor", "next", 2);
            p.steps[1].prev_hash
        })
        .collect();
    for i in 0..links.len() {
        for j in i + 1..links.len() {
            assert_ne!(links[i], links[j], "{:?} and {:?}", kinds[i], kinds[j]);
        }
    }
}
