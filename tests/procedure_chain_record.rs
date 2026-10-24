//! What `verify_chain` detects, given the head digest held outside the steps.
//!
//! Each link covers the whole record of the step before it (sequence, kind, actor, timestamp,
//! content, its own link) and the procedure id; the first link covers the procedure id and
//! sequence 0. The head ([`Procedure::head`]) is the link the next step would carry, so it covers
//! the last step and the length. Editing any field of any step, removing, inserting or reordering
//! steps, truncating or extending the chain, and moving steps to another procedure must each make
//! `verify_chain(&head)` fail.

use alice_legal::prelude::*;

/// Three steps and the head recorded after the last one
fn procedure() -> (Procedure, [u8; 32]) {
    let mut p = Procedure::new(1);
    p.add_step(StepKind::Application, "applicant", "filed", 10);
    p.add_step(StepKind::Review, "reviewer", "reviewed", 20);
    p.add_step(StepKind::Approval, "approver", "approved", 30);
    let head = p.head();
    assert!(p.verify_chain(&head));
    (p, head)
}

fn fails(p: &Procedure, head: &[u8; 32]) {
    assert!(!p.verify_chain(head));
}

#[test]
fn editing_any_field_of_any_step_breaks_the_chain() {
    for i in 0..3 {
        let (mut p, head) = procedure();
        p.steps[i].actor_hash[0] ^= 0x01;
        fails(&p, &head);
        let (mut p, head) = procedure();
        p.steps[i].kind = StepKind::Rejection;
        fails(&p, &head);
        let (mut p, head) = procedure();
        p.steps[i].timestamp_ns += 1;
        fails(&p, &head);
        let (mut p, head) = procedure();
        p.steps[i].sequence += 1;
        fails(&p, &head);
        let (mut p, head) = procedure();
        p.steps[i].content_hash[0] ^= 0x01;
        fails(&p, &head);
        let (mut p, head) = procedure();
        p.steps[i].prev_hash[0] ^= 0x01;
        fails(&p, &head);
    }
}

#[test]
fn removing_the_first_step_breaks_the_chain() {
    let (mut p, head) = procedure();
    p.steps.remove(0);
    fails(&p, &head);
}

#[test]
fn removing_a_middle_step_breaks_the_chain() {
    let (mut p, head) = procedure();
    p.steps.remove(1);
    fails(&p, &head);
}

#[test]
fn truncating_the_chain_breaks_it() {
    let (mut p, head) = procedure();
    p.steps.pop();
    fails(&p, &head);
    p.steps.clear();
    fails(&p, &head);
}

#[test]
fn extending_the_chain_without_the_new_head_breaks_it() {
    let (mut p, head) = procedure();
    p.add_step(StepKind::Completion, "approver", "closed", 40);
    fails(&p, &head);
    let new_head = p.head();
    assert!(p.verify_chain(&new_head));
}

#[test]
fn swapping_two_steps_breaks_the_chain() {
    let (mut p, head) = procedure();
    p.steps.swap(0, 1);
    fails(&p, &head);
}

#[test]
fn steps_moved_to_another_procedure_do_not_verify_there() {
    let (p1, head1) = procedure();
    let mut p2 = Procedure::new(2);
    p2.steps = p1.steps.clone();
    fails(&p2, &head1);
    // and the procedure id itself is bound
    let (mut p, head) = procedure();
    p.id = ProcedureId(2);
    fails(&p, &head);
}

#[test]
fn an_empty_procedure_has_a_head_of_its_own() {
    let p1 = Procedure::new(1);
    let p2 = Procedure::new(2);
    assert!(p1.verify_chain(&p1.head()));
    assert_ne!(p1.head(), p2.head());
    assert!(!p2.verify_chain(&p1.head()));
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
    let heads: Vec<_> = kinds
        .iter()
        .map(|&k| {
            let mut p = Procedure::new(1);
            p.add_step(k, "actor", "content", 1);
            p.head()
        })
        .collect();
    for i in 0..heads.len() {
        for j in i + 1..heads.len() {
            assert_ne!(heads[i], heads[j], "{:?} and {:?}", kinds[i], kinds[j]);
        }
    }
}
