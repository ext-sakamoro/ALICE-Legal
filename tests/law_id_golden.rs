//! The record identifiers are LawIdHasher v2 identifiers: each value below was computed with
//! ALICE-Zip's independent reference (`scripts/law_id_v2_reference.py`, standard-library Python)
//! from the kind, `sha256(b"alice-legal/semantics/text-and-integers/v1")` and the typed values, and
//! the records built through this crate's API must give exactly those bytes.

use alice_legal::law_id::{Digest, LEGAL_SEMANTICS_ID};
use alice_legal::oracle::{compute_data_hash, OracleRegistry, OracleType};
use alice_legal::penalty::{PenaltyEngine, PenaltyKind, PenaltyRule};
use alice_legal::prelude::*;

fn hex(d: &Digest) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn the_semantics_identifier() {
    assert_eq!(
        hex(&LEGAL_SEMANTICS_ID),
        "d48ce42c2ea15aab42bca80e47753099fd47fe904009a9f38c42e2e282c8f0e2"
    );
}

#[test]
fn an_audit_actor() {
    let mut log = AuditLog::new();
    log.append(AuditEventKind::StatuteCreated, 1, "alice", "content", 1);
    assert_eq!(
        hex(&log.entries[0].actor_hash),
        "6f6cbb813b09dd662396ff6eb46fd16fdb641f2a7612f95b8a65a3ee28305829"
    );
}

#[test]
fn oracle_names_and_data() {
    let mut reg = OracleRegistry::new();
    let a = reg.register(OracleType::PriceFeed, "c5bde799c2362419", 50);
    let b = reg.register(OracleType::PriceFeed, "a1a9a9bf38687075", 50);
    assert_eq!(
        hex(&a),
        "cae758c7cdd903047bc0a33019e2fb59d33d245c47785b7cca2acee3ede490fc"
    );
    assert_eq!(
        hex(&b),
        "182eee977ffd77f164aecfaceea95d4d4a8bed586f45344767af884c691e7a9a"
    );
    assert_eq!(
        hex(&compute_data_hash(b"test")),
        "548c914ce6ec3620e8cdb8e0279a8f5718739811f0feccfc4af899290b85e066"
    );
}

#[test]
fn a_contract_content() {
    let c = Contract::new(1, &[1, 2], 7);
    assert_eq!(
        hex(&c.content_hash),
        "1d704b8161c7c3dae32132d83d99cfe66f98cee4ec1a0fb8305065eb45f4d306"
    );
}

#[test]
fn a_penalty_record() {
    let mut e = PenaltyEngine::new();
    e.add_rule(PenaltyRule {
        id: 1,
        contract_id: ContractId(1),
        obligation_index: 0,
        kind: PenaltyKind::FixedAmount,
        amount_ticks: 10,
        grace_period_ns: 0,
        max_applications: 0,
    });
    let idx = e
        .execute_penalty(1, PartyId(2), 3)
        .expect("the rule applies");
    assert_eq!(
        hex(&e.get_record(idx).unwrap().record_hash),
        "cab6d6797eaf37d858ca184a35773bc97d7a2b83f4f03894a0ba0c62dc8af1fa"
    );
}

#[test]
fn a_procedure_chain_link() {
    let mut p = Procedure::new(1);
    p.add_step(StepKind::Application, "actor", "x", 1);
    p.add_step(StepKind::Review, "actor", "y", 2);
    // the first link: procedure id 1, sequence 0
    assert_eq!(
        hex(&p.steps[0].prev_hash),
        "cf8ca22e8f998359a99c2bc49af59502a30d32a0b62e860a201f4e350dbaebc3"
    );
    assert_eq!(
        hex(&p.steps[1].prev_hash),
        "385b1d8a1fa2286e0b0ecdbb3f21bf6d7570c39064a5451a26eb3d8db4d23ae0"
    );
    let head = p.head();
    assert_eq!(
        hex(&head),
        "d88be8dcd475bb83e48a9a5a1dc547d8b68b8b8ff308db8e1d1542ade8c00ae4"
    );
    assert!(p.verify_chain(&head));
}
