# ALICE-Legal

Deterministic legal tree compilation, contract execution, and administrative procedure events for machine-verifiable legal operations.

## Features

- **Statute AST compilation** — natural language laws compiled into a deterministic clause tree with six clause kinds (Obligation, Prohibition, Permission, Definition, Penalty, Exception)
- **Tamper-evident procedure log** — each step in an administrative procedure chains to the previous via its v2 identifier (LawIdHasher v2, 32 bytes), enabling offline integrity verification with `verify_chain()`
- **Smart contract execution** — lifecycle management (Draft → Active → Fulfilled / Breached / Terminated / Expired) with `i128` fixed-point arithmetic for all monetary amounts
- **Append-only audit log** — every significant legal event is recorded with actor hash, content hash, and Unix nanosecond timestamp
- **O(1) lookups via HashMap indices** — `StatuteTree::find_clause`, `StatuteTree::children_of`, and `AuditLog::entries_for_entity` use internal `HashMap` indices instead of linear scans
- **LawIdHasher v2 identifiers throughout** — every content and identity field is the 32-byte v2 identifier (ALICE-Zip `law_id`) of a kind, `LEGAL_SEMANTICS_ID` and the typed values, defined once in `law_id`
- **Zero external dependencies** — `[dependencies]` is empty; the crate compiles on stable Rust with no network access
- **91 unit tests** across all five modules

## Module Overview

| Module | Primary Types | Responsibility |
|---|---|---|
| `law_id` | `Digest`, `LEGAL_SEMANTICS_ID`, `text`, `data`, `hasher` | Record identifiers (LawIdHasher v2, 32 bytes) used by every other module |
| `statute` | `StatuteTree`, `Clause`, `ClauseKind`, `StatuteId` | Build and query deterministic legal ASTs; O(1) clause and children lookups |
| `contract` | `Contract`, `Obligation`, `Condition`, `ContractStatus`, `ContractId`, `PartyId` | Create contracts, add obligations and conditions, drive lifecycle, sum fixed-point amounts |
| `procedure` | `Procedure`, `ProcedureStep`, `StepKind`, `ProcedureStatus`, `ProcedureId` | Append-only administrative event stream with hash-chain integrity |
| `audit` | `AuditLog`, `AuditEntry`, `AuditEventKind` | Sequenced, append-only compliance log with O(1) entity filtering and time-range queries |

## Quick Start

Add the crate to your `Cargo.toml`:

```toml
[dependencies]
alice-legal = { path = "../ALICE-Legal" }
```

### Statute tree

```rust
use alice_legal::statute::{StatuteTree, ClauseKind};

let mut statute = StatuteTree::new(1, "Civil Code Article 1");

// Add a parent clause and two child clauses
let parent = statute.add_clause(ClauseKind::Definition, "Chapter 1", None, 0);
let child = statute.add_clause(
    ClauseKind::Obligation,
    "Parties must act in good faith",
    Some(parent),
    0,
);

// O(1) lookups backed by internal HashMap indices
let clause = statute.find_clause(child).unwrap();
let children = statute.children_of(parent);

// Temporal effectivity check
let effective = statute.is_effective(child, 1_000_000_000u64); // at 1 s
```

### Contract execution

```rust
use alice_legal::contract::{Contract, ContractStatus};

let mut contract = Contract::new(100, &[1, 2], 1_000_000);

// Amounts in i128 fixed-point ticks — no floating-point
let ob_idx = contract.add_obligation(1, 2, 5_000_0000_i128, 2_000_000_000);
let cond_idx = contract.add_condition("Regulatory approval", "oracle-regulator");

contract.meet_condition(cond_idx);
contract.fulfill_obligation(ob_idx);

contract.check_status(1_500_000_000); // now_ns
assert_eq!(contract.status, ContractStatus::Fulfilled);

println!("Total ticks: {}", contract.total_obligation());
```

### Administrative procedure

```rust
use alice_legal::procedure::{Procedure, StepKind};

let mut proc = Procedure::new(42);

proc.add_step(StepKind::Application, "citizen-001", "permit application", 1_000_000_000);
proc.add_step(StepKind::Review,      "officer-042", "documents reviewed",  2_000_000_000);
proc.add_step(StepKind::Approval,    "authority",   "permit granted",       3_000_000_000);

let head = proc.head();          // keep outside the steps (store or sign it)
assert!(proc.verify_chain(&head)); // tamper detection
```

### Audit log

```rust
use alice_legal::audit::{AuditLog, AuditEventKind};

let mut log = AuditLog::new();

log.append(AuditEventKind::StatuteCreated,  1,   "admin", "Civil Code Article 1", 0);
log.append(AuditEventKind::ContractCreated, 100, "alice", "sales contract",        1_000_000_000);

// O(1) entity lookup
let entries = log.entries_for_entity(100);

// Half-open time range [from_ns, to_ns)
let recent = log.entries_in_range(0, 2_000_000_000);

assert!(log.verify_sequence());
```

## Performance

| Optimization | Detail |
|---|---|
| O(1) clause lookup | `StatuteTree` maintains a `HashMap<clause_id, Vec_index>` updated on every `add_clause` call |
| O(1) children lookup | `StatuteTree` maintains a `HashMap<parent_id, Vec<Vec_index>>` updated on every `add_clause` call |
| O(1) audit entity filter | `AuditLog` maintains a `HashMap<entity_id, Vec<index>>` updated on every `append` call |
| i128 fixed-point | All monetary amounts use `i128` ticks; no `f32`/`f64` anywhere in the execution path |

## Release Profile

```toml
[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
panic = "abort"
strip = true
```

## Running Tests

```sh
cargo test
```

91 tests cover all five modules, including determinism, boundary conditions, tamper detection, and lifecycle state transitions.

## License

`LicenseRef-Proprietary`. The text is [LICENSE-Proprietary](LICENSE-Proprietary).

Enquiries: https://extoria.co.jp/
