# Contributing to ALICE-Legal

## Build

```bash
cargo build
```

## Test

```bash
cargo test
```

## Lint

```bash
cargo clippy -- -W clippy::all
cargo fmt -- --check
cargo doc --no-deps 2>&1 | grep warning
```

## Design Constraints

- **Deterministic legal trees**: statutes compile into AST-based clause trees with O(1) lookup by clause ID.
- **Tamper-evident procedures**: administrative steps are hash-chained; any modification invalidates the chain.
- **Immutable audit trail**: append-only log with entity-indexed and time-range queries.
- **Integer timestamps**: all times are nanosecond integers (no floating point, no timezone ambiguity).
- **Zero external dependencies**: all hashing, indexing, and logic is self-contained.
