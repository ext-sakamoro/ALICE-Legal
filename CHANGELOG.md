# Changelog

All notable changes to ALICE-Legal will be documented in this file.

## [Unreleased]

### Changed
- `signed_contract` の Ed25519 / SHA-256 / `MerkleTree` と時刻印 (`TimeStamp` / `TimeStampToken`) を `alice-sign` (MIT OR Apache-2.0、公開、git rev 6b79a0ba、feature `timestamp`) から取るようにした 型と byte 列は同じ (これまでの依存先も同じ実装) 公開の source だけで build できる

## [0.1.0] - 2026-02-23

### Added
- `statute` — `StatuteTree`, `Clause`, `ClauseKind` (Obligation/Prohibition/Right/Penalty/Definition/Procedural), hierarchical clause indexing
- `contract` — `Contract`, `Obligation`, `ContractStatus`, deterministic obligation fulfilment tracking
- `procedure` — `Procedure`, `ProcedureStep`, `StepKind`, tamper-evident hash-chained event stream
- `audit` — `AuditLog`, `AuditEntry`, `AuditEventKind`, entity and time-range indexed immutable log
- `hash_utils` — FNV-1a shared hashing utility
- Zero external dependencies
- 91 unit tests + 1 doc-test

### Fixed
- `or_insert_with(Vec::new)` → `or_default()` in audit.rs and statute.rs (clippy)
