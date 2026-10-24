# Changelog

All notable changes to ALICE-Legal will be documented in this file.

## [Unreleased]

### Security
- CI: `security-audit.yml` を追加 毎回新しい解決で `cargo audit` と `cargo deny --all-features check all` を走らせ、解決と deny の graph がこの crate を含むこと (0 件は失敗) を検査する ignore する勧告は無い 週次は火曜 02:47 UTC
- `deny.toml` を追加: alice-sign の git source を許可

### Added
- CI: `Test (public siblings)` job `cargo test --all-features` を走らせ、cargo の失敗、失敗した試験、通った試験が 166 件未満のどれでも失敗 `ci/**` の branch でも走る `scripts/preflight.sh` は生成し直して同じ step を持つ

### Changed
- `src/ffi.rs` と UE5 / Unity binding の license の行を `SPDX-License-Identifier: LicenseRef-Proprietary` に変更
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
