# Changelog

All notable changes to ALICE-Legal will be documented in this file.

## [Unreleased]

### 破壊的変更
- 記録の識別子を FNV-1a 64 bit から LawIdHasher v2 (ALICE-Zip `law_id`、32 byte) に変更 audit / procedure の actor・content・prev、dispute の reason、oracle の id・name・data、penalty の record、contract の content・condition の description と evaluator、statute の title と clause の content が `[u8; 32]` (`law_id::Digest`) になる `OracleRegistry::register` は `Digest` を返し、`find_oracle` / `deactivate` と `OracleResponse::oracle_id` も `Digest` を取る
- `hash_utils` (`fnv1a`) を削除し、`law_id` (`Digest` / `ZERO` / `LEGAL_SEMANTICS_ID` / `hasher` / `text` / `data`) を追加
- 手続きの連鎖の link は手続きの id と前の段の記録全体 (sequence・kind・actor・timestamp・content・link) の v2 識別子、最初の段の link は手続きの id と sequence 0 の v2 識別子
- `Procedure::verify_chain(&self)` を `verify_chain(&self, expected_head: &Digest)` に変更し、`Procedure::head` (次の段が持つ link) を追加 段の外に持った head と照合し、段の位置 (sequence が index と一致) も確かめる 検出するもの・しないものは `procedure` の module doc に記載
- FFI: `alice_procedure_verify_chain(proc, head)` (32 byte の head を取る) に変更し、`alice_procedure_head(proc, out)` を追加 UE5 / Unity binding も同じ

### Added
- 試験 `tests/identifier_collision.rs` (FNV-1a 64 bit で衝突する 2 つの文字列で、各記録の識別子が別になることと oracle の応答の照合を確かめる) 、`tests/law_id_golden.rs` (ALICE-Zip の独立実装で計算した識別子) と `tests/procedure_chain_record.rs` (各段の各 field の書き換え、段の削除・入れ替え・切り詰め・延長、別の手続きへの移動で連鎖の照合が失敗する)
- 依存 `alice-zip` (git)、`deny.toml` の allow-git に ALICE-DetMath と ALICE-Zip

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
