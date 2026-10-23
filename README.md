# Signature Security in Lean

Machine-checked security of four signature schemes — BLS, OOPS, Proximity and
Schnorr — in Lean 4 over [VCVio](https://github.com/Verified-zkEVM/VCVio): the
games, the reductions, and concrete and asymptotic bounds whose reduction
budgets are derived from executed attacker code (the vendored
[Caliper](vendor/caliper/UPSTREAM.md) model). Every public theorem depends only
on `propext`, `Classical.choice` and `Quot.sound`.

## Statements

| Scheme | Attacker model | Theorem | Bound |
| --- | --- | --- | --- |
| BLS | algebraic (AGM) | [`BLS.agm_security`](Signatures/BLS/Statement.lean) | `2·εDL + 1/p` |
| BLS | ordinary (ROM) | [`BLS.cocdh_security`](Signatures/BLS/Statement.lean) | `coronFactor qS · εcoCDH` |
| OOPS | algebraic | [`OOPS.agm_security`](Signatures/OOPS/Statement.lean) | `2·εDL + 1/p`, target-topic degree rule |
| Proximity | algebraic | [`Proximity.agm_security`](Signatures/Proximity/Statement.lean) | `2·εDL + 1/p` + fresh-collision probability |
| Schnorr | ordinary (ROM) | [`Schnorr.rom_security`](Signatures/Schnorr/Statement.lean) | forking bound, full-field nonces |
| Schnorr | ordinary (ROM) | [`Schnorr.NonzeroNonce.rom_security`](Signatures/Schnorr/Statement.lean) | forking bound, nonzero nonces |
| Schnorr | algebraic | [`Schnorr.agm_security`](Signatures/Schnorr/Statement.lean) | `εDL + (qH+1)/p + qS(qS+qH)/p` |

`εDL`/`εcoCDH` are DLog/co-CDH success suprema at the proved reduction budget in
the same execution model; `p` is the group order. Each statement has a
polynomial-family corollary (`*FamilyStatement.lean`) and the two-budget form
of each AGM bound is its scheme's `Proofs.agm_security`.

## Games

One experiment, [`Model.EufCma.game`](Signatures/Model/EufCma.lean), defines
security for every scheme: a scheme (key generation, signing, verification over
one lazy random oracle) and an attacker model (how an attacker is run against the
signing oracle — ordinary oracle programs, or algebraic attackers that explain
every group element they output). For ordinary attackers it is VCVio's
`unforgeableExperiment`. Each `Signatures/<Scheme>/Game.lean` is that experiment
at the scheme, written out once more as a theorem so the file reads as the
paper's figure; the proof-side games that reductions start from are related to it
by equalities in `Proofs/` (e.g. [`BLS.Game.eufCma_eq_rom`](Signatures/BLS/Proofs/EufCma.lean)).

## Layout

- `Signatures/Model/` — shared notions: random oracle, EUF-CMA experiment, algebraic group model, hardness.
- `Signatures/{BLS,OOPS,Proximity,Schnorr}/` — `Game.lean`, `Statement.lean`, `Spec/`, `Proofs/`, model records.
- `Signatures/Runtime/` — executed reductions and their resource accounting (`Runtime/Caliper/` for the Caliper word machine).
- `SignaturesTest/` — regression tests and audit guards (module location, explicit arguments, axioms of every public theorem).
- `docs/` — [review guide](docs/review-guide.md), [security games](docs/SECURITY-GAMES.md), [computational-security status](docs/COMPUTATIONAL-SECURITY.md), [Schnorr review path](docs/SCHNORR.md), [Caliper backend](docs/CALIPER-BACKEND-PLAN.md), [API migration](docs/API-MIGRATION.md), and the retired long-form [development notes](docs/DEVELOPMENT-NOTES.md).

## Build

Lean `v4.34.0` (from `lean-toolchain`, via elan).

```sh
lake exe cache get
lake build Signatures SignaturesTest
```

CI runs exactly this. Pinned upstreams:
[ArkLib](https://github.com/Verified-zkEVM/ArkLib) `7653a901`,
[VCVio](https://github.com/Verified-zkEVM/VCVio) `f5119c64`,
[agm-lean](https://github.com/zksecurity/agm-lean) `c207f29d`,
[Caliper](https://github.com/zksecurity/caliper) `b62f7c8b` (vendored with a minimal Lean 4.34 port).

## Scope

The games use lazy random oracles. Attackers are arbitrary programs in the
fixed execution model, with declared query and resource allowances; the theorems
quantify over that class, and coverage of every conventional efficient attacker
is a separate machine-adequacy claim not made here. A successful build checks
the Lean statements, not their correspondence with the papers; the
[review guide](docs/review-guide.md) is for that.
