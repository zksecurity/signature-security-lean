# Signature Security in Lean

Machine-checked security of four signature schemes — BLS, OOPS, Proximity and
Schnorr — in Lean 4 over [VCVio](https://github.com/Verified-zkEVM/VCVio): the
games, the reductions, and concrete and asymptotic bounds whose reduction
budgets are derived from executed attacker code (the
[Caliper](https://github.com/zksecurity/caliper) model). Every public theorem depends only
on `propext`, `Classical.choice` and `Quot.sound`.

## Statements

| Scheme | Attacker model | Theorem | Bound |
| --- | --- | --- | --- |
| BLS | algebraic (AGM) | [`BLS.agm_security`](Signatures/BLS/Statement.lean) | `ε(good A) + ε(bad A) + 1/p` |
| BLS | ordinary (ROM) | [`BLS.cocdh_security`](Signatures/BLS/Statement.lean) | `coronFactor qS · εcoCDH(R A)` |
| OOPS | algebraic | [`OOPS.agm_security`](Signatures/OOPS/Statement.lean) | `ε(good A) + ε(bad A) + 1/p`, target-topic degree rule |
| Proximity | algebraic | [`Proximity.agm_security`](Signatures/Proximity/Statement.lean) | `ε(good A) + ε(bad A) + 1/p` + fresh-collision probability |
| Schnorr | ordinary (ROM) | [`Schnorr.rom_security`](Signatures/Schnorr/Statement.lean) | forking bound in `ε(R A)`, full-field nonces |
| Schnorr | ordinary (ROM) | [`Schnorr.NonzeroNonce.rom_security`](Signatures/Schnorr/Statement.lean) | forking bound in `ε(R A)`, nonzero nonces |
| Schnorr | algebraic | [`Schnorr.agm_security`](Signatures/Schnorr/Statement.lean) | `ε(R A) + (qH+1)/p + qS(qS+qH)/p` |
| Synchronized PS | algebraic | [`SynchronizedPS.agm_security`](Signatures/SynchronizedPS/Statement.lean) | `εX + εY + εH + 1/p`, one honest signature per period |
| Synchronized PS | algebraic | [`SynchronizedPS.agm_security_budgeted`](Signatures/SynchronizedPS/Statement.lean) | four named reductions `+ 2/p`, Caliper-costed |

Each bound is in the success `ε` of reductions built from the attacker `A` (DLog,
`(1,1)`-DLog or co-CDH), named in the scheme's security model; `p` is the group
order. Every such reduction has its own `*_reduction_within` theorem next to the
bound, stating that it is Caliper code within the derived code, memory and time
budget, so a hardness assumption for budgeted solvers applies to it. Each
statement also has a polynomial-family corollary (`*FamilyStatement.lean`). Synchronized
Pointcheval–Sanders has two forms: `εX`, `εY`, `εH` are the DLog successes of its
[three named solvers](Signatures/SynchronizedPS/Spec/Reduction.lean) (challenge as the first key,
as the second key, or in the period hashes), uncosted and for a finite period type since they
sample a hash table; the budgeted form costs four executed solvers in Caliper by wrapping the
attacker's caller for the two weighted schemes `x•H(t)` and `y•(m•H(t))` with the other key known
([`SyncWrap*`](Proofs/Runtime/Caliper/SyncWrapParameters.lean)), holds for any period type with decidable equality
([transport](Proofs/SynchronizedPS/PeriodTransport.lean), as OOPS's topics), and has the usual
polynomial-family corollary. Its term generators and wrapper routines are executed on 64-bit words
in [`SignaturesTest/CaliperSyncWrap.lean`](SignaturesTest/CaliperSyncWrap.lean). The same wrapping
is also done in the general PolyFun backend ([`GeneralSyncWrap*`](Proofs/Runtime/GeneralSyncWrapParameters.lean)):
the attacker's realized caller is wrapped at every known key, each wrapped caller is an adversary of
the weighted pipeline, and the sampled solvers' advantages are averages of in-budget ones, giving
[`SynchronizedPS.GeneralAGM.agm_security`](Proofs/SynchronizedPS/GeneralAGM.lean) (four per-key reductions'
successes averaged over the known key, each in budget at every key, `+ 2/p`) and
the [family corollary](Signatures/SynchronizedPS/GeneralAGMFamilyStatement.lean), which picks the best
key per security parameter as a solver family of the same class.

## Games

One experiment, [`Model.EufCma.game`](Signatures/Model/EufCma.lean), defines
security for every scheme: a scheme (key generation, signing, verification over
one lazy random oracle) and an attacker model (how an attacker is run against the
signing oracle — ordinary oracle programs, or algebraic attackers that explain
every group element they output). For ordinary attackers it is VCVio's
`unforgeableExperiment`. Each `Signatures/<Scheme>/Game.lean` is that experiment
at the scheme, written out once more as a theorem so the file reads as the
paper's figure; the proof-side games that reductions start from are related to it
by equalities in `Proofs/` (e.g. [`BLS.Game.eufCma_eq_rom`](Proofs/BLS/EufCma.lean)).
[Synchronized Pointcheval–Sanders](Signatures/SynchronizedPS/Game.lean) attacks one honest key,
and the one-signature-per-period rule is the admissibility restriction. Its base is a
hash, so every element the attacker sees is bilinear in the secrets and the hash exponents, and the
AGM proof stays linear like OOPS's. Plain Pointcheval–Sanders, whose base is attacker-chosen, is
not in scope.

## Layout

Two libraries, split by what a reviewer has to read.

- `Signatures/` — **the review surface**: everything a public statement's meaning depends on.
  `Model/` (random oracle, EUF-CMA experiment, curves, algebraic group model, advantage notions,
  the attacker's query allowance) and,
  per scheme, `Game.lean`, `Statement.lean`, the `*FamilyStatement.lean` corollaries, `Spec/`
  (the scheme and its oracles), `QueryAllowance`, and the `*SecurityModel`/`*Parameters`/`*Resources`
  records that fix the execution model and derived budgets, and `Runtime/` with the
  hardness-family hypotheses of the asymptotic statements. 105 modules.
- `Proofs/` — everything else: the proofs of the statements (`Proofs/<Scheme>/`), the executed
  reductions and their resource accounting (`Proofs/Runtime/`, `Proofs/Runtime/Caliper/`), and
  supporting lemmas (`Proofs/Model/`). Nothing here needs to be read to know what is claimed.
- `SignaturesTest/` — regression tests and audit guards (module location, explicit arguments,
  axioms of every public theorem, and that statements mention only review-surface definitions).
- `docs/` — [review guide](docs/review-guide.md), [security games](docs/SECURITY-GAMES.md),
  [computational security](docs/COMPUTATIONAL-SECURITY.md), [Schnorr review path](docs/SCHNORR.md),
  [bit complexity](docs/BIT-COMPLEXITY.md).

## Build

Lean `v4.36.0` (from `lean-toolchain`, via elan).

```sh
lake exe cache get
lake build Signatures Proofs SignaturesTest
```

CI runs exactly this. Pinned upstreams:
[VCVio](https://github.com/Verified-zkEVM/VCVio) `70c422d6`, which provides the generic
algebraic-adversary interface `GroupModel.Interaction`, and
[Caliper](https://github.com/zksecurity/caliper) `1d9c510f` (the Lean 4.36 port proposed in
zksecurity/caliper#2, taken from the fork until it merges).

## Scope

The games use lazy random oracles. Attackers are arbitrary programs in the
fixed execution model, with declared query and resource allowances; the theorems
quantify over that class, and coverage of every conventional efficient attacker
is a separate machine-adequacy claim not made here. A successful build checks
the Lean statements, not their correspondence with the papers; the
[review guide](docs/review-guide.md) is for that.
