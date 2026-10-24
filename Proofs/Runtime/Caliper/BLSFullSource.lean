import Proofs.Runtime.Caliper.BLSFullOriginal

/-! Source correspondence for the constructed caller and extractors. The caller
supplies only its local machine-head correspondence and query termination bound;
the query service, private-cache handoff and extraction equality are proved here. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {M F G K A : Type}
    (layout : Layouts w M F G K A) (caller : Caller layout) {fuel : Nat}
    (invariant : Caller.Invariant layout caller fuel)

/-- Local correspondence of caller code with its oracle machine. This does not
assume that either completed reduction implements its source program. -/
structure Caller.Correspondence where
  machine : OracleMachine (Model.LazyAGM.advSpec M M G) K layout.Forgery
  stateView : layout.Request × A → machine.State
  source : K → OracleComp (Model.LazyAGM.advSpec M M G) layout.Forgery
  implements : machine.ImplementsWithin source fuel
  goodAdvance : ∀ remaining q c, invariant.domain (remaining + 1) (q, c) →
    ∀ next : (Model.LazyAGM.advSpec M M G).Range (BLSCallerHandler.query layout.good.service layout.randomBound q) → machine.State,
      machine.view (stateView (q, c)) = .inr ⟨BLSCallerHandler.query layout.good.service layout.randomBound q, next⟩ →
      ∀ represented original, BLSCallerHandler.replyMatches layout.good.service layout.randomBound q represented original →
        CallerMachine.Matches machine (BLSCallerHandler.query layout.good.service layout.randomBound) stateView
          (caller.advance (c, represented)) (next original)
  badAdvance : ∀ remaining q c, invariant.domain (remaining + 1) (q, c) →
    ∀ next : (Model.LazyAGM.advSpec M M G).Range (BLSCallerHandler.query layout.bad.service layout.randomBound q) → machine.State,
      machine.view (stateView (q, c)) = .inr ⟨BLSCallerHandler.query layout.bad.service layout.randomBound q, next⟩ →
      ∀ represented original, BLSCallerHandler.replyMatches layout.bad.service layout.randomBound q represented original →
        CallerMachine.Matches machine (BLSCallerHandler.query layout.bad.service layout.randomBound) stateView
          (caller.advance (c, represented)) (next original)
  goodInitial : ∀ value : layout.key.Value,
    CallerMachine.Matches machine (BLSCallerHandler.query layout.good.service layout.randomBound) stateView
      (caller.initial value) (machine.init value.val)
  badInitial : ∀ value : layout.key.Value,
    CallerMachine.Matches machine (BLSCallerHandler.query layout.bad.service layout.randomBound) stateView
      (caller.initial value) (machine.init value.val)

variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Field (val.Value base)] [SampleableType (val.Value base)]
    [SMul (val.Value base) G] [Add G] [SMul (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A) (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller layout) (fuel : Nat)
    (drawSource : ProbComp layout.scheme.cache.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (invariant : Caller.Invariant layout caller fuel)
    (witness : Caller.Correspondence layout caller invariant)

include drawLaw witness in
theorem good_tail_original (value : layout.key.Value × layout.good.service.store.Value)
    (valid : goodAdmitted layout fuel value) :
    Subtype.val <$> goodTailSource layout routines P comparison correct caller fuel drawSource value =
      ((simulateQ (BLSCallerHandler.original (fun signing sample => sample.1 • (if signing then sample.2.2 else sample.2.1)))
        (witness.source value.1.val)).run value.2.val >>=
        fun answer => goodOriginalExtract (answer.1.val, answer.2.2)) :=
  BLSCallerExtraction.denote_source layout.good (zero layout routines) P comparison correct
    (goodResponse layout routines) (BLSResponse.good_buffers layout.scheme.response routines.groupScale routines.scaleNames.buffers)
    (layout.scheme.goodReserve routines.reserve) caller.advance caller.initial fuel drawSource drawLaw
    invariant.domain invariant.goodAdvance (goodAdmitted layout fuel) (fun value _ => invariant.initial value.1)
    (fun _ valid => valid.1) (fun _ valid => valid.2) (zero layout routines)
    (goodExtract layout routines P comparison correct drawSource) goodOriginalExtract
    (good_extract_original layout routines P comparison correct drawSource drawLaw)
    witness.machine witness.stateView Subtype.val witness.goodAdvance (fun value _ => witness.goodInitial value.1)
    witness.source witness.implements value valid

include drawLaw witness in
theorem bad_tail_original (value : layout.key.Value × layout.bad.service.store.Value)
    (valid : badAdmitted layout fuel value) :
    Subtype.val <$> badTailSource layout routines P comparison correct caller fuel drawSource value =
      ((simulateQ (BLSCallerHandler.original (base := base) (key := key) (val := .pair val val) (fun signing (sample : (val.Value base × val.Value base) × (val.Value base × (G × G))) =>
        if signing then sample.2.1 • (sample.1.1 • sample.2.2.2 + sample.1.2 • sample.2.2.1)
        else sample.1.1 • sample.2.2.2 + sample.1.2 • sample.2.2.1))
        (witness.source value.1.val)).run value.2.val >>=
        fun answer => badOriginalExtract (answer.1.val, answer.2.2)) :=
  BLSCallerExtraction.denote_source (base := base) (key := key) (val := .pair val val)
    layout.bad (pairZero layout routines) P comparison correct
    (badResponse layout routines) (BLSResponse.bad_buffers layout.scheme.response routines.groupScale routines.groupAdd routines.scaleNames.buffers
      (by have := routines.reserve; omega) routines.groupAddNames.buffers)
    (layout.scheme.badReserve routines.reserve) caller.advance caller.initial fuel (pairSource layout drawSource) (pair_law layout drawSource drawLaw)
    invariant.domain invariant.badAdvance (badAdmitted layout fuel) (fun value _ => by
      have valid := invariant.initial value.1
      cases h : caller.initial value.1 with
      | inl result => trivial
      | inr pending => simpa only [BLSCaller.HeadValid, h] using valid)
    (fun _ valid => valid.1) (fun _ valid => valid.2) (zero layout routines)
    (badExtract layout routines P comparison correct drawSource) badOriginalExtract
    (bad_extract_original layout routines P comparison correct drawSource drawLaw)
    witness.machine witness.stateView Subtype.val witness.badAdvance (fun value _ => witness.badInitial value.1)
    witness.source witness.implements value valid
end Signatures.Runtime.CaliperBackend.BLSFull
