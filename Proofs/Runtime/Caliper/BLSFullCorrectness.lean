import Proofs.Runtime.Caliper.BLSFullSetup

/-! Refinement of both complete BLS AGM programs. Extraction contracts are
proved from the constructed extractors, response contracts from named group
routines, and initial cache/log readiness from executed setup. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {G K A : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] [SMul (val.Value base) G] [Add G] [SMul (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A) (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller layout) (draw : Interactive.Code w) (fuel : Nat)
    (drawSource : ProbComp layout.scheme.cache.value.Value)
    (drawCorrect : Interactive.Refines layout.port .unit layout.scheme.cache.lookup.unit.representation
      layout.scheme.cache.value.representation (fun _ => drawSource) draw)

include drawCorrect in
theorem good_extract_refines : Interactive.RefinesOn (BLSExtractorFrame.ready layout.tokens.good) layout.port .unit
    (BLSExtractorFrame.input layout.tokens.good).representation (BLSCallerFinish.result layout.tokens.good).representation
    (goodExtract layout routines P comparison correct drawSource) (goodExtractor layout routines P comparison correct draw) :=
  BLSExtractor.good_refines layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.divNames.buffers layout.port drawCorrect
include drawCorrect in
theorem bad_extract_refines : Interactive.RefinesOn (BLSExtractorFrame.ready layout.tokens.bad) layout.port .unit
    (BLSExtractorFrame.input layout.tokens.bad).representation (BLSCallerFinish.result layout.tokens.bad).representation
    (badExtract layout routines P comparison correct drawSource) (badExtractor layout routines P comparison correct draw) := by
  have refined := BLSExtractor.bad_refines layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarNeg routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.negNames.buffers routines.divNames.buffers layout.port drawCorrect
  exact fun tape value ready before holds => refined tape value (BLSExtractorFrame.signatureReady_of_ready layout.tokens.bad value ready) before holds
omit [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] [SMul (val.Value base) G] [Add G] [SMul (val.Value base) K] in
include drawCorrect in
theorem pair_refines : Interactive.Refines layout.port .unit layout.bad.service.cache.lookup.unit.representation
    layout.bad.service.cache.value.representation (fun _ => pairSource layout drawSource) (pairDraw layout draw) :=
  PairSampling.refines (hw := layout.scheme.cache.wordFits) (fits := layout.scheme.cache.pairValueFits) drawCorrect drawCorrect

variable [SampleableType (val.Value base)]
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (invariant : Caller.Invariant layout caller fuel)

omit [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] [SMul (val.Value base) G] [Add G] [SMul (val.Value base) K] in
include drawLaw in
theorem pair_law : Subtype.val <$> pairSource layout drawSource = ($ᵗ (val.Value base × val.Value base) : ProbComp (val.Value base × val.Value base)) :=
  PairSampling.uniform layout.scheme.cache.value layout.scheme.cache.value layout.scheme.cache.pairValueFits drawSource drawSource drawLaw drawLaw

include drawCorrect drawLaw invariant in
theorem good_tail_refines : Interactive.RefinesOn (goodAdmitted layout fuel) layout.port .unit layout.goodInput layout.scheme.cache.value.representation
    (goodTailSource layout routines P comparison correct caller fuel drawSource) (goodTail layout routines P comparison correct caller draw fuel) :=
  BLSCallerExtraction.refines layout.good (zero layout routines) P comparison correct
    (goodResponse layout routines) (BLSResponse.good_buffers layout.scheme.response routines.groupScale routines.scaleNames.buffers)
    (layout.scheme.goodReserve routines.reserve) draw caller.advance caller.continuation caller.localNameFits
    layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.goodFits fuel drawSource drawCorrect drawLaw
    invariant.domain invariant.goodAdvance (goodAdmitted layout fuel) (fun value _ => invariant.initial value.1)
    (fun _ valid => valid.1) (fun _ valid => valid.2) (zero layout routines)
    (good_extract_refines layout routines P comparison correct draw drawSource drawCorrect)
include drawCorrect drawLaw invariant in
theorem bad_tail_refines : Interactive.RefinesOn (badAdmitted layout fuel) layout.port .unit layout.badInput layout.scheme.cache.value.representation
    (badTailSource layout routines P comparison correct caller fuel drawSource) (badTail layout routines P comparison correct caller draw fuel) :=
  BLSCallerExtraction.refines (base := base) (key := key) (val := .pair val val) layout.bad (pairZero layout routines) P comparison correct
    (badResponse layout routines) (BLSResponse.bad_buffers layout.scheme.response routines.groupScale routines.groupAdd routines.scaleNames.buffers
      (by have := routines.reserve; omega) routines.groupAddNames.buffers)
    (layout.scheme.badReserve routines.reserve) (pairDraw layout draw) caller.advance caller.continuation caller.localNameFits
    layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.badFits fuel (pairSource layout drawSource)
    (pair_refines layout draw drawSource drawCorrect) (pair_law layout drawSource drawLaw)
    invariant.domain invariant.badAdvance (badAdmitted layout fuel) (fun value _ => by
      have valid := invariant.initial value.1
      cases h : caller.initial value.1 with
      | inl result => trivial
      | inr pending => simpa only [BLSCaller.HeadValid, h] using valid)
    (fun _ valid => valid.1) (fun _ valid => valid.2) (zero layout routines)
    (bad_extract_refines layout routines P comparison correct draw drawSource drawCorrect)

variable (logRoom : fuel ≤ layout.tokens.capacity)
    (cacheRoom : 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1)
include drawCorrect drawLaw invariant logRoom cacheRoom in
theorem good_refines : Interactive.Refines layout.port .unit layout.setup.challenge.representation layout.scheme.cache.value.representation
    (goodSource layout routines P comparison correct caller fuel drawSource) (goodCode layout routines P comparison correct caller draw fuel) := by
  have composed := ((good_setup_refines layout).on (fun _ => True)).seq
    (good_tail_refines layout routines P comparison correct caller draw fuel drawSource drawCorrect drawLaw invariant) (by
      intro value _ answer reached
      have equal : answer = goodStart layout value := by simpa only [support_pure, Set.mem_singleton_iff] using reached
      subst answer
      exact good_start_admitted layout fuel logRoom cacheRoom value)
  intro tape value before holds
  convert composed tape value trivial before holds using 1 <;> rfl
include drawCorrect drawLaw invariant logRoom cacheRoom in
theorem bad_refines : Interactive.Refines layout.port .unit layout.setup.challenge.representation layout.scheme.cache.value.representation
    (badSource layout routines P comparison correct caller fuel drawSource) (badCode layout routines P comparison correct caller draw fuel) := by
  have composed := ((bad_setup_refines layout routines draw drawSource drawCorrect).on (fun _ => True)).seq
    (bad_tail_refines layout routines P comparison correct caller draw fuel drawSource drawCorrect drawLaw invariant)
    (fun value _ answer reached => bad_start_admitted layout routines drawSource fuel logRoom cacheRoom value answer reached)
  exact fun tape value before holds => composed tape value trivial before holds
end Signatures.Runtime.CaliperBackend.BLSFull
