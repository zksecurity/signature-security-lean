import Proofs.Runtime.Caliper.BLSFullBudget

/-! Derived runtime and stored-code bounds of both complete BLS AGM programs. -/
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
    (bound : Routines.Bounds layout routines) (localBound : Caller.Bounds layout caller)
    {drawTime drawWords : Nat}
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.scheme.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)

include drawCorrect drawTimeBound in
theorem good_extract_time : Interactive.TimeBoundOn (BLSExtractorFrame.ready layout.tokens.good) layout.port .unit
    (BLSExtractorFrame.input layout.tokens.good).representation (goodExtractor layout routines P comparison correct draw)
    (goodExtractionTime layout routines bound drawTime) :=
  BLSExtractor.good_time layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.divNames.buffers layout.port
    drawCorrect drawTimeBound bound.mulBound bound.addBound bound.subBound bound.divBound
include drawCorrect drawTimeBound in
theorem bad_extract_time : Interactive.TimeBoundOn (BLSExtractorFrame.ready layout.tokens.bad) layout.port .unit
    (BLSExtractorFrame.input layout.tokens.bad).representation (badExtractor layout routines P comparison correct draw)
    (badExtractionTime layout routines bound drawTime) := by
  have bounded := BLSExtractor.bad_time layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarNeg routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.negNames.buffers routines.divNames.buffers layout.port
    drawCorrect drawTimeBound bound.mulBound bound.addBound bound.subBound bound.negBound bound.divBound
  exact fun tape value ready before holds finished reached => bounded tape value
    (BLSExtractorFrame.signatureReady_of_ready layout.tokens.bad value ready) before holds finished reached
include drawWordsBound in
theorem good_extract_words : ((goodExtractor layout routines P comparison correct draw).lower layout.port).descriptionWords ≤
    goodExtractionWords layout routines bound drawWords :=
  BLSExtractor.good_words layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.divNames.buffers layout.port draw
    drawWordsBound bound.mulBound bound.addBound bound.subBound bound.divBound
include drawWordsBound in
theorem bad_extract_words : ((badExtractor layout routines P comparison correct draw).lower layout.port).descriptionWords ≤
    badExtractionWords layout routines bound drawWords :=
  BLSExtractor.bad_words layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarNeg routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.negNames.buffers routines.divNames.buffers layout.port draw
    drawWordsBound bound.mulBound bound.addBound bound.subBound bound.negBound bound.divBound

variable [SampleableType (val.Value base)]
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (invariant : Caller.Invariant layout caller fuel)
include drawCorrect drawLaw invariant drawTimeBound in
theorem good_tail_time : Interactive.TimeBoundOn (goodAdmitted layout fuel) layout.port .unit layout.goodInput
    (goodTail layout routines P comparison correct caller draw fuel) (goodTailTime layout routines bound caller localBound drawTime fuel) :=
  BLSCallerExtraction.time layout.good (zero layout routines) P comparison correct
    (goodResponse layout routines) (BLSResponse.good_buffers layout.scheme.response routines.groupScale routines.scaleNames.buffers)
    (layout.scheme.goodReserve routines.reserve) draw caller.advance caller.continuation caller.localNameFits
    layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.goodFits fuel drawSource drawCorrect drawLaw
    invariant.domain invariant.goodAdvance (goodAdmitted layout fuel) (fun value _ => invariant.initial value.1)
    (fun _ valid => valid.1) (fun _ valid => valid.2) drawTimeBound
    (BLSResponse.good_bounded layout.scheme.response routines.groupScale bound.scaleBound) localBound.localTime localBound.initialTime (zero layout routines)
    (good_extract_refines layout routines P comparison correct draw drawSource drawCorrect)
    (good_extract_time layout routines P comparison correct draw drawSource drawCorrect bound drawTimeBound)
include drawCorrect drawLaw invariant drawTimeBound in
theorem bad_tail_time : Interactive.TimeBoundOn (badAdmitted layout fuel) layout.port .unit layout.badInput
    (badTail layout routines P comparison correct caller draw fuel) (badTailTime layout routines bound caller localBound drawTime fuel) :=
  BLSCallerExtraction.time (base := base) (key := key) (val := .pair val val) layout.bad (pairZero layout routines) P comparison correct
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
    (fun _ valid => valid.1) (fun _ valid => valid.2)
    (PairSampling.time_bound (hw := layout.scheme.cache.wordFits) (fits := layout.scheme.cache.pairValueFits) drawCorrect drawCorrect drawTimeBound drawTimeBound)
    (BLSResponse.bad_bounded layout.scheme.response routines.groupScale routines.groupAdd bound.scaleBound bound.groupAddBound
      routines.scaleNames.buffers (by have := routines.reserve; omega) routines.groupAddNames.buffers)
    localBound.localTime localBound.initialTime (zero layout routines)
    (bad_extract_refines layout routines P comparison correct draw drawSource drawCorrect)
    (bad_extract_time layout routines P comparison correct draw drawSource drawCorrect bound drawTimeBound)

omit [SampleableType (val.Value base)] in
include drawWordsBound in
theorem good_tail_words : ((goodTail layout routines P comparison correct caller draw fuel).lower layout.port).descriptionWords ≤
    goodTailWords layout routines bound caller localBound drawWords fuel :=
  BLSCallerExtraction.words layout.good (zero layout routines) P comparison correct
    (goodResponse layout routines) (BLSResponse.good_buffers layout.scheme.response routines.groupScale routines.scaleNames.buffers)
    (layout.scheme.goodReserve routines.reserve) draw caller.advance caller.continuation caller.localNameFits
    layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.goodFits fuel drawWordsBound
    (BLSResponse.good_bounded layout.scheme.response routines.groupScale bound.scaleBound) localBound.localWords localBound.initialWords (zero layout routines)
    (good_extract_words layout routines P comparison correct draw bound drawWordsBound)
omit [SampleableType (val.Value base)] in
include drawWordsBound in
theorem bad_tail_words : ((badTail layout routines P comparison correct caller draw fuel).lower layout.port).descriptionWords ≤
    badTailWords layout routines bound caller localBound drawWords fuel :=
  BLSCallerExtraction.words (base := base) (key := key) (val := .pair val val) layout.bad (pairZero layout routines) P comparison correct
    (badResponse layout routines) (BLSResponse.bad_buffers layout.scheme.response routines.groupScale routines.groupAdd routines.scaleNames.buffers
      (by have := routines.reserve; omega) routines.groupAddNames.buffers)
    (layout.scheme.badReserve routines.reserve) (pairDraw layout draw) caller.advance caller.continuation caller.localNameFits
    layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.badFits fuel
    (PairSampling.code_bound layout.scheme.cache.value layout.scheme.cache.value layout.scheme.cache.wordFits layout.scheme.cache.pairValueFits layout.port draw draw drawWordsBound drawWordsBound)
    (BLSResponse.bad_bounded layout.scheme.response routines.groupScale routines.groupAdd bound.scaleBound bound.groupAddBound
      routines.scaleNames.buffers (by have := routines.reserve; omega) routines.groupAddNames.buffers)
    localBound.localWords localBound.initialWords (zero layout routines)
    (bad_extract_words layout routines P comparison correct draw bound drawWordsBound)

variable (logRoom : fuel ≤ layout.tokens.capacity) (cacheRoom : 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1)
include drawCorrect drawLaw invariant drawTimeBound logRoom cacheRoom in
theorem good_time : Interactive.TimeBound layout.port .unit layout.setup.challenge.representation
    (goodCode layout routines P comparison correct caller draw fuel) (goodTime layout routines bound caller localBound drawTime fuel) := by
  have composed := ((BLSSetup.good_time layout.setup layout.port).on (fun _ => True)).seq
    ((good_setup_refines layout).on (fun _ => True))
    (good_tail_time layout routines P comparison correct caller draw fuel drawSource drawCorrect bound localBound drawTimeBound drawLaw invariant) (by
      intro value _ answer reached
      have equal : answer = goodStart layout value := by simpa only [support_pure, Set.mem_singleton_iff] using reached
      subst answer
      exact good_start_admitted layout fuel logRoom cacheRoom value)
  exact fun tape value before holds finished reached => composed tape value trivial before holds finished reached
include drawCorrect drawLaw invariant drawTimeBound logRoom cacheRoom in
theorem bad_time : Interactive.TimeBound layout.port .unit layout.setup.challenge.representation
    (badCode layout routines P comparison correct caller draw fuel) (badTime layout routines bound caller localBound drawTime fuel) := by
  have setupBound := BLSSetup.bad_time layout.setup layout.port draw drawSource drawCorrect drawTimeBound
    routines.keyScale routines.keyNames.buffers (by have := routines.reserve; omega) bound.keyBound
  have composed := (setupBound.on (fun _ => True)).seq
    ((bad_setup_refines layout routines draw drawSource drawCorrect).on (fun _ => True))
    (bad_tail_time layout routines P comparison correct caller draw fuel drawSource drawCorrect bound localBound drawTimeBound drawLaw invariant)
    (fun value _ answer reached => bad_start_admitted layout routines drawSource fuel logRoom cacheRoom value answer reached)
  exact fun tape value before holds finished reached => composed tape value trivial before holds finished reached

omit [SampleableType (val.Value base)] in
include drawWordsBound in
theorem good_words : ((goodCode layout routines P comparison correct caller draw fuel).lower layout.port).descriptionWords ≤
    goodWords layout routines bound caller localBound drawWords fuel := by
  have setupBound := BLSSetup.good_words layout.setup layout.port
  have tailBound := good_tail_words layout routines P comparison correct caller draw fuel bound localBound drawWordsBound
  simp only [goodCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, goodWords]
  exact Nat.add_le_add_right (Nat.add_le_add setupBound tailBound) 1
omit [SampleableType (val.Value base)] in
include drawWordsBound in
theorem bad_words : ((badCode layout routines P comparison correct caller draw fuel).lower layout.port).descriptionWords ≤
    badWords layout routines bound caller localBound drawWords fuel := by
  have setupBound := BLSSetup.bad_words layout.setup layout.port draw drawWordsBound
    routines.keyScale routines.keyNames.buffers (by have := routines.reserve; omega) bound.keyBound
  have tailBound := bad_tail_words layout routines P comparison correct caller draw fuel bound localBound drawWordsBound
  simp only [badCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, badWords]
  exact Nat.add_le_add_right (Nat.add_le_add setupBound tailBound) 1
end Signatures.Runtime.CaliperBackend.BLSFull
