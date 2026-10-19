import Signatures.Runtime.Caliper.BLSFullBounds

/-! Complete register/descriptor accounting is derived from the primitive
reservations, actual local caller code and constructed setup/extraction. -/
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
    (localBound : Caller.Bounds layout caller) {drawNames : Nat}
    (drawNamed : WordIO.NamesBound (draw.lower layout.port) drawNames)

include drawNamed in
theorem good_extract_names : WordIO.NamesAccounted ((goodExtractor layout routines P comparison correct draw).lower layout.port)
    (BLSExtractor.nameBudget drawNames routines.slots) :=
  BLSExtractor.good_names layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.divNames.buffers layout.port draw
    drawNamed routines.mulNames.accounted routines.addNames.accounted routines.subNames.accounted routines.divNames.accounted
include drawNamed in
theorem bad_extract_names : WordIO.NamesAccounted ((badExtractor layout routines P comparison correct draw).lower layout.port)
    (BLSExtractor.nameBudget drawNames routines.slots) :=
  BLSExtractor.bad_names layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarNeg routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.negNames.buffers routines.divNames.buffers layout.port draw
    drawNamed routines.mulNames.accounted routines.addNames.accounted routines.subNames.accounted routines.negNames.accounted routines.divNames.accounted

include drawNamed in
theorem good_tail_names : WordIO.NamesAccounted ((goodTail layout routines P comparison correct caller draw fuel).lower layout.port)
    (nameBudget layout routines caller localBound drawNames) := by
  have bounds : 5 ≤ nameBudget layout routines caller localBound drawNames ∧ drawNames ≤ nameBudget layout routines caller localBound drawNames ∧
      routines.slots ≤ nameBudget layout routines caller localBound drawNames := by
    dsimp only [nameBudget, BLSExtractor.nameBudget, BLSSignatureTail.nameBudget, PairSampling.slots]
    omega
  exact BLSCallerExtraction.names layout.good (zero layout routines) P comparison correct
    (goodResponse layout routines) (BLSResponse.good_buffers layout.scheme.response routines.groupScale routines.scaleNames.buffers)
    (layout.scheme.goodReserve routines.reserve) draw caller.advance caller.continuation caller.localNameFits
    layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.goodFits fuel (zero layout routines)
    bounds.1 drawNamed (BLSResponse.good_names layout.scheme.response routines.slots routines.groupScale routines.scaleNames.accounted)
    bounds.2.1 bounds.2.2
    (localBound.localNames.mono (Nat.le_max_right _ _)) (localBound.initialNames.mono (Nat.le_max_right _ _))
    ((good_extract_names layout routines P comparison correct draw drawNamed).mono (Nat.le_max_left _ _))
include drawNamed in
theorem bad_tail_names : WordIO.NamesAccounted ((badTail layout routines P comparison correct caller draw fuel).lower layout.port)
    (nameBudget layout routines caller localBound drawNames) := by
  have bounds : 5 ≤ nameBudget layout routines caller localBound drawNames ∧
      PairSampling.slots drawNames drawNames ≤ nameBudget layout routines caller localBound drawNames ∧
      routines.slots ≤ nameBudget layout routines caller localBound drawNames := by
    dsimp only [nameBudget, BLSExtractor.nameBudget, BLSSignatureTail.nameBudget]
    omega
  exact BLSCallerExtraction.names (base := base) (key := key) (val := .pair val val) layout.bad (pairZero layout routines) P comparison correct
    (badResponse layout routines) (BLSResponse.bad_buffers layout.scheme.response routines.groupScale routines.groupAdd routines.scaleNames.buffers
      (by have := routines.reserve; omega) routines.groupAddNames.buffers)
    (layout.scheme.badReserve routines.reserve) (pairDraw layout draw) caller.advance caller.continuation caller.localNameFits
    layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.badFits fuel (zero layout routines) bounds.1
    (PairSampling.names layout.scheme.cache.value layout.scheme.cache.value layout.scheme.cache.wordFits layout.scheme.cache.pairValueFits layout.port draw draw drawNamed drawNamed)
    (BLSResponse.bad_names layout.scheme.response routines.slots routines.groupScale routines.groupAdd routines.scaleNames.accounted routines.groupAddNames.accounted
      routines.scaleNames.buffers (by have := routines.reserve; omega) routines.groupAddNames.buffers)
    bounds.2.1 bounds.2.2
    (localBound.localNames.mono (Nat.le_max_right _ _)) (localBound.initialNames.mono (Nat.le_max_right _ _))
    ((bad_extract_names layout routines P comparison correct draw drawNamed).mono (Nat.le_max_left _ _))
include drawNamed in
theorem good_names : WordIO.NamesAccounted ((goodCode layout routines P comparison correct caller draw fuel).lower layout.port)
    (nameBudget layout routines caller localBound drawNames) := by
  have setupBound := WordIO.NamesAccounted.compute (BLSSetup.good_names layout.setup 0)
  have setupNames : WordIO.NamesAccounted ((BLSSetup.goodCode layout.setup).lower layout.port)
      (nameBudget layout routines caller localBound drawNames) := setupBound.mono (by
    dsimp only [nameBudget, BLSExtractor.nameBudget, BLSSignatureTail.nameBudget]
    omega)
  exact setupNames.seq (good_tail_names layout routines P comparison correct caller draw fuel localBound drawNamed)
include drawNamed in
theorem bad_names : WordIO.NamesAccounted ((badCode layout routines P comparison correct caller draw fuel).lower layout.port)
    (nameBudget layout routines caller localBound drawNames) := by
  have setupBound := BLSSetup.bad_names layout.setup layout.port draw routines.keyScale routines.keyNames.buffers (by have := routines.reserve; omega)
    drawNamed routines.keyNames.accounted
  have setupNames := setupBound.mono (show max (max 3 drawNames) routines.slots ≤ nameBudget layout routines caller localBound drawNames from by
    dsimp only [nameBudget, BLSExtractor.nameBudget, BLSSignatureTail.nameBudget, PairSampling.slots]
    omega)
  exact setupNames.seq (bad_tail_names layout routines P comparison correct caller draw fuel localBound drawNamed)
end Signatures.Runtime.CaliperBackend.BLSFull
