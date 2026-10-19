import Signatures.Runtime.Caliper.BLSFullNames

/-! Address-width bounds for generated saved-buffer names are checked against
constructed handler budgets. Every stored operand of both full programs fits. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {G K A : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] [SMul (val.Value base) G] [Add G] [SMul (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A) (routines : Routines layout)
    (bound : Routines.Bounds layout routines)

def goodHandlerWords (drawWords : Nat) :=
  BLSOracle.codeBudget layout.good.service
    (BLSDispatch.codeBudget layout.good.service drawWords (fun _ => BLSResponse.goodWords layout.scheme.response bound.scale.words)) +
    710 * BLSCallerPackets.width layout.good.service + 420
def badHandlerWords (drawWords : Nat) :=
  BLSOracle.codeBudget layout.bad.service
    (BLSDispatch.codeBudget (base := base) (key := key) (val := .pair val val) layout.bad.service (PairSampling.codeBudget layout.scheme.cache.value layout.scheme.cache.value drawWords drawWords)
      (fun signing => BLSResponse.badWords layout.scheme.response signing bound.scale.words bound.groupAdd.words)) +
    710 * BLSCallerPackets.width layout.bad.service + 420
structure AddressBounds (drawNames drawWords : Nat) : Prop where
  draw : drawNames + 4 < 2 ^ w
  goodHandler : max (max 5 drawNames) routines.slots + goodHandlerWords layout routines bound drawWords + 1 < 2 ^ w
  badHandler : max (max 5 (PairSampling.slots drawNames drawNames)) routines.slots + badHandlerWords layout routines bound drawWords + 1 < 2 ^ w

variable {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller layout) (draw : Interactive.Code w) (fuel : Nat)
    {drawNames drawWords : Nat} (drawNamed : WordIO.NamesBound (draw.lower layout.port) drawNames)
    (drawStored : (draw.lower layout.port).descriptionWords ≤ drawWords)
    (drawFits : (draw.lower layout.port).DescriptionFits)
    (addresses : AddressBounds layout routines bound drawNames drawWords)

include drawNamed drawFits addresses in
theorem good_extract_fits : ((goodExtractor layout routines P comparison correct draw).lower layout.port).DescriptionFits :=
  BLSExtractor.good_descriptionFits layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.divNames.buffers layout.port draw
    drawFits drawNamed addresses.draw
include drawNamed drawFits addresses in
theorem bad_extract_fits : ((badExtractor layout routines P comparison correct draw).lower layout.port).DescriptionFits :=
  BLSExtractor.bad_descriptionFits layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarNeg routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.negNames.buffers routines.divNames.buffers layout.port draw
    drawFits drawNamed addresses.draw
include drawNamed drawStored drawFits addresses in
theorem good_tail_fits : ((goodTail layout routines P comparison correct caller draw fuel).lower layout.port).DescriptionFits :=
  BLSCallerExtraction.descriptionFits layout.good (zero layout routines) P comparison correct
    (goodResponse layout routines) (BLSResponse.good_buffers layout.scheme.response routines.groupScale routines.scaleNames.buffers)
    (layout.scheme.goodReserve routines.reserve) draw caller.advance caller.continuation caller.localNameFits
    layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.goodFits fuel drawStored
    (BLSResponse.good_bounded layout.scheme.response routines.groupScale bound.scaleBound) (zero layout routines) drawFits drawNamed
    (BLSResponse.good_names layout.scheme.response routines.slots routines.groupScale routines.scaleNames.accounted)
    addresses.goodHandler (good_extract_fits layout routines bound P comparison correct draw drawNamed drawFits addresses)
include drawNamed drawStored drawFits addresses in
theorem bad_tail_fits : ((badTail layout routines P comparison correct caller draw fuel).lower layout.port).DescriptionFits :=
  BLSCallerExtraction.descriptionFits (base := base) (key := key) (val := .pair val val) layout.bad (pairZero layout routines) P comparison correct
    (badResponse layout routines) (BLSResponse.bad_buffers layout.scheme.response routines.groupScale routines.groupAdd routines.scaleNames.buffers
      (by have := routines.reserve; omega) routines.groupAddNames.buffers)
    (layout.scheme.badReserve routines.reserve) (pairDraw layout draw) caller.advance caller.continuation caller.localNameFits
    layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.badFits fuel
    (PairSampling.code_bound layout.scheme.cache.value layout.scheme.cache.value layout.scheme.cache.wordFits layout.scheme.cache.pairValueFits layout.port draw draw drawStored drawStored)
    (BLSResponse.bad_bounded layout.scheme.response routines.groupScale routines.groupAdd bound.scaleBound bound.groupAddBound
      routines.scaleNames.buffers (by have := routines.reserve; omega) routines.groupAddNames.buffers) (zero layout routines)
    (PairSampling.descriptionFits layout.scheme.cache.value layout.scheme.cache.value layout.scheme.cache.wordFits layout.scheme.cache.pairValueFits layout.port draw draw
      drawFits drawFits drawNamed (by have := addresses.draw; omega))
    (PairSampling.names layout.scheme.cache.value layout.scheme.cache.value layout.scheme.cache.wordFits layout.scheme.cache.pairValueFits layout.port draw draw drawNamed drawNamed)
    (BLSResponse.bad_names layout.scheme.response routines.slots routines.groupScale routines.groupAdd routines.scaleNames.accounted routines.groupAddNames.accounted
      routines.scaleNames.buffers (by have := routines.reserve; omega) routines.groupAddNames.buffers)
    addresses.badHandler (bad_extract_fits layout routines bound P comparison correct draw drawNamed drawFits addresses)
include drawNamed drawStored drawFits addresses in
theorem good_fits : ((goodCode layout routines P comparison correct caller draw fuel).lower layout.port).DescriptionFits :=
  .seq layout.scheme.cache.wordFits (.compute (BLSSetup.good layout.setup).program.description_fits)
    (good_tail_fits layout routines bound P comparison correct caller draw fuel drawNamed drawStored drawFits addresses)
include drawNamed drawStored drawFits addresses in
theorem bad_fits : ((badCode layout routines P comparison correct caller draw fuel).lower layout.port).DescriptionFits :=
  .seq layout.scheme.cache.wordFits
    (BLSSetup.bad_descriptionFits layout.setup layout.port draw routines.keyScale routines.keyNames.buffers (by have := routines.reserve; omega)
      drawFits drawNamed (by have := addresses.draw; omega))
    (bad_tail_fits layout routines bound P comparison correct caller draw fuel drawNamed drawStored drawFits addresses)
end Signatures.Runtime.CaliperBackend.BLSFull
