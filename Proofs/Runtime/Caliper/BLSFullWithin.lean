import Proofs.Runtime.Caliper.BLSFullResources
import Proofs.Runtime.Caliper.Within

/-! Both generated BLS AGM programs belong to the actual Caliper resource class.
The witnesses are the constructed programs. All budgets are computed from the
primitive and caller ledgers; the input buffer and its descriptor are charged. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {G K A : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] [SMul (val.Value base) G] [Add G] [SMul (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A) (routines : Routines layout)
    (bound : Routines.Bounds layout routines) (caller : Caller layout) (localBound : Caller.Bounds layout caller)

def goodMemory (drawTime drawWords drawNames fuel : Nat) : Nat :=
  5 * goodWords layout routines bound caller localBound drawWords fuel +
    4 * nameBudget layout routines caller localBound drawNames + 3 + layout.setup.challenge.representation.encoding.words +
    goodTime layout routines bound caller localBound drawTime fuel
def badMemory (drawTime drawWords drawNames fuel : Nat) : Nat :=
  5 * badWords layout routines bound caller localBound drawWords fuel +
    4 * nameBudget layout routines caller localBound drawNames + 3 + layout.setup.challenge.representation.encoding.words +
    badTime layout routines bound caller localBound drawTime fuel

def solverWords (drawWords fuel : Nat) : Nat :=
  max (goodWords layout routines bound caller localBound drawWords fuel) (badWords layout routines bound caller localBound drawWords fuel)
def solverMemory (drawTime drawWords drawNames fuel : Nat) : Nat :=
  max (goodMemory layout routines bound caller localBound drawTime drawWords drawNames fuel)
    (badMemory layout routines bound caller localBound drawTime drawWords drawNames fuel)
def solverTime (drawTime fuel : Nat) : Nat :=
  max (goodTime layout routines bound caller localBound drawTime fuel) (badTime layout routines bound caller localBound drawTime fuel)

variable {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (draw : Interactive.Code w) (fuel : Nat)
    (drawSource : ProbComp layout.scheme.cache.value.Value)
    (drawCorrect : Interactive.Refines layout.port .unit layout.scheme.cache.lookup.unit.representation
      layout.scheme.cache.value.representation (fun _ => drawSource) draw)
    {drawTime drawWords drawNames : Nat}
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.scheme.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)
    (drawNamed : WordIO.NamesBound (draw.lower layout.port) drawNames)
    (drawFits : (draw.lower layout.port).DescriptionFits)
    (addresses : AddressBounds layout routines bound drawNames drawWords)
    [SampleableType (val.Value base)]
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (invariant : Caller.Invariant layout caller fuel)
    (logRoom : fuel ≤ layout.tokens.capacity) (cacheRoom : 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1)

include drawCorrect drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw invariant logRoom cacheRoom in
theorem good_within :
    Interactive.Within layout.port layout.setup.challenge layout.scheme.cache.value
      (goodWords layout routines bound caller localBound drawWords fuel)
      (goodMemory layout routines bound caller localBound drawTime drawWords drawNames fuel)
      (goodTime layout routines bound caller localBound drawTime fuel)
      (fun value => Subtype.val <$> goodSource layout routines P comparison correct caller fuel drawSource value) :=
  Interactive.within_of_refines_accounted
    (good_refines layout routines P comparison correct caller draw fuel drawSource drawCorrect drawLaw invariant logRoom cacheRoom)
    (good_time layout routines P comparison correct caller draw fuel drawSource drawCorrect bound localBound drawTimeBound drawLaw invariant logRoom cacheRoom)
    (good_words layout routines P comparison correct caller draw fuel bound localBound drawWordsBound)
    (good_names layout routines P comparison correct caller draw fuel localBound drawNamed)
    (good_fits layout routines bound P comparison correct caller draw fuel drawNamed drawWordsBound drawFits addresses)

include drawCorrect drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw invariant logRoom cacheRoom in
theorem bad_within :
    Interactive.Within layout.port layout.setup.challenge layout.scheme.cache.value
      (badWords layout routines bound caller localBound drawWords fuel)
      (badMemory layout routines bound caller localBound drawTime drawWords drawNames fuel)
      (badTime layout routines bound caller localBound drawTime fuel)
      (fun value => Subtype.val <$> badSource layout routines P comparison correct caller fuel drawSource value) :=
  Interactive.within_of_refines_accounted
    (bad_refines layout routines P comparison correct caller draw fuel drawSource drawCorrect drawLaw invariant logRoom cacheRoom)
    (bad_time layout routines P comparison correct caller draw fuel drawSource drawCorrect bound localBound drawTimeBound drawLaw invariant logRoom cacheRoom)
    (bad_words layout routines P comparison correct caller draw fuel bound localBound drawWordsBound)
    (bad_names layout routines P comparison correct caller draw fuel localBound drawNamed)
    (bad_fits layout routines bound P comparison correct caller draw fuel drawNamed drawWordsBound drawFits addresses)
end Signatures.Runtime.CaliperBackend.BLSFull
