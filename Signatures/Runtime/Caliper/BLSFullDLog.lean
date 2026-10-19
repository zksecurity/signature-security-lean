import Signatures.Runtime.Caliper.BLSFullWithin
import Signatures.Runtime.Caliper.BLSFullEquivalence
import Signatures.Runtime.Caliper.BLSFullChallenges
import Signatures.Runtime.Caliper.DLog

/-! Construct the two original BLS reductions' DLog efficiency certificates in
the fixed Caliper model. Challenge coverage follows from the represented
generators and primitive scaling; exact source equality and every resource bound
follow from the assembled programs. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {G K A : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Field (val.Value base)] [SampleableType (val.Value base)]
    [AddCommGroup G] [Module (val.Value base) G] [AddCommGroup K] [Module (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A) (routines : Routines layout)
    (bound : Routines.Bounds layout routines) (caller : Caller layout) (localBound : Caller.Bounds layout caller)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
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
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (invariant : Caller.Invariant layout caller fuel)
    (logRoom : fuel ≤ layout.tokens.capacity) (cacheRoom : 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1)
    (witness : Caller.Correspondence layout caller invariant)
    (adversary : Model.LazyAGM.Adversary (val.Value base) (key.Value base) (key.Value base) G K)
    (same : ∀ pk : layout.key.Value, (fun answer => output answer.val) <$> witness.source pk.val = adversary.main pk.val)
    (generator : layout.scheme.point.Value) (keyGenerator : layout.key.Value)

include correct drawCorrect drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw logRoom cacheRoom same in
theorem good_dlogWithin :
    dlogWithin layout.port layout.setup.challenge layout.scheme.cache.value generator.val keyGenerator.val
      (goodWords layout routines bound caller localBound drawWords fuel)
      (goodMemory layout routines bound caller localBound drawTime drawWords drawNames fuel)
      (goodTime layout routines bound caller localBound drawTime fuel)
      (BLS.LazyAGM.Reduction.goodReductionList adversary) := by
  refine ⟨challenge_valid layout routines drawSource drawLaw generator keyGenerator, ?_⟩
  exact (good_within layout routines bound caller localBound P comparison correct draw fuel drawSource drawCorrect
    drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw invariant logRoom cacheRoom).congr
      (good_source layout routines P comparison correct caller fuel drawSource drawLaw invariant witness adversary same logRoom cacheRoom)

include correct drawCorrect drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw logRoom cacheRoom same in
theorem bad_dlogWithin :
    dlogWithin layout.port layout.setup.challenge layout.scheme.cache.value generator.val keyGenerator.val
      (badWords layout routines bound caller localBound drawWords fuel)
      (badMemory layout routines bound caller localBound drawTime drawWords drawNames fuel)
      (badTime layout routines bound caller localBound drawTime fuel)
      (BLS.LazyAGM.Reduction.badReductionList adversary) := by
  refine ⟨challenge_valid layout routines drawSource drawLaw generator keyGenerator, ?_⟩
  exact (bad_within layout routines bound caller localBound P comparison correct draw fuel drawSource drawCorrect
    drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw invariant logRoom cacheRoom).congr
      (bad_source layout routines P comparison correct caller fuel drawSource drawLaw invariant witness adversary same logRoom cacheRoom)
end Signatures.Runtime.CaliperBackend.BLSFull
