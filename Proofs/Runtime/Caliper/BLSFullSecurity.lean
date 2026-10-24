import Proofs.Runtime.Caliper.BLSFullDLog
import Proofs.BLS.LazyAGMArbitraryMessages
import Proofs.Model.DirectAGM

/-! Concrete BLS AGM security against the fixed Caliper DLog class. Both full
reduction certificates are constructed from named primitive implementations and
local caller code. Time, stored code and total memory are all derived. The
shared-AGM source game stays separate from these implementation obligations. -/
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


variable {GT : Type} [Fintype (val.Value base)] [SampleableType G] [Fintype G]
    [DecidableEq (val.Value base)] [DecidableEq GT]
    [AddCommGroup GT] [Module (val.Value base) GT] [BilinearGroup.BilinearPairing (val.Value base) G K GT]
    (generates : Function.Bijective (fun scalar : val.Value base => scalar • generator.val))
    (pairingInjective : Function.Injective (fun scalar : val.Value base =>
      scalar • (BilinearGroup.pairing (F := val.Value base) generator.val keyGenerator.val : GT)))

include generates pairingInjective correct drawCorrect drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw logRoom cacheRoom same in
theorem security :
    𝒟[BLS.LazyAGM.game (Gₜ := GT) generator.val keyGenerator.val adversary] {true} ≤
      2 * dlogSuccessBound layout.port layout.setup.challenge layout.scheme.cache.value generator.val keyGenerator.val
        (solverWords layout routines bound caller localBound drawWords fuel)
        (solverMemory layout routines bound caller localBound drawTime drawWords drawNames fuel)
        (solverTime layout routines bound caller localBound drawTime fuel) +
      1 / (Fintype.card (val.Value base) : ENNReal) := by
  have good := good_dlogWithin layout routines bound caller localBound P comparison correct draw fuel drawSource drawCorrect
    drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw invariant logRoom cacheRoom witness adversary same generator keyGenerator
  have bad := bad_dlogWithin layout routines bound caller localBound P comparison correct draw fuel drawSource drawCorrect
    drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw invariant logRoom cacheRoom witness adversary same generator keyGenerator
  have goodBound := Model.le_advantageBound (Model.dlog11Advantage generator.val keyGenerator.val)
    (dlogWithin layout.port layout.setup.challenge layout.scheme.cache.value generator.val keyGenerator.val
      (solverWords layout routines bound caller localBound drawWords fuel)
      (solverMemory layout routines bound caller localBound drawTime drawWords drawNames fuel)
      (solverTime layout routines bound caller localBound drawTime fuel)) _
    (good.mono (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have badBound := Model.le_advantageBound (Model.dlog11Advantage generator.val keyGenerator.val)
    (dlogWithin layout.port layout.setup.challenge layout.scheme.cache.value generator.val keyGenerator.val
      (solverWords layout routines bound caller localBound drawWords fuel)
      (solverMemory layout routines bound caller localBound drawTime drawWords drawNames fuel)
      (solverTime layout routines bound caller localBound drawTime fuel)) _
    (bad.mono (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have probability := BLS.LazyAGM.Reduction.security_arbitrary_messages_list generator.val keyGenerator.val adversary generates pairingInjective
  simpa only [two_mul, dlogSuccessBound] using probability.trans (add_le_add (add_le_add goodBound badBound) le_rfl)

omit same in
include generates pairingInjective correct drawCorrect drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw logRoom cacheRoom in
theorem direct_security
    (attack : Model.DirectAGM.Adversary (val.Value base) (key.Value base) (key.Value base) G K)
    (source : ∀ pk : layout.key.Value, (fun answer => output answer.val) <$> witness.source pk.val =
      (Model.DirectAGM.ProofView.adversary generator.val attack).main pk.val) :
    𝒟[Model.DirectAGM.game (Gₜ := GT) BLS.LazyAGM.terms (fun _ _ => True) generator.val keyGenerator.val attack] {true} ≤
      2 * dlogSuccessBound layout.port layout.setup.challenge layout.scheme.cache.value generator.val keyGenerator.val
        (solverWords layout routines bound caller localBound drawWords fuel)
        (solverMemory layout routines bound caller localBound drawTime drawWords drawNames fuel)
        (solverTime layout routines bound caller localBound drawTime fuel) +
      1 / (Fintype.card (val.Value base) : ENNReal) :=
  (Model.DirectAGM.game_le BLS.LazyAGM.terms (fun _ _ => True) generator.val keyGenerator.val attack).trans
    (security layout routines bound caller localBound P comparison correct draw fuel drawSource drawCorrect
      drawTimeBound drawWordsBound drawNamed drawFits addresses drawLaw invariant logRoom cacheRoom witness
      (Model.DirectAGM.ProofView.adversary generator.val attack) source generator keyGenerator generates pairingInjective)
end Signatures.Runtime.CaliperBackend.BLSFull
