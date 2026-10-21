import Signatures.Runtime.Caliper.SchnorrROMFullSecurity
import Signatures.Runtime.BackendSchnorrNonzeroReduction
import Signatures.Schnorr.Proofs.NonzeroLazyROM

/-! The same executed solver, with a signing branch whose source law is the
nonzero-nonce list backend, is the nonzero-nonce reduction: class membership
and challenge coverage are shared with the full-field route, and the
nonzero-nonce forking bound transfers to the fixed Caliper class. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Full.Nonzero
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (shape : Shape config) (caller : Caller config shape)
    (ops : Handler.Operations config) (law : Handler.SigningLaw config ops.signing)
    [inst : SampleableType F] [SampleableType Fˣ]
    (nonzero : letI := PrivateSampler.Enumerated.sampleable config.sampler
      law.target = Schnorr.NonzeroListROM.handler (G₂ := G) (K := M))
    (budget : Handler.Budget config ops) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)
    (limits : Limits) (bounded : caller.Bounds config shape limits)
    (arith : ReplayFork.Extract.Arithmetic config) (arithBudget : ReplayFork.Extract.Arithmetic.Budget config arith)
    (handlerRoom : Handler.nameBudget config ops ≤ limits.names) (slotsRoom : ops.slots + 4 < 2 ^ w)
    (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1) (tapes : 6 * fuel + 3 ≤ config.sampler.capacity)
    (sampled : inst = PrivateSampler.Enumerated.sampleable config.sampler)
    (witness : Pass.Caller.Source config (caller.toPass config shape) fuel)
    (attacker : G → OracleComp (Schnorr.ListROM.NativeInterface.sourceSpec F G M) (M × G × F))
    (same : ∀ pk : config.point.Value, Subtype.val <$> witness.program (witness.inputView pk) = attacker pk.val)

include sampled nonzero same in
theorem source_original (value : (Pass.Initialization.points config).Value) :
    Subtype.val <$> ReplayFork.Extract.fullSource config (caller.toPass config shape) ops qH indexFits fuel tables tapes value =
      Schnorr.NonzeroListROM.NativeSolver.reduction (G₂ := G) (K := M) attacker qH value.val.1 value.val.2 := by
  subst sampled
  rw [ReplayFork.Extract.fullSource_original config (caller.toPass config shape) ops law qH indexFits fuel witness tables tapes value]
  unfold Schnorr.NonzeroListROM.NativeSolver.reduction ReplayFork.originalMain
  rw [nonzero, same ⟨value.val.2, value.property.2⟩]
  rfl

include bounded handlerRoom slotsRoom tables tapes sampled nonzero same in
theorem within_original :
    Interactive.Within (Fresh.port config.handler.sampler.tape) (Pass.Initialization.points config) config.handler.sampler.tape.scalar
      (codeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (memoryBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (timeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (fun value => Schnorr.NonzeroListROM.NativeSolver.reduction (G₂ := G) (K := M) attacker qH value.val.1 value.val.2) :=
  (within config shape caller ops budget qH indexFits limits bounded arith arithBudget handlerRoom slotsRoom fuel tables tapes).congr
    (source_original config shape caller ops law nonzero qH indexFits fuel tables tapes sampled witness attacker same)

variable (generator : config.point.Value)

include bounded handlerRoom slotsRoom tables tapes sampled nonzero same in
theorem dlogWithin :
    cyclicDLogWithin (Fresh.port config.handler.sampler.tape) (Pass.Initialization.points config) config.handler.sampler.tape.scalar generator.val
      (codeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (memoryBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (timeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (Schnorr.NonzeroListROM.NativeSolver.reduction (G₂ := G) (K := M) attacker qH) :=
  ⟨challenge_valid config ops generator,
    within_original config shape caller ops law nonzero budget qH indexFits limits bounded arith arithBudget handlerRoom slotsRoom
      fuel tables tapes sampled witness attacker same⟩

section Security
variable [Fintype F] [SampleableType G]
    (generates : Function.Bijective (fun x : F => x • generator.val))
    (adversary : _root_.Schnorr.NonzeroNonce.Adversary (F := F) (M := M) generator.val) (qS : Nat)

include bounded handlerRoom slotsRoom tables tapes sampled nonzero generates in
/-- The nonzero-nonce forking bound: signing loss over `|F| − 1`, fork loss over
`|F|`, and the DLog term over the fixed Caliper class at the shape-level budgets. -/
theorem security
    (same : ∀ pk : config.point.Value, Subtype.val <$> witness.program (witness.inputView pk) = adversary.main pk.val)
    (queries : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adversary.main pk) qS qH) :
    𝒟[_root_.Schnorr.NonzeroNonce.game generator.val adversary] {true} ≤
      (qS : ENNReal) * (qS + qH) * ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹ +
      (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
      ((qH + 1 : ENNReal) * cyclicDLogSuccessBound (Fresh.port config.handler.sampler.tape)
        (Pass.Initialization.points config) config.handler.sampler.tape.scalar generator.val
        (codeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
        (memoryBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
        (timeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)) ^ (1 / 2 : ℝ) := by
  have fits := dlogWithin config shape caller ops law nonzero budget qH indexFits limits bounded arith arithBudget handlerRoom slotsRoom
    fuel tables tapes sampled witness adversary.main same generator
  have hardness := Model.le_advantageBound
    (fun solver => 𝒟[DiffieHellman.dlogExperiment generator.val solver] {true}) _ _ fits
  rw [Schnorr.NonzeroListROM.NativeSolver.reduction_experiment (G₂ := G) (K := M) generator.val adversary qH] at hardness
  apply Model.forking_inverse qH (MeasureTheory.measure_ne_top _ _) (ENNReal.inv_ne_top.mpr (by positivity))
  exact (_root_.Schnorr.NonzeroNonce.LazyROM.security generator.val generates adversary qS qH queries).trans hardness
end Security

end Signatures.Runtime.CaliperBackend.SchnorrROM.Full.Nonzero
