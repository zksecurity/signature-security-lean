import Proofs.Runtime.Caliper.SchnorrROMFullSecurity
import Proofs.Runtime.BackendSchnorrNonzeroReduction
import Proofs.Schnorr.NonzeroLazyROM

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

end Signatures.Runtime.CaliperBackend.SchnorrROM.Full.Nonzero
