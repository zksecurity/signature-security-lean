import Proofs.Runtime.Caliper.SchnorrROMFullShape
import Proofs.Runtime.Caliper.CyclicDLog
import Proofs.Runtime.BackendSchnorrROMReduction
import Proofs.Schnorr.LazyROM
import Proofs.Model.ForkingLoss

/-! The complete executed Schnorr ROM solver belongs to the cyclic DLog class at
the shape-level budgets, and the original ROM forking bound transfers to that
class. Only the attacker's local routines, their declared allowances and the
source correspondence of its caller are supplied; the reduction witness, its
resources and the challenge coverage are constructed. The ambient scalar sampler
must be the enumerated draw that the handler executes (`sampled`). -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Full
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (shape : Shape config) (caller : Caller config shape)
    (ops : Handler.Operations config) (law : Handler.SigningLaw config ops.signing)
    (full : letI := PrivateSampler.Enumerated.sampleable config.sampler; law.target = Schnorr.ListROM.handler (G₂ := G) (K := M))
    (budget : Handler.Budget config ops) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)
    (limits : Limits) (bounded : caller.Bounds config shape limits)
    (arith : ReplayFork.Extract.Arithmetic config) (arithBudget : ReplayFork.Extract.Arithmetic.Budget config arith)
    (handlerRoom : Handler.nameBudget config ops ≤ limits.names) (slotsRoom : ops.slots + 4 < 2 ^ w)
    (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1) (tapes : 6 * fuel + 3 ≤ config.sampler.capacity)

include bounded handlerRoom slotsRoom in
theorem within :
    Interactive.Within (Fresh.port config.handler.sampler.tape) (Pass.Initialization.points config) config.handler.sampler.tape.scalar
      (codeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (memoryBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (timeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (fun value => Subtype.val <$> ReplayFork.Extract.fullSource config (caller.toPass config shape) ops qH indexFits fuel tables tapes value) :=
  Interactive.within_of_refines_accounted (input := Pass.Initialization.points config) (output := config.handler.sampler.tape.scalar)
    (ReplayFork.Extract.full_refines config (caller.toPass config shape) ops qH indexFits arith fuel tables tapes)
    (ReplayFork.Extract.full_time config (caller.toPass config shape) ops qH indexFits budget
      (bounded.localBudget config shape caller limits) arith arithBudget fuel tables tapes)
    (ReplayFork.Extract.full_words config (caller.toPass config shape) ops qH indexFits budget
      (bounded.localBudget config shape caller limits) arith arithBudget fuel)
    (ReplayFork.Extract.full_names config (caller.toPass config shape) ops qH indexFits arith limits.names handlerRoom
      bounded.localNames bounded.initialNames fuel)
    (ReplayFork.Extract.full_descriptionFits config (caller.toPass config shape) ops qH indexFits arith
      ⟨slotsRoom, bounded.localRoom, bounded.initialRoom⟩ fuel)

variable [inst : SampleableType F] (sampled : inst = PrivateSampler.Enumerated.sampleable config.sampler)
    (witness : Pass.Caller.Source config (caller.toPass config shape) fuel)
    (attacker : G → OracleComp (Schnorr.ListROM.NativeInterface.sourceSpec F G M) (M × G × F))
    (same : ∀ pk : config.point.Value, Subtype.val <$> witness.program (witness.inputView pk) = attacker pk.val)

include sampled full same in
theorem source_original (value : (Pass.Initialization.points config).Value) :
    Subtype.val <$> ReplayFork.Extract.fullSource config (caller.toPass config shape) ops qH indexFits fuel tables tapes value =
      Schnorr.ListROM.NativeSolver.reduction (G₂ := G) (K := M) attacker qH value.val.1 value.val.2 := by
  subst sampled
  rw [ReplayFork.Extract.fullSource_original config (caller.toPass config shape) ops law qH indexFits fuel witness tables tapes value]
  unfold Schnorr.ListROM.NativeSolver.reduction ReplayFork.originalMain
  rw [full, same ⟨value.val.2, value.property.2⟩]
  rfl

include bounded handlerRoom slotsRoom tables tapes sampled full same in
theorem within_original :
    Interactive.Within (Fresh.port config.handler.sampler.tape) (Pass.Initialization.points config) config.handler.sampler.tape.scalar
      (codeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (memoryBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (timeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (fun value => Schnorr.ListROM.NativeSolver.reduction (G₂ := G) (K := M) attacker qH value.val.1 value.val.2) :=
  (within config shape caller ops budget qH indexFits limits bounded arith arithBudget handlerRoom slotsRoom fuel tables tapes).congr
    (source_original config shape caller ops law full qH indexFits fuel tables tapes sampled witness attacker same)

variable (generator : config.point.Value)

omit [DecidableEq F] [DecidableEq M] [DecidableEq G] inst in
include ops in
/-- Every DLog challenge `(g, x • g)` is represented: scalars are all valid and the
handler's implemented scaling preserves point validity. -/
theorem challenge_valid (scalar : F) : (Pass.Initialization.points config).valid (generator.val, scalar • generator.val) :=
  ⟨generator.property, ops.scale.preserves (scalar, generator.val) ⟨trivial, generator.property⟩⟩

include bounded handlerRoom slotsRoom tables tapes sampled full same in
theorem dlogWithin :
    cyclicDLogWithin (Fresh.port config.handler.sampler.tape) (Pass.Initialization.points config) config.handler.sampler.tape.scalar generator.val
      (codeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (memoryBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (timeBudget config shape limits ops budget qH indexFits arith arithBudget fuel)
      (Schnorr.ListROM.NativeSolver.reduction (G₂ := G) (K := M) attacker qH) :=
  ⟨challenge_valid config ops generator,
    within_original config shape caller ops law full budget qH indexFits limits bounded arith arithBudget handlerRoom slotsRoom fuel tables tapes
      sampled witness attacker same⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Full
