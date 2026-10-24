import Proofs.Runtime.Caliper.SchnorrROMSigningHandler
import Proofs.Runtime.Caliper.SchnorrROMSigningSource

/-! The executed signing wrapper implements the original shared-tape oracle.
The scalar sampler premise is equality of the original query program, rather
than equality of its output distribution: replay preserves query chronology. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G G₂ K C : Type} [Field F] [SampleableType F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K]
    (layout : Layouts w M F G C) (zeroValid : layout.sampler.tape.scalar.valid 0)
    (scale : Implementation .unit layout.core.arithmetic.scaleArgs layout.core.point (fun value => value.1 • value.2))
    (sub : Implementation .unit layout.core.arithmetic.points layout.core.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (caller : PrivateSampler.Caller layout.sampler)
    (fuel : Nat) (terminates : PrivateSampler.Terminates layout.sampler caller fuel)
    (samples : Subtype.val <$> PrivateSampler.original layout.sampler caller fuel terminates
      (PrivateSampler.Service.unit layout.sampler) = ($ᵗ F : ProbComp F))

include terminates samples

theorem source_original (input : layout.input.Value) (valid : ready layout fuel input) :
    Subtype.val <$> source layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel input =
      (Schnorr.ListROM.Shared.interpret (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (.inr input.val.1))).run input.val.2 := by
  rw [Signing.signing_run]
  have same := congrArg (Functor.map (fun draws : F × F × Schnorr.ListROM.Shared.Tape F =>
    let computed := Core.value ((draws.1, draws.2.1), input.val.2.1.1.1, input.val.2.1.1.2, input.val.1, input.val.2.1.2.1)
    (computed.1, (computed.2.1, computed.2.2, input.val.2.1.2.2), draws.2.2)))
    (PrivateSampler.Pair.scalar_source layout.sampler caller zeroValid fuel terminates samples (tapes layout input) valid)
  simp only [source, Functor.map_map, map_bind, bind_pure_comp, result, finishValue, coreValue, context, tapes] at same ⊢
  convert same using 1

theorem observe_original (tape : RandomTape w) (input : layout.input.Value) (valid : ready layout fuel input)
    (before : State w) (holds : layout.input.representation.Holds input before) :
    (fun result => (Interactive.observe layout.output.representation result).map Subtype.val) <$>
      (code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).execute (Fresh.port layout.sampler.tape) .unit tape before =
        some <$> (Schnorr.ListROM.Shared.interpret
          (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (.inr input.val.1))).run input.val.2 := by
  have observed := (refines layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).observe tape input valid before holds
  have mapped := congrArg (Functor.map (Option.map Subtype.val)) observed
  simp only [Functor.map_map, Option.map_some] at mapped
  have same := source_original (G₂ := G₂) (K := K) layout zeroValid scale sub scaleBuffers subBuffers reserve caller
    fuel terminates samples input valid
  simpa only [Functor.map_map, Option.map_some] using mapped.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
