import Signatures.Runtime.Caliper.SchnorrROMFinEnumSampler
import Signatures.Runtime.Caliper.SchnorrROMSigningHandlerMemory

/-! Signing with the constructed canonical scalar caller. Only group routines
remain local implementation parameters; sampler code, termination, source
correspondence and caller resource bounds are supplied by this construction. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Enumerated
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec

structure Configuration (w : Nat) (M F G : Type) where
  sampler : PrivateSampler.Enumerated.Parameters w F
  message : Layout w M
  point : Layout w G
  capacityPred : Nat
  countFits : capacityPred + 1 < 2 ^ w
  storageFits : 128 * (1 + (capacityPred + 1) * (message.representation.encoding.words +
    point.representation.encoding.words + 1) + 3 + 3 * point.representation.encoding.words +
    message.representation.encoding.words + (Read.tapes (PrivateSampler.Enumerated.tape sampler)).representation.encoding.words) < 2 ^ w

def Configuration.handler {w : Nat} {M F G : Type} (config : Configuration w M F G) : Handler.Layouts w M F G Unit where
  sampler := PrivateSampler.Enumerated.layout config.sampler
  message := config.message
  point := config.point
  capacityPred := config.capacityPred
  countFits := config.countFits
  storageFits := config.storageFits

variable {w : Nat} {M F G : Type} (config : Configuration w M F G)

section Code
variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (scale : Implementation .unit config.handler.core.arithmetic.scaleArgs config.handler.core.point (fun value => value.1 • value.2))
    (sub : Implementation .unit config.handler.core.arithmetic.points config.handler.core.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)

def code := Handler.code config.handler trivial scale sub scaleBuffers subBuffers reserve (PrivateSampler.Enumerated.caller config.sampler) 1
def source := Handler.source config.handler trivial scale sub scaleBuffers subBuffers reserve (PrivateSampler.Enumerated.caller config.sampler) 1

theorem time_bound {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords) :
    Interactive.TimeBoundOn (Handler.ready config.handler 1) (Fresh.port (PrivateSampler.Enumerated.tape config.sampler)) .unit config.handler.input.representation
      (code config scale sub scaleBuffers subBuffers reserve) (Handler.timeBudget config.handler trivial 38 16 1 scaleTime subTime) :=
  Handler.time_bound config.handler trivial scale sub scaleBuffers subBuffers reserve (PrivateSampler.Enumerated.caller config.sampler) 1 38 16
    (PrivateSampler.Enumerated.continuation_time config.sampler) (PrivateSampler.Enumerated.initial_time config.sampler) scaleBound subBound

theorem code_bound {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords) :
    ((code config scale sub scaleBuffers subBuffers reserve).lower (Fresh.port (PrivateSampler.Enumerated.tape config.sampler))).descriptionWords ≤
      Handler.codeBudget config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1 scaleWords subWords :=
  Handler.code_bound config.handler trivial scale sub scaleBuffers subBuffers reserve
    (PrivateSampler.Enumerated.caller config.sampler) 1 scaleBound subBound

theorem buffers : ((code config scale sub scaleBuffers subBuffers reserve).lower (Fresh.port (PrivateSampler.Enumerated.tape config.sampler))).memBound ≤
    max 11 (slots + 3) := by
  have bounded := Handler.buffers config.handler trivial scale sub scaleBuffers subBuffers reserve
    (PrivateSampler.Enumerated.caller config.sampler) 1
  have initial := PrivateSampler.Enumerated.initial_buffers config.sampler
  have localBound := PrivateSampler.Enumerated.continuation_buffers config.sampler
  change ((code config scale sub scaleBuffers subBuffers reserve).lower (Fresh.port (PrivateSampler.Enumerated.tape config.sampler))).memBound ≤ _ at bounded
  dsimp only [PrivateSampler.Service.bufferBudget, PrivateSampler.Enumerated.caller] at bounded
  omega

theorem names (primitiveNames : Nat) (scaleNames : NamesAccounted scale.program.code primitiveNames)
    (subNames : NamesAccounted sub.program.code primitiveNames) :
    WordIO.NamesAccounted ((code config scale sub scaleBuffers subBuffers reserve).lower (Fresh.port (PrivateSampler.Enumerated.tape config.sampler)))
      (Handler.nameBudget config.handler trivial 3 primitiveNames) :=
  Handler.names config.handler trivial scale sub scaleBuffers subBuffers reserve (PrivateSampler.Enumerated.caller config.sampler) 1 3 primitiveNames
    (PrivateSampler.Enumerated.continuation_names config.sampler).accounted (PrivateSampler.Enumerated.initial_names config.sampler).accounted scaleNames subNames

theorem descriptionFits : ((code config scale sub scaleBuffers subBuffers reserve).lower (Fresh.port (PrivateSampler.Enumerated.tape config.sampler))).DescriptionFits :=
  Handler.descriptionFits config.handler trivial scale sub scaleBuffers subBuffers reserve (PrivateSampler.Enumerated.caller config.sampler) 1
    (PrivateSampler.Enumerated.continuation_headroom config.sampler) (PrivateSampler.Enumerated.initial_headroom config.sampler)

end Code

section Source
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]
    {G₂ K : Type} [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K]
    (scale : Implementation .unit config.handler.core.arithmetic.scaleArgs config.handler.core.point (fun value => value.1 • value.2))
    (sub : Implementation .unit config.handler.core.arithmetic.points config.handler.core.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)

theorem source_original (input : config.handler.input.Value) (valid : Handler.ready config.handler 1 input) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Subtype.val <$> source config scale sub scaleBuffers subBuffers reserve input =
      (Schnorr.ListROM.Shared.interpret (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (.inr input.val.1))).run input.val.2 := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  exact Handler.source_original (G₂ := G₂) (K := K) config.handler trivial scale sub scaleBuffers subBuffers reserve
    (PrivateSampler.Enumerated.caller config.sampler) 1 (PrivateSampler.Enumerated.terminates config.sampler)
    (PrivateSampler.Enumerated.samples config.sampler (PrivateSampler.Service.unit (PrivateSampler.Enumerated.layout config.sampler))) input valid

theorem observe_original (tape : RandomTape w) (input : config.handler.input.Value) (valid : Handler.ready config.handler 1 input)
    (before : State w) (holds : config.handler.input.representation.Holds input before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe config.handler.output.representation result).map Subtype.val) <$>
      (code config scale sub scaleBuffers subBuffers reserve).execute (Fresh.port (PrivateSampler.Enumerated.tape config.sampler)) .unit tape before =
        some <$> (Schnorr.ListROM.Shared.interpret
          (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (.inr input.val.1))).run input.val.2 := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  exact Handler.observe_original (G₂ := G₂) (K := K) config.handler trivial scale sub scaleBuffers subBuffers reserve
    (PrivateSampler.Enumerated.caller config.sampler) 1 (PrivateSampler.Enumerated.terminates config.sampler)
    (PrivateSampler.Enumerated.samples config.sampler (PrivateSampler.Service.unit (PrivateSampler.Enumerated.layout config.sampler))) tape input valid before holds

end Source
end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Enumerated
