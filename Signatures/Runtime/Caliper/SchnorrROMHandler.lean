import Signatures.Runtime.Caliper.SchnorrROMHandlerLayout
import Signatures.Runtime.Caliper.SchnorrROMPrivateGrowth

/-! The complete three-way ROM service is constructed from the verified
handlers. Only scalar multiplication and group subtraction are supplied as
local routines; sampling, replay, dispatch and copying are constructed here. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

/-- An executed signing branch: code over the signing packet, its source, their
refinement, resource bounds and the store postconditions the service invariant
needs. The full-field and nonzero-nonce simulators are instances; its source law
to a list-backend handler is stated separately (`SigningLaw`). -/
structure SigningBranch (slots : Nat) where
  code : Interactive.Code w
  source : config.handler.input.Value → ProbComp config.handler.output.Value
  refines : Interactive.RefinesOn (signingReady config) (Fresh.port config.handler.sampler.tape) .unit
    config.handler.input.representation config.handler.output.representation source code
  time : Nat
  words : Nat
  nameSlots : Nat
  time_bound : Interactive.TimeBoundOn (signingReady config) (Fresh.port config.handler.sampler.tape) .unit
    config.handler.input.representation code time
  code_bound : (code.lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ words
  names : WordIO.NamesAccounted (code.lower (Fresh.port config.handler.sampler.tape)) nameSlots
  buffers : (code.lower (Fresh.port config.handler.sampler.tape)).memBound ≤ max 11 (slots + 3)
  descriptionFits : (code.lower (Fresh.port config.handler.sampler.tape)).DescriptionFits
  preserves_config : ∀ value answer, answer ∈ support (source value) → answer.val.2.1.1 = value.val.2.1.1
  preserves_live : ∀ value answer, answer ∈ support (source value) → answer.val.2.1.2.2 = value.val.2.1.2.2
  managed_length : ∀ value answer, answer ∈ support (source value) → answer.val.2.1.2.1.length ≤ value.val.2.1.2.1.length + 1
  tape_lengths : ∀ value, signingReady config value → ∀ answer, answer ∈ support (source value) →
    answer.val.2.2.1.length ≤ value.val.2.2.1.length + 3 ∧ answer.val.2.2.2.length ≤ value.val.2.2.2.length

structure Operations where
  scale : Implementation .unit config.handler.core.arithmetic.scaleArgs config.handler.core.point (fun value => value.1 • value.2)
  sub : Implementation .unit config.handler.core.arithmetic.points config.handler.core.point (fun value => value.1 - value.2)
  slots : Nat
  scaleNames : NamesBound scale.program.code slots
  subNames : NamesBound sub.program.code slots
  reserve : slots + 3 < 2 ^ w
  signing : SigningBranch config slots

/-- The full-field signing branch: two private tape draws through the enumerated
sampler, then the executed commitment and cache programming. -/
def fullField (scale : Implementation .unit config.handler.core.arithmetic.scaleArgs config.handler.core.point (fun value => value.1 • value.2))
    (sub : Implementation .unit config.handler.core.arithmetic.points config.handler.core.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleNames : NamesBound scale.program.code slots) (subNames : NamesBound sub.program.code slots)
    (reserve : slots + 3 < 2 ^ w) {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords) : SigningBranch config slots where
  code := Signing.Enumerated.code config scale sub scaleNames.buffers subNames.buffers reserve
  source := Signing.Enumerated.source config scale sub scaleNames.buffers subNames.buffers reserve
  refines := fun tape value valid before holds =>
    Signing.Handler.refines config.handler trivial scale sub scaleNames.buffers subNames.buffers reserve
      (PrivateSampler.Enumerated.caller config.sampler) 1 tape value (signingReady_pair config value valid) before holds
  time := Signing.Handler.timeBudget config.handler trivial 38 16 1 scaleTime subTime
  words := Signing.Handler.codeBudget config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1 scaleWords subWords
  nameSlots := Signing.Handler.nameBudget config.handler trivial 3 slots
  time_bound := fun tape value valid before holds =>
    Signing.Enumerated.time_bound config scale sub scaleNames.buffers subNames.buffers reserve scaleBound subBound
      tape value (signingReady_pair config value valid) before holds
  code_bound := Signing.Enumerated.code_bound config scale sub scaleNames.buffers subNames.buffers reserve scaleBound subBound
  names := Signing.Enumerated.names config scale sub scaleNames.buffers subNames.buffers reserve slots
    scaleNames.accounted subNames.accounted
  buffers := Signing.Enumerated.buffers config scale sub scaleNames.buffers subNames.buffers reserve
  descriptionFits := Signing.Enumerated.descriptionFits config scale sub scaleNames.buffers subNames.buffers reserve
  preserves_config := by
    intro value answer reached
    simp only [Signing.Enumerated.source, Signing.Handler.source, support_map, Set.mem_image] at reached
    obtain ⟨sampled, _, rfl⟩ := reached
    rfl
  preserves_live := fun value answer reached => Signing.Handler.preserves_live config.handler trivial scale sub
    scaleNames.buffers subNames.buffers reserve (PrivateSampler.Enumerated.caller config.sampler) 1 value answer reached
  managed_length := fun value answer reached => Signing.Handler.managed_length config.handler trivial scale sub
    scaleNames.buffers subNames.buffers reserve (PrivateSampler.Enumerated.caller config.sampler) 1 value answer reached
  tape_lengths := by
    intro value valid answer reached
    simp only [Signing.Enumerated.source, Signing.Handler.source, support_map, Set.mem_image] at reached
    obtain ⟨sampled, supported, rfl⟩ := reached
    have grown := PrivateSampler.Pair.tape_lengths config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler)
      trivial 1 (Signing.Handler.tapes config.handler value) (signingReady_pair config value valid) sampled supported
    change sampled.val.2.2.1.length ≤ value.val.2.2.1.length + 3 ∧ sampled.val.2.2.2.length ≤ value.val.2.2.2.length
    change sampled.val.2.2.1.length ≤ value.val.2.2.1.length + 2 ∧ sampled.val.2.2.2.length ≤ value.val.2.2.2.length at grown
    exact ⟨grown.1.trans (by omega), grown.2⟩

variable (ops : Operations config)
def signCode := ops.signing.code
def signSource := ops.signing.source
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem sign_refines : Interactive.RefinesOn (signingReady config)
    (Fresh.port config.handler.sampler.tape) .unit config.handler.input.representation config.handler.output.representation
    (signSource config ops) (signCode config ops) :=
  ops.signing.refines

omit [SMul F G] [Sub G] in
def randomCode : Interactive.Code w := .seq (Random.code config) (.compute (randomTag config).code)
omit [SMul F G] [Sub G] in
def hashCode : Interactive.Code w := .seq (Hash.code config) (.compute (hashTag config).code)
def signingCode : Interactive.Code w := .seq (signCode config ops) (.compute (signingTag config).code)
omit [SMul F G] [Sub G] in
def innerCode : Interactive.Code w := Interactive.dispatch (randomCode config) (hashCode config)
  (Random.input config).representation.encoding.words (Hash.input config).representation.encoding.words
def code : Interactive.Code w := Interactive.dispatch (innerCode config) (signingCode config ops)
  (innerInput config).encoding.words config.handler.input.representation.encoding.words

omit [SMul F G] [Sub G] in
def randomSource (value : (Random.input config).Value) : ProbComp (Output config) :=
  (fun answer => .inl (.inl answer)) <$> Random.source config value
omit [SMul F G] [Sub G] in
def hashSource (value : (Hash.input config).Value) : ProbComp (Output config) :=
  (fun answer => .inl (.inr answer)) <$> Hash.source config value
def signingSource (value : config.handler.input.Value) : ProbComp (Output config) :=
  Sum.inr <$> signSource config ops value
def source : Input config → ProbComp (Output config) :=
  Sum.elim (Sum.elim (randomSource config) (hashSource config)) (signingSource config ops)

omit [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] in
theorem random_refines : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (Random.input config).representation (output config) (randomSource config) (randomCode config) := by
  have combined := (Random.refines config).seq (Interactive.Refines.compute _ .unit (randomTag config))
  convert combined using 1
  · funext value
    simp only [bind_pure_comp]
    rfl
  · rfl
omit [SMul F G] [Sub G] in
theorem hash_refines : Interactive.RefinesOn (Hash.ready config) (Fresh.port config.handler.sampler.tape) .unit
    (Hash.input config).representation (output config) (hashSource config) (hashCode config) := by
  have combined := (Hash.refines config).seq
    ((Interactive.Refines.compute _ .unit (hashTag config)).on (fun _ => True)) (by intros; trivial)
  convert combined using 1
  · funext value
    simp only [bind_pure_comp]
    rfl
  · rfl
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem signing_refines : Interactive.RefinesOn (signingReady config)
    (Fresh.port config.handler.sampler.tape) .unit config.handler.input.representation (output config)
    (signingSource config ops) (signingCode config ops) := by
  have combined := (sign_refines config ops).seq
    ((Interactive.Refines.compute _ .unit (signingTag config)).on (fun _ => True)) (by intros; trivial)
  convert combined using 1
  · funext value
    simp only [bind_pure_comp]
    rfl
  · rfl
theorem refines : Interactive.RefinesOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config) (output config) (source config ops) (code config ops) :=
  Interactive.RefinesOn.dispatch _ _ _
    (Interactive.RefinesOn.dispatch _ _ _ ((random_refines config).on (fun _ => True)) (hash_refines config)
      (width_pos config.sampler.wordFits) (innerInput config).fits)
    (signing_refines config ops) (width_pos config.sampler.wordFits) (input config).fits

end Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
