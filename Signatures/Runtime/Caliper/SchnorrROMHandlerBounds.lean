import Signatures.Runtime.Caliper.SchnorrROMHandlerSource

/-! Complete service bounds charge the selected execution, every stored branch,
and both tag levels and their copied payloads. Local group costs remain explicit. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Operations config)

structure Budget where
  scaleTime : Nat
  scaleWords : Nat
  subTime : Nat
  subWords : Nat
  scale : ops.scale.BoundedBy scaleTime scaleWords
  sub : ops.sub.BoundedBy subTime subWords

variable (budget : Budget config ops)
def signingTime := Signing.Handler.timeBudget config.handler trivial 38 16 1 budget.scaleTime budget.subTime
def signingWords := Signing.Handler.codeBudget config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1
  budget.scaleWords budget.subWords
def timeBudget := max (max (Random.timeBudget config) (Hash.timeBudget config)) (signingTime config ops budget) +
  200 * config.handler.width + 10
def codeBudget := Random.codeBudget config + Hash.codeBudget config + signingWords config ops budget +
  1400 * config.handler.width + 200

omit [SMul F G] [Sub G] [Zero F] [DecidableEq M] [DecidableEq G] in
theorem randomTag_time (value) : (randomTag config).time value ≤
    8 * (innerOutput config).encoding.words + 8 * (output config).encoding.words :=
  Nat.add_le_add
    (inl_time (Random.output config).representation (Hash.output config).representation config.sampler.wordFits (innerOutput config).fits value)
    (inl_time (innerOutput config) config.handler.output.representation config.sampler.wordFits (output config).fits (.inl value))
omit [SMul F G] [Sub G] [Zero F] [DecidableEq M] [DecidableEq G] in
theorem hashTag_time (value) : (hashTag config).time value ≤
    8 * (innerOutput config).encoding.words + 8 * (output config).encoding.words :=
  Nat.add_le_add
    (inr_time (Random.output config).representation (Hash.output config).representation config.sampler.wordFits (innerOutput config).fits value)
    (inl_time (innerOutput config) config.handler.output.representation config.sampler.wordFits (output config).fits (.inr value))
omit [SMul F G] [Sub G] [Zero F] [DecidableEq M] [DecidableEq G] in
theorem signingTag_time (value) : (signingTag config).time value ≤ 8 * (output config).encoding.words :=
  inr_time _ _ _ _ value

theorem time_bound : Interactive.TimeBoundOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config) (code config ops) (timeBudget config ops budget) := by
  have random := (Random.time_bound config).seq (Random.refines config)
    (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (randomTag config) _ (randomTag_time config))
  have hashed := Interactive.TimeBoundOn.seq (Hash.refines config) (Hash.time_bound config)
    ((Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (hashTag config) _ (hashTag_time config)).on (fun _ => True)) (by intros; trivial)
  have signed := Interactive.TimeBoundOn.seq (sign_refines config ops)
    (Signing.Enumerated.time_bound config ops.scale ops.sub ops.scaleNames.buffers ops.subNames.buffers ops.reserve
      budget.scale budget.sub)
    ((Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (signingTag config) _ (signingTag_time config)).on (fun _ => True)) (by intros; trivial)
  have inner := Interactive.TimeBoundOn.dispatch _ _ (random.on (fun _ => True)) hashed
    (width_pos config.sampler.wordFits) (innerInput config).fits
  have combined := Interactive.TimeBoundOn.dispatch _ _ inner signed
    (width_pos config.sampler.wordFits) (input config).fits
  apply combined.mono
  simp only [Interactive.dispatchTime_unit]
  have := input_widths config; have := packet_widths config
  change 2 + max (8 * _ + (2 + max _ _)) (8 * _ + (_ + 8 * (output config).encoding.words)) ≤ _
  unfold timeBudget signingTime
  dsimp only [innerInput] at *
  omega

omit [SMul F G] [Sub G] [Zero F] [DecidableEq M] [DecidableEq G] in
theorem randomTag_words : descriptionWords (randomTag config).code ≤
    26 * (innerOutput config).encoding.words + 26 * (output config).encoding.words + 29 := by
  have first := inl_words (Random.output config).representation (Hash.output config).representation
    config.sampler.wordFits (innerOutput config).fits
  have second := inl_words (innerOutput config) config.handler.output.representation config.sampler.wordFits (output config).fits
  change descriptionWords _ ≤ 26 * (innerOutput config).encoding.words + 14 at first
  change descriptionWords _ ≤ 26 * (output config).encoding.words + 14 at second
  change descriptionWords (_ ;; _) ≤ _
  rw [descriptionWords_seq]
  omega
omit [SMul F G] [Sub G] [Zero F] [DecidableEq M] [DecidableEq G] in
theorem hashTag_words : descriptionWords (hashTag config).code ≤
    26 * (innerOutput config).encoding.words + 26 * (output config).encoding.words + 29 := by
  have first := inr_words (Random.output config).representation (Hash.output config).representation
    config.sampler.wordFits (innerOutput config).fits
  have second := inl_words (innerOutput config) config.handler.output.representation config.sampler.wordFits (output config).fits
  change descriptionWords _ ≤ 26 * (innerOutput config).encoding.words + 14 at first
  change descriptionWords _ ≤ 26 * (output config).encoding.words + 14 at second
  change descriptionWords (_ ;; _) ≤ _
  rw [descriptionWords_seq]
  omega
omit [SMul F G] [Sub G] [Zero F] [DecidableEq M] [DecidableEq G] in
theorem signingTag_words : descriptionWords (signingTag config).code ≤ 26 * (output config).encoding.words + 14 :=
  inr_words _ _ _ _

theorem code_bound : ((code config ops).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    codeBudget config ops budget := by
  have random := Random.code_bound config
  have hashed := Hash.code_bound config
  have signed := Signing.Enumerated.code_bound config ops.scale ops.sub ops.scaleNames.buffers ops.subNames.buffers
    ops.reserve budget.scale budget.sub
  change ((signCode config ops).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    signingWords config ops budget at signed
  have rt := randomTag_words config; have ht := hashTag_words config; have st := signingTag_words config
  rw [code, Interactive.dispatch_descriptionWords, innerCode, Interactive.dispatch_descriptionWords]
  simp only [randomCode, hashCode, signingCode, Interactive.Code.lower,
    WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  have := input_widths config; have := packet_widths config
  unfold codeBudget
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
