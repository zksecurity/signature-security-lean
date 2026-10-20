import Signatures.Runtime.Caliper.SchnorrROMHandlerLayout

/-! The complete three-way ROM service is constructed from the verified
handlers. Only scalar multiplication and group subtraction are supplied as
local routines; sampling, replay, dispatch and copying are constructed here. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

structure Operations where
  scale : Implementation .unit config.handler.core.arithmetic.scaleArgs config.handler.core.point (fun value => value.1 • value.2)
  sub : Implementation .unit config.handler.core.arithmetic.points config.handler.core.point (fun value => value.1 - value.2)
  slots : Nat
  scaleNames : NamesBound scale.program.code slots
  subNames : NamesBound sub.program.code slots
  reserve : slots + 3 < 2 ^ w

variable (ops : Operations config)
def signCode := Signing.Enumerated.code config ops.scale ops.sub ops.scaleNames.buffers ops.subNames.buffers ops.reserve
def signSource := Signing.Enumerated.source config ops.scale ops.sub ops.scaleNames.buffers ops.subNames.buffers ops.reserve
theorem sign_refines : Interactive.RefinesOn (Signing.Handler.ready config.handler 1)
    (Fresh.port config.handler.sampler.tape) .unit config.handler.input.representation config.handler.output.representation
    (signSource config ops) (signCode config ops) :=
  Signing.Handler.refines config.handler trivial ops.scale ops.sub ops.scaleNames.buffers ops.subNames.buffers ops.reserve
    (PrivateSampler.Enumerated.caller config.sampler) 1

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
theorem signing_refines : Interactive.RefinesOn (Signing.Handler.ready config.handler 1)
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
