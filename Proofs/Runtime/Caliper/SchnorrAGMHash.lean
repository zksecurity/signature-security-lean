import Proofs.Runtime.Caliper.SchnorrAGMHashRouting

/-! Complete well-shaped Schnorr hash requests. The affine explanation is
computed before challenge sampling, with the complete original input physically
retained around flattening. The constructed read then updates the source state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Hash
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Mul F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

omit [DecidableEq F] [DecidableEq M] [DecidableEq G] in
theorem flatten_nameFits : (Flatten.implementation layout.flat zeroValid mul add mulBuffers addBuffers reserve).program.savedBuffer < 2 ^ w := by
  have bounded := Flatten.buffers layout.flat zeroValid mul add mulBuffers addBuffers reserve
  have hw := layout.scheme.wordFits
  change max 2 (Flatten.implementation layout.flat zeroValid mul add mulBuffers addBuffers reserve).program.code.memBound < _
  omega

def explanation (value : layout.input.Value) : layout.flat.affine.Value :=
  ⟨Flatten.denote (layout.flattenInput value).val,
    (Flatten.implementation layout.flat zeroValid mul add mulBuffers addBuffers reserve).preserves
      (layout.flattenInput value).val (layout.flattenInput value).property⟩

def holdFlatten : Realizer .unit layout.packed layout.flattened
    (fun value => (⟨Flatten.denote value.1.val,
      (Flatten.implementation layout.flat zeroValid mul add mulBuffers addBuffers reserve).preserves value.1.val value.1.property⟩, value.2)) :=
  (Flatten.implementation layout.flat zeroValid mul add mulBuffers addBuffers reserve).program.retain (by decide)
    layout.input.representation layout.scheme.wordFits (flatten_nameFits layout zeroValid mul add mulBuffers addBuffers reserve)
    layout.packed.fits layout.flattened.fits

def prepareValue (value : layout.input.Value) : (Read.input layout.scheme).Value :=
  layout.readValue (explanation layout zeroValid mul add mulBuffers addBuffers reserve value, value)

def prepare : Realizer .unit layout.input.representation (Read.input layout.scheme).representation
    (prepareValue layout zeroValid mul add mulBuffers addBuffers reserve) :=
  (((pack layout).then (holdFlatten layout zeroValid mul add mulBuffers addBuffers reserve)).then (finish layout)).viewOutput _
    (prepareValue layout zeroValid mul add mulBuffers addBuffers reserve) (fun _ => rfl)

variable (port : Interactive.Port w spec)

def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (prepare layout zeroValid mul add mulBuffers addBuffers reserve).code)
    (Read.code layout.scheme zeroValid add addBuffers (by omega) port sampler)

def source (sampler : OracleComp spec layout.scheme.scalar.Value) (value : layout.input.Value) :
    OracleComp spec (Read.output layout.scheme).Value :=
  Read.source layout.scheme zeroValid sampler (prepareValue layout zeroValid mul add mulBuffers addBuffers reserve value)

theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.input.representation (Read.output layout.scheme).representation
      (source layout zeroValid mul add mulBuffers addBuffers reserve sampleSource)
      (code layout zeroValid mul add mulBuffers addBuffers reserve port sampler) := by
  have compiled := (Interactive.Refines.compute port .unit (prepare layout zeroValid mul add mulBuffers addBuffers reserve)).seq
    (Read.refines layout.scheme zeroValid add addBuffers (by omega) port sampleCorrect)
  convert compiled using 1
  · funext value
    simp only [pure_bind, source]
  · rfl

section Original
variable {w qH qS : Nat} {M F G : Type} [Field F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)
open Signatures.Runtime.SchnorrAGM.Native

theorem source_original [SampleableType F] (sampler : ProbComp layout.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (key : M × G) (coefficients : List F)
    (valid : layout.input.valid (key, coefficients, encodeState state)) :
    Subtype.val <$> source layout zeroValid mul add mulBuffers addBuffers reserve sampler ⟨(key, coefficients, encodeState state), valid⟩ =
      (fun result => (result.1, encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.read key (Schnorr.AGM.flatten coefficients state.representations)).run state := by
  let ready := prepareValue layout zeroValid mul add mulBuffers addBuffers reserve ⟨(key, coefficients, encodeState state), valid⟩
  have value : ready.val = (key, encodeAffine (Schnorr.AGM.flatten coefficients state.representations), encodeState state) := by
    change (key, Flatten.denote (state.representations.map encodeAffine, coefficients), encodeState state) = _
    rw [Flatten.denote_source]
  have admitted : (Read.input layout.scheme).valid (key, encodeAffine (Schnorr.AGM.flatten coefficients state.representations), encodeState state) := by
    rw [← value]
    exact ready.property
  have same : ready = ⟨(key, encodeAffine (Schnorr.AGM.flatten coefficients state.representations), encodeState state), admitted⟩ :=
    Subtype.ext value
  change Subtype.val <$> Read.source layout.scheme zeroValid sampler ready = _
  rw [same]
  exact Read.source_original layout.scheme zeroValid sampler uniform state key _ admitted

omit [DecidableEq F] in
theorem input_valid (scalars : ∀ value, layout.scheme.scalar.valid value) (points : ∀ value, layout.scheme.point.valid value)
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (key : M × G) (coefficients : List F)
    (keyValid : layout.scheme.message.valid key.1) (coefficientLength : coefficients.length ≤ layout.coefficients)
    (stateValid : layout.scheme.state.valid (encodeState state)) (spare : state.cache.length ≤ qH + qS) :
    layout.input.valid (key, coefficients, encodeState state) := by
  refine ⟨⟨⟨keyValid, points _⟩, ⟨coefficientLength, fun value _ => scalars value⟩, stateValid⟩, ?_⟩
  intro _
  change (state.cache.map (Prod.map id encodeEntry)).length ≤ qH + qS
  simpa only [List.length_map] using spare

omit [DecidableEq F] in
theorem reserved_input (scalars : ∀ value, layout.scheme.scalar.valid value) (points : ∀ value, layout.scheme.point.valid value)
    {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.scheme.Reserved hashes signatures state) (key : M × G) (coefficients : List F)
    (keyValid : layout.scheme.message.valid key.1) (coefficientLength : coefficients.length ≤ layout.coefficients) :
    layout.input.valid (key, coefficients, encodeState state) :=
  input_valid layout scalars points state key coefficients keyValid coefficientLength (room.encoded layout.scheme scalars points)
    (by have := room.2.1; omega)

end Original

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Hash
