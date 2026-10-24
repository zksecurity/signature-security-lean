import Proofs.Runtime.Caliper.SchnorrAGMSampling
import Proofs.Runtime.Caliper.InteractiveMemory

/-! Signing resources include both sampler bodies and calls, the retained
request/state, and the complete deterministic signing program. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampling
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [SMul F G] [Sub G] [Neg F]
    [DecidableEq M] [DecidableEq G] {spec : OracleSpec I}
    (layout : Histories.Layouts w M F G qH qS)

def timeBudget (scaleTime subTime negateTime sampleTime : Nat) : Nat :=
  Sampled.timeBudget layout scaleTime subTime negateTime + 2 * sampleTime +
    52 * layout.scheme.scalar.representation.encoding.words + 12 * (input layout).representation.encoding.words
def codeBudget (scaleWords subWords negateWords sampleWords : Nat) : Nat :=
  Sampled.codeBudget layout scaleWords subWords negateWords + 2 * sampleWords +
    169 * layout.scheme.scalar.representation.encoding.words + 39 * (input layout).representation.encoding.words + 128
def nameBudget (primitiveNames sampleSlots : Nat) : Nat := max 5 (max primitiveNames (PairSampling.slots sampleSlots sampleSlots))

omit [Zero F] [SMul F G] [Sub G] [Neg F] [DecidableEq M] [DecidableEq G] in
theorem sample_time (port : Interactive.Port w spec) {sampler : Interactive.Code w}
    {samplerSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => samplerSource) sampler) {sampleTime : Nat}
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit (input layout).representation (sample layout port sampler)
      (2 * sampleTime + 52 * layout.scheme.scalar.representation.encoding.words + 12 * (input layout).representation.encoding.words) := by
  have paired := PairSampling.refines (hw := layout.scheme.wordFits) (fits := pairFits layout) sampleCorrect sampleCorrect
  have timed := PairSampling.time_bound (hw := layout.scheme.wordFits) (fits := pairFits layout) sampleCorrect sampleCorrect sampleBound sampleBound
  have held := timed.retain paired (by decide) (input layout).representation layout.scheme.wordFits
    (by change 0 + _ < _; simpa using (input layout).representation.fits)
  have viewed := held.viewInput (input layout).representation (fun args => (⟨(), trivial⟩, args)) (fun _ => rfl)
  have bounded := viewed.mono (Interactive.retain_time_unit_le _ 0 _ _ _)
  apply bounded.mono
  change (sampleTime + sampleTime + 20 * _ + 16 * _) + 8 * 0 + 8 * (_ + _) + 12 * _ ≤ _
  omega

variable (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.signing.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.signing.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

theorem time_bound {sampler : Interactive.Code w} {samplerSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => samplerSource) sampler) {scaleTime scaleWords subTime subWords negateTime negateWords sampleTime : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit (input layout).representation
      (code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
      (timeBudget layout scaleTime subTime negateTime sampleTime) := by
  have computed := Sampled.bounded layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve scaleBound subBound negateBound
  have combined := (sample_time layout port sampleCorrect sampleBound).seq (sample_refines layout port sampleCorrect)
    (Interactive.TimeBound.compute (port := port) (cost := .unit)
      (Sampled.implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program _ computed.time_le)
  exact combined.mono (by unfold timeBudget; omega)

theorem code_bound (sampler : Interactive.Code w) {scaleTime scaleWords subTime subWords negateTime negateWords sampleWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords) (sampleBound : (sampler.lower port).descriptionWords ≤ sampleWords) :
    ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).descriptionWords ≤
      codeBudget layout scaleWords subWords negateWords sampleWords := by
  have paired := PairSampling.code_bound layout.scheme.scalar layout.scheme.scalar layout.scheme.wordFits (pairFits layout) port
    sampler sampler sampleBound sampleBound
  have held := Interactive.retain_descriptionWords_le port (pairs layout port sampler)
    (Interactive.savedBuffer port (pairs layout port sampler)) 0 layout.scheme.affine.representation.encoding.words (input layout).representation.encoding.words
  have computed := (Sampled.bounded layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve scaleBound subBound negateBound).code_le
  change ((pairs layout port sampler).lower port).descriptionWords ≤ _ at paired
  change ((sample layout port sampler).lower port).descriptionWords ≤ _ at held
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  dsimp only [codeBudget, PairSampling.codeBudget] at *
  rw [SchnorrAGM.Layouts.affine_words] at held
  omega

theorem names (sampler : Interactive.Code w) {primitiveNames sampleSlots : Nat}
    (scaleNames : NamesAccounted scale.program.code primitiveNames) (subNames : NamesAccounted sub.program.code primitiveNames)
    (negateNames : NamesAccounted negate.program.code primitiveNames)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port)
      (nameBudget primitiveNames sampleSlots) := by
  have paired := PairSampling.names layout.scheme.scalar layout.scheme.scalar layout.scheme.wordFits (pairFits layout) port
    sampler sampler sampleNames sampleNames
  have held := Interactive.retain_names port paired.accounted 0 layout.scheme.affine.representation.encoding.words (input layout).representation.encoding.words
  have computed := Sampled.names layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve scaleNames subNames negateNames
  have heldNames : WordIO.NamesAccounted ((sample layout port sampler).lower port) (nameBudget primitiveNames sampleSlots) :=
    held.mono (by unfold nameBudget; omega)
  exact heldNames.seq ((WordIO.NamesAccounted.compute computed).mono (by unfold nameBudget; omega))

theorem descriptionFits (sampler : Interactive.Code w) (sampleFits : (sampler.lower port).DescriptionFits)
    {sampleSlots : Nat} (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (sampleReserve : sampleSlots + 2 < 2 ^ w) :
    ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).DescriptionFits := by
  have paired := PairSampling.descriptionFits layout.scheme.scalar layout.scheme.scalar layout.scheme.wordFits (pairFits layout) port
    sampler sampler sampleFits sampleFits sampleNames (by omega)
  have named := PairSampling.names layout.scheme.scalar layout.scheme.scalar layout.scheme.wordFits (pairFits layout) port
    sampler sampler sampleNames sampleNames
  have nameFits : Interactive.savedBuffer port (pairs layout port sampler) < 2 ^ w := by
    have bound := named.buffers
    change ((pairs layout port sampler).lower port).memBound ≤ PairSampling.slots sampleSlots sampleSlots at bound
    have hw := layout.scheme.wordFits
    dsimp only [Interactive.savedBuffer, PairSampling.slots] at *
    omega
  have held := Interactive.retain_descriptionFits port (pairs layout port sampler)
    (Interactive.savedBuffer port (pairs layout port sampler)) 0 layout.scheme.affine.representation.encoding.words
    (input layout).representation.encoding.words layout.scheme.wordFits paired nameFits (by positivity)
    (input layout).representation.fits (frameFits layout)
  exact .seq layout.scheme.wordFits held
    (.compute (Sampled.implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.description_fits)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampling
