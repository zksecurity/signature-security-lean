import Signatures.Runtime.Caliper.SchnorrAGMFlattenSetup

/-! Executed affine flattening over the bounded chronological basis. Positional
attachment is implemented before the scalar fold; neither a completed flattening
routine nor its source equivalence is assumed as an arithmetic primitive. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Flatten
open Caliper BoundedSource
variable {w : Nat} {F : Type} [Zero F] [Mul F] [Add F]
    (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)
    (mul : Implementation .unit layout.affine layout.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

omit [Zero F] in
theorem body_nameFits : (body layout mul add mulBuffers addBuffers reserve).program.savedBuffer < 2 ^ w := by
  have bound := body_buffers layout mul add mulBuffers addBuffers reserve
  have hw := layout.wordFits
  change max 2 (body layout mul add mulBuffers addBuffers reserve).program.code.memBound < _
  omega

def fold : Implementation .unit layout.frame layout.affine (FoldImplementation.sourceFold step) :=
  FoldImplementation.compile layout.attach.row layout.affine layout.unit layout.argFits
    (body layout mul add mulBuffers addBuffers reserve) (by decide) layout.wordFits
    (body_nameFits layout mul add mulBuffers addBuffers reserve) layout.capacity layout.attach.countFits layout.foldFits

def denote (value : List (F × F) × List F) : F × F :=
  (value.1.mapIdx fun n pair => (pair, (value.2[n]?).getD 0)).foldl
    (fun accumulator row => (accumulator.1 + row.2 * row.1.1, accumulator.2 + row.2 * row.1.2)) (0, 0)

def implementation : Implementation .unit layout.input layout.affine denote :=
  ((((prepare layout zeroValid).then (AttachRows.implementation layout.attach)).then
    (initial layout zeroValid)).then (fold layout mul add mulBuffers addBuffers reserve)).castFunction (by
      funext value
      rfl)

theorem buffers : (implementation layout zeroValid mul add mulBuffers addBuffers reserve).program.code.memBound ≤
    max 10 (max 3 slots + 3) := by
  have prepared := (Assembly.code_names _ 1 (prepareOperands_sources layout zeroValid)).2
  have attached := AttachRows.buffers layout.attach
  have initialized := (Assembly.code_names _ 1 (initialOperands_sources layout zeroValid)).2
  have folded := ListFold.buffers (body layout mul add mulBuffers addBuffers reserve).program.code
    layout.attach.row.representation.encoding.words layout.affine.representation.encoding.words
    layout.unit.representation.encoding.words layout.capacity
  have stepped := body_buffers layout mul add mulBuffers addBuffers reserve
  change (prepare layout zeroValid).program.code.memBound ≤ 2 at prepared
  change (initial layout zeroValid).program.code.memBound ≤ 2 at initialized
  change (fold layout mul add mulBuffers addBuffers reserve).program.code.memBound ≤ _ at folded
  change max (max (max _ _) _) _ ≤ _
  omega

theorem names (names : Nat) (mulNames : NamesAccounted mul.program.code names) (addNames : NamesAccounted add.program.code names) :
    NamesAccounted (implementation layout zeroValid mul add mulBuffers addBuffers reserve).program.code names :=
  (((Assembly.code_namesAccounted _ _ (prepareOperands_sources layout zeroValid)).seq (AttachRows.names layout.attach names)).seq
    (Assembly.code_namesAccounted _ _ (initialOperands_sources layout zeroValid))).seq
      (FoldImplementation.compile_names layout.attach.row layout.affine layout.unit layout.argFits
        (body layout mul add mulBuffers addBuffers reserve) layout.wordFits (body_nameFits layout mul add mulBuffers addBuffers reserve)
        layout.capacity layout.attach.countFits layout.foldFits
        (body_names layout mul add mulBuffers addBuffers reserve names mulNames addNames))

section Source
variable {F : Type} [Semiring F]

theorem fold_total (rows : List ((F × F) × F)) (accumulator : F × F) :
    rows.foldl (fun acc row => (acc.1 + row.2 * row.1.1, acc.2 + row.2 * row.1.2)) accumulator =
      (accumulator.1 + (Signatures.Runtime.SchnorrAGM.Native.Flatten.total rows).1,
        accumulator.2 + (Signatures.Runtime.SchnorrAGM.Native.Flatten.total rows).2) := by
  induction rows generalizing accumulator with
  | nil => simp [Signatures.Runtime.SchnorrAGM.Native.Flatten.total]
  | cons row rows ih => simp [ih, Signatures.Runtime.SchnorrAGM.Native.Flatten.total, add_assoc]

theorem denote_value (basis : List (F × F)) (coefficients : List F) :
    denote (basis, coefficients) = Signatures.Runtime.SchnorrAGM.Native.Flatten.value basis coefficients := by
  unfold denote
  rw [fold_total]
  simp only [zero_add]
  rfl
end Source

section Original
variable {F : Type} [Field F]

theorem denote_source (basis : List (Schnorr.AGM.Affine F)) (coefficients : List F) :
    denote (basis.map Signatures.Runtime.SchnorrAGM.Native.encodeAffine, coefficients) =
      Signatures.Runtime.SchnorrAGM.Native.encodeAffine (Schnorr.AGM.flatten coefficients basis) := by
  rw [denote_value, Signatures.Runtime.SchnorrAGM.Native.Flatten.value_source]
end Original

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Flatten
