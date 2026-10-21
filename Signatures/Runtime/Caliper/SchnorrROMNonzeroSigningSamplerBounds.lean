import Signatures.Runtime.Caliper.SchnorrROMNonzeroSigningSampler

/-! Constant local costs of the executed map past zero, of the replayed nonzero
caller and of the direct nonzero draw. None depends on the field size: the zero
index and the range are immediates, not tables. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated.Nonzero
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (params : Parameters w F) (positive : 0 < params.bound)

omit [Zero F] in
theorem wordBinary_time (op : BinOp) (value : Word w × Word w) :
    (WordBinary.realizer (w := w) .unit op params.wordFits).time value ≤ 6 := by
  change Caliper.CostModel.unit.memLoad + (Caliper.CostModel.unit.imm + Caliper.CostModel.unit.memLoad) +
    (Caliper.CostModel.unit.bin op + (Caliper.CostModel.unit.memStore + Caliper.CostModel.unit.memPop)) ≤ 6
  cases op <;> decide

theorem wordBinary_names (op : BinOp) (slots : Nat) : NamesAccounted (WordBinary.code (w := w) op) slots := by
  have registers : registerSlots (WordBinary.code (w := w) op) ≤ 3 := by
    cases op <;> simp [WordBinary.code, WordBinary.load, WordBinary.finish, registerSlots]
  have buffers : (WordBinary.code (w := w) op).memBound ≤ 1 := by
    cases op <;> simp [WordBinary.code, WordBinary.load, WordBinary.finish, Stmt.memBound]
  have words : descriptionWords (WordBinary.code (w := w) op) = 27 := WordBinary.descriptionWords_eq op
  constructor <;> omega

omit [Zero F] in
theorem two_operand_time (operands : List (Assembly.Operand w)) (length : operands.length = 2) :
    (Assembly.code operands).staticTime .unit ≤ 16 := by
  have := Assembly.code_time_unit_le operands; omega

omit [Zero F] in
theorem two_operand_words (operands : List (Assembly.Operand w)) (length : operands.length = 2) :
    descriptionWords (Assembly.code operands) ≤ 66 := by
  have := Assembly.code_descriptionWords_le operands; omega

theorem compare_time (value : Word w) : (compare params).time value ≤ 22 := by
  have args := two_operand_time (w := w) [.literal (BitVec.ofNat w (zeroIndex params).val), .read 0 0] rfl
  change (compareArgs params).time value ≤ 16 at args
  exact Nat.add_le_add args (wordBinary_time params .ule _)

theorem compare_words : descriptionWords (compare params).code ≤ 94 := by
  have args := two_operand_words (w := w) [.literal (BitVec.ofNat w (zeroIndex params).val), .read 0 0] rfl
  change descriptionWords ((compareArgs params).code ;; WordBinary.code .ule) ≤ 94
  rw [descriptionWords_seq, WordBinary.descriptionWords_eq]
  change descriptionWords (compareArgs params).code ≤ 66 at args
  omega

theorem compare_names (slots : Nat) : NamesAccounted (compare params).code slots :=
  (Assembly.code_namesAccounted _ slots (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).seq
    (wordBinary_names .ule slots)

theorem flagged_time (value : Word w) : (flagged params).time value ≤ 126 := by
  have paired := Pairing.time_unit_le (Realizer.identity (width_pos params.wordFits) (word params)) (compare params) params.wordFits
    (identity_nameFits params) (compare_nameFits params) (pairFits params) (pairFits params) (pairFits params) value
  have compared := compare_time params value
  change (flagged params).time value ≤ 0 + (compare params).time value + 52 * 1 + 36 * 1 + 16 * 1 at paired
  omega

theorem flagged_words : descriptionWords (flagged params).code ≤ 557 := by
  have paired := Pairing.descriptionWords_le (Realizer.identity (width_pos params.wordFits) (word params)) (compare params) (by decide)
    params.wordFits (identity_nameFits params) (compare_nameFits params) (pairFits params) (pairFits params) (pairFits params)
  have compared := compare_words params
  change descriptionWords (flagged params).code ≤ descriptionWords (Stmt.skip : Stmt w) + descriptionWords (compare params).code +
    169 * 1 + 117 * 1 + 52 * 1 + 124 at paired
  have skipWords : descriptionWords (Stmt.skip : Stmt w) = 1 := rfl
  omega

theorem flagged_names (slots : Nat) : NamesAccounted (flagged params).code slots :=
  Pairing.names (Realizer.identity (width_pos params.wordFits) (word params)) (compare params) (by decide)
    params.wordFits (identity_nameFits params) (compare_nameFits params) (pairFits params) (pairFits params) (pairFits params)
    (_root_.Signatures.Runtime.CaliperBackend.skip_names slots) (compare_names params slots)

theorem skip_time (value : Word w) : (skipRealizer params positive).time value ≤ 154 := by
  have args := two_operand_time (w := w) [.read 0 0, .literal (BitVec.ofNat w params.bound)] rfl
  change (reduceArgs params).time value ≤ 16 at args
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add args (wordBinary_time params .umod _))
    (flagged_time params _)) (wordBinary_time params .add _)

theorem skip_words : descriptionWords (skipRealizer params positive).code ≤ 680 := by
  have args := two_operand_words (w := w) [.read 0 0, .literal (BitVec.ofNat w params.bound)] rfl
  have flaggedWords := flagged_words params
  change descriptionWords ((((reduceArgs params).code ;; WordBinary.code .umod) ;; (flagged params).code) ;;
    WordBinary.code .add) ≤ 680
  rw [descriptionWords_seq, descriptionWords_seq, descriptionWords_seq, WordBinary.descriptionWords_eq,
    WordBinary.descriptionWords_eq]
  change descriptionWords (reduceArgs params).code ≤ 66 at args
  omega

theorem skipRealizer_names (slots : Nat) : NamesAccounted (skipRealizer params positive).code slots :=
  (((Assembly.code_namesAccounted _ slots (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).seq
    (wordBinary_names .umod slots)).seq (flagged_names params slots)).seq (wordBinary_names .add slots)

/-! ### Replayed caller costs -/

omit [Zero F] in
theorem initial_time (input : (tape params).unit.Value) : (initialCode params).time input ≤ 16 :=
  two_operand_time _ rfl
omit [Zero F] in
theorem initial_words : descriptionWords (initialCode params).code ≤ 66 := two_operand_words _ rfl

theorem continuation_time (input : Unit × Response (layout params)) : (continuation params positive).time input ≤ 186 := by
  have picked := Assembly.code_time_unit_le (w := w) [.read 0 1]
  have skipped := skip_time params positive (BitVec.ofNat w input.2.val.2)
  have tagged := Assembly.code_time_unit_le (w := w) (Construction.taggedOperands 0 1 0)
  change (reply params).time input ≤ 8 * 1 at picked
  change (Assembly.code (Construction.taggedOperands (w := w) 0 1 0)).staticTime .unit ≤ 8 * 2 at tagged
  exact le_trans (Nat.add_le_add (Nat.add_le_add picked (skip_time params positive _)) tagged) (by norm_num)

theorem continuation_words : descriptionWords (continuation params positive).code ≤ 788 := by
  have picked := Assembly.code_descriptionWords_le (w := w) [.read 0 1]
  have skipped := skip_words params positive
  have tagged := Assembly.code_descriptionWords_le (w := w) (Construction.taggedOperands 0 1 0)
  change descriptionWords (reply params).code ≤ 26 * 1 + 14 at picked
  change descriptionWords (Assembly.code (Construction.taggedOperands (w := w) 0 1 0)) ≤ 26 * 2 + 14 at tagged
  change descriptionWords (((reply params).code ;; (skipRealizer params positive).code) ;;
    Assembly.code (Construction.taggedOperands 0 1 0)) ≤ 788
  rw [descriptionWords_seq, descriptionWords_seq]
  omega

omit [Zero F] in
theorem initial_names : NamesAccounted (initialCode params).code 3 :=
  Assembly.code_namesAccounted _ 3 (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])

theorem continuation_names : NamesAccounted (continuation params positive).code 3 := by
  have tagged : NamesAccounted (Assembly.code (w := w) (Construction.taggedOperands 0 1 0)) 3 :=
    Assembly.code_namesAccounted _ 3 (by
      simp [Construction.taggedOperands, Assembly.SourcesBound, Assembly.Operand.SourcesBound, Assembly.reads])
  exact ((Assembly.code_namesAccounted _ 3 (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).seq
    (skipRealizer_names params positive 3)).seq tagged

omit [Zero F] in
theorem initial_headroom : (initialCode params).code.memBound + 2 < 2 ^ w := by
  have := initial_buffers params; have := params.wordFits
  omega
theorem continuation_headroom : (continuation params positive).code.memBound + 2 < 2 ^ w := by
  have := continuation_buffers params positive; have := params.wordFits
  omega

/-! ### Direct draw costs -/

namespace Direct

theorem finish_time (value) : (finish params positive).time value ≤ 154 :=
  skip_time params positive _

theorem time_bound : Interactive.TimeBound (Fresh.port (tape params)) .unit
    (tape params).unit.representation (code params positive) 180 := by
  have drawn := UniformSampling.time_bound Fresh.randomBound params.wordFits Fresh.randomFits (Direct.request params)
  have last := Interactive.TimeBound.compute (port := UniformQuery.port Fresh.randomBound params.wordFits Fresh.randomFits)
    (cost := .unit) (finish params positive) 154 (finish_time params positive)
  exact drawn.seq (UniformSampling.refines Fresh.randomBound params.wordFits Fresh.randomFits (Direct.request params)) last

theorem code_words : ((code params positive).lower (Fresh.port (tape params))).descriptionWords ≤ 807 := by
  have drawn := UniformSampling.code_words Fresh.randomBound params.wordFits Fresh.randomFits (Direct.request params)
  have last : descriptionWords (finish params positive).code ≤ 680 := skip_words params positive
  change ((Direct.draw params).lower (Fresh.port (tape params))).descriptionWords ≤ 125 at drawn
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

theorem names : WordIO.NamesAccounted ((code params positive).lower (Fresh.port (tape params))) 3 :=
  (UniformSampling.names Fresh.randomBound params.wordFits Fresh.randomFits (Direct.request params)).accounted.seq
    (WordIO.NamesAccounted.compute (skipRealizer_names params positive 3))

theorem buffers : ((code params positive).lower (Fresh.port (tape params))).memBound ≤ 3 := by
  have drawn := (UniformSampling.names Fresh.randomBound params.wordFits Fresh.randomFits (Direct.request params)).buffers
  have last : (finish params positive).code.memBound ≤ 3 := skip_buffers params positive
  change ((Direct.draw params).lower (Fresh.port (tape params))).memBound ≤ 3 at drawn
  simp only [code, Interactive.Code.lower, WordIO.Code.memBound]
  omega

theorem descriptionFits : ((code params positive).lower (Fresh.port (tape params))).DescriptionFits :=
  .seq params.wordFits (UniformSampling.descriptionFits Fresh.randomBound params.wordFits Fresh.randomFits (Direct.request params))
    (.compute (finish params positive).description_fits)

end Direct
end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated.Nonzero
