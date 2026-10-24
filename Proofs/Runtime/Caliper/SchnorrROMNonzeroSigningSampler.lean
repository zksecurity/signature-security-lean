import Proofs.Runtime.Caliper.SchnorrROMEnumeratedDraw

/-! An executed uniform draw of a NONZERO scalar in the enumerated index
representation. A uniform index below `bound` is reduced by executed word modulo
and mapped past the index of `0` by an executed unsigned comparison and word
addition: `k ↦ k + [index 0 ≤ k]`, i.e. `Fin.succAbove (index 0)`. The index of
`0` is a per-parameter immediate, like the modulus literal of `Enumerated`.

The same executed map serves two callers: a private replayed caller for the
shared tape (its single uniform request is `bound - 1`) and a direct draw on the
uniform port. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated.Nonzero
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (params : Parameters w F)

/-- The index of the field zero: an immediate of the generated code. -/
def zeroIndex : Fin (params.bound + 1) := params.index 0
/-- Skip the zero index. -/
def skip (k : Fin params.bound) : Fin (params.bound + 1) := (zeroIndex params).succAbove k
/-! ### Caller requests (independent of the positivity witness) -/

def request : Request (layout params) := ⟨params.bound - 1, by change params.bound - 1 < 2 ^ w - 2; have := params.rangeFits; omega⟩
def initial (_ : (tape params).unit.Value) : Head (layout params) := .inr (request params, ())

def initialCode : Realizer .unit (tape params).unit.representation (CallerStep.next (step (layout params))) (initial params) :=
  Assembly.realizer .unit (by decide) _ _ _ [.literal 1, .literal (BitVec.ofNat w (params.bound - 1))] params.wordFits
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro _ _ _ operand member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> trivial)
    (fun _ _ _ => rfl)


def Direct.request : Fin (Fresh.randomBound (w := w) + 1) :=
  ⟨params.bound - 1, by rw [Fresh.randomSize]; have := params.rangeFits; omega⟩


def Direct.draw : Interactive.Code w :=
  UniformSampling.code Fresh.randomBound params.wordFits Fresh.randomFits (Direct.request params)

variable (positive : 0 < params.bound)

/-- Reduce an arbitrary reply below `bound`. -/
def reduce (r : Nat) : Fin params.bound := ⟨r % params.bound, Nat.mod_lt _ positive⟩
/-- The scalar selected by a raw reply. -/
def scalarOf (r : Nat) : (scalar params).Value :=
  ⟨params.index.symm (skip params (reduce params positive r)), trivial⟩

omit [Zero F] in
theorem skip_val (z : Fin (params.bound + 1)) (k : Fin params.bound) :
    (z.succAbove k).val = k.val + (if z.val ≤ k.val then 1 else 0) := by
  unfold Fin.succAbove
  split_ifs with lower upper upper
  · simp only [Fin.lt_def, Fin.val_castSucc] at lower; omega
  · simp
  · simp
  · simp only [Fin.lt_def, Fin.val_castSucc, not_lt] at lower; omega

theorem scalarOf_ne (r : Nat) : (scalarOf params positive r).val ≠ 0 := by
  intro same
  have indexed := congrArg params.index same
  simp only [scalarOf, Equiv.apply_symm_apply] at indexed
  exact Fin.succAbove_ne _ _ indexed

omit [Zero F] in
theorem boundFits : params.bound < 2 ^ w := by have := params.rangeFits; omega
theorem zeroFits : (zeroIndex params).val < 2 ^ w := by have := (zeroIndex params).isLt; have := params.rangeFits; omega

/-! ### The executed map past zero -/

def word := wordRepresentation w (width_pos params.wordFits)

def reduceArgs : Realizer .unit (word params) (WordBinary.pair w params.wordFits)
    (fun value => (value, BitVec.ofNat w params.bound)) :=
  Assembly.realizer .unit (by decide) _ _ _ [.read 0 0, .literal (BitVec.ofNat w params.bound)] params.wordFits
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 1 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [Assembly.Operand.Valid, size])
    (by
      intro value before holds
      have contents : before.bufs 0 = #[value] := Array.toList_inj.mp holds.2.1
      change [(before.bufs 0)[0]?.getD 0, BitVec.ofNat w params.bound] = _
      rw [contents]
      rfl)

def compareArgs : Realizer .unit (word params) (WordBinary.pair w params.wordFits)
    (fun value => (BitVec.ofNat w (zeroIndex params).val, value)) :=
  Assembly.realizer .unit (by decide) _ _ _ [.literal (BitVec.ofNat w (zeroIndex params).val), .read 0 0] params.wordFits
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 1 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [Assembly.Operand.Valid, size])
    (by
      intro value before holds
      have contents : before.bufs 0 = #[value] := Array.toList_inj.mp holds.2.1
      change [BitVec.ofNat w (zeroIndex params).val, (before.bufs 0)[0]?.getD 0] = _
      rw [contents]
      rfl)

def compare : Realizer .unit (word params) (word params)
    (fun value => BinOp.eval .ule (BitVec.ofNat w (zeroIndex params).val) value) :=
  (compareArgs params).then (WordBinary.realizer .unit .ule params.wordFits)

omit [Zero F] in
theorem pairFits : (word params).encoding.words + (word params).encoding.words < 2 ^ w := by
  change 1 + 1 < 2 ^ w; have := params.wordFits; omega

theorem compare_buffers : (compare params).code.memBound ≤ 2 := by
  have args := (Assembly.code_names (w := w) [.literal (BitVec.ofNat w (zeroIndex params).val), .read 0 0] 1
    (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).2
  change max (compareArgs params).code.memBound (WordBinary.code (w := w) .ule).memBound ≤ 2
  change (compareArgs params).code.memBound ≤ 2 at args
  have word : (WordBinary.code (w := w) .ule).memBound ≤ 2 := by change 1 ≤ 2; omega
  omega

theorem compare_nameFits : (compare params).savedBuffer < 2 ^ w := by
  have := compare_buffers params; have := params.wordFits
  unfold Realizer.savedBuffer; omega

omit [Zero F] in
theorem identity_nameFits : (Realizer.identity (cost := .unit) (width_pos params.wordFits) (word params)).savedBuffer < 2 ^ w := by
  have := params.wordFits
  change max 2 0 < 2 ^ w; omega

def flagged : Realizer .unit (word params) (WordBinary.pair w params.wordFits)
    (fun value => (value, BinOp.eval .ule (BitVec.ofNat w (zeroIndex params).val) value)) :=
  Pairing.realizer (Realizer.identity (width_pos params.wordFits) (word params)) (compare params) (by decide) params.wordFits
    (identity_nameFits params) (compare_nameFits params) (pairFits params) (pairFits params) (pairFits params)

/-- The word computed by the executed map. -/
def mapWord (value : Word w) : Word w :=
  let reduced := value % BitVec.ofNat w params.bound
  reduced + BinOp.eval .ule (BitVec.ofNat w (zeroIndex params).val) reduced

def mapped : Realizer .unit (word params) (word params) (mapWord params) :=
  (((reduceArgs params).then (WordBinary.realizer .unit .umod params.wordFits)).then (flagged params)).then
    (WordBinary.realizer .unit .add params.wordFits)

theorem mapWord_eq (value : Word w) :
    mapWord params value = BitVec.ofNat w (skip params (reduce params positive value.toNat)).val := by
  have boundFits := boundFits params
  have zeroFits := zeroFits params
  have reducedLt : value.toNat % params.bound < params.bound := Nat.mod_lt _ positive
  apply BitVec.eq_of_toNat_eq
  simp only [mapWord, BinOp.eval, BitVec.toNat_add, BitVec.toNat_umod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt boundFits, Nat.mod_eq_of_lt zeroFits, skip, reduce, skip_val]
  split_ifs with compared
  · have one : (1 : Word w).toNat = 1 := by simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (width_pos params.wordFits).ne')]
    rw [one]
  · have small : value.toNat % params.bound < 2 ^ w := by omega
    have zero : (0 : Word w).toNat = 0 := by simp
    rw [zero, Nat.add_zero, Nat.mod_eq_of_lt small]

/-- The executed map past zero, as a scalar-valued realizer on any word. -/
def skipRealizer : Realizer .unit (word params) (scalar params).representation
    (fun value => scalarOf params positive value.toNat) :=
  (mapped params).viewOutput (scalar params).representation (fun value => scalarOf params positive value.toNat) (by
    intro value
    change [BitVec.ofNat w (params.index (params.index.symm (skip params (reduce params positive value.toNat)))).val] =
      [mapWord params value]
    rw [Equiv.apply_symm_apply, mapWord_eq params positive])

/-! ### The private replayed caller -/

def normalized (value : Unit × Response (layout params)) : (scalar params).Value := scalarOf params positive value.2.val.2
def advance (value : Unit × Response (layout params)) : Head (layout params) := .inl (normalized params positive value)

def reply : Realizer .unit (CallerStep.resume (step (layout params))) (word params)
    (fun value => BitVec.ofNat w value.2.val.2) :=
  Assembly.realizer .unit (by decide) _ _ _ [.read 0 1] params.wordFits
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 2 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      simp [Assembly.Operand.Valid, size, (width_pos params.wordFits).ne'])
    (by
      intro value before holds
      have contents : before.bufs 0 = #[BitVec.ofNat w value.2.val.1, BitVec.ofNat w value.2.val.2] :=
        Array.toList_inj.mp holds.2.1
      change [(before.bufs 0)[1]?.getD 0] = _
      rw [contents]
      rfl)

def normalize : Realizer .unit (CallerStep.resume (step (layout params))) (scalar params).representation
    (normalized params positive) :=
  ((reply params).then (skipRealizer params positive)).viewOutput (scalar params).representation
    (normalized params positive) (by
      intro value
      have replyFits : value.2.val.2 < 2 ^ w := value.2.property.1.2
      change _ = (scalar params).representation.encoding.encode
        (scalarOf params positive (BitVec.ofNat w value.2.val.2).toNat)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt replyFits]
      rfl)

def continuation : Realizer .unit (CallerStep.resume (step (layout params))) (CallerStep.next (step (layout params)))
    (advance params positive) :=
  (normalize params positive).then (inlRealizer .unit (by decide) (scalar params).representation
    ((Reply.range (tape params)).representation.prod (Pairing.unitRepresentation w) (by change 1 + 0 < 2 ^ w; have := params.wordFits; omega))
    params.wordFits (by change 1 + max 1 (1 + 0) < 2 ^ w; have := params.wordFits; omega))

theorem mapped_buffers : (mapped params).code.memBound ≤ 3 := by
  have reduced := (Assembly.code_names (w := w) [.read 0 0, .literal (BitVec.ofNat w params.bound)] 1
    (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).2
  have paired := Pairing.buffers (Realizer.identity (cost := .unit) (width_pos params.wordFits) (word params)) (compare params)
    (by decide) params.wordFits (identity_nameFits params) (compare_nameFits params) (pairFits params) (pairFits params) (pairFits params)
  have compared := compare_buffers params
  change (reduceArgs params).code.memBound ≤ 2 at reduced
  change (flagged params).code.memBound ≤ _ at paired
  change max (max (max (reduceArgs params).code.memBound (WordBinary.code (w := w) .umod).memBound)
    (flagged params).code.memBound) (WordBinary.code (w := w) .add).memBound ≤ 3
  have umod : (WordBinary.code (w := w) .umod).memBound ≤ 1 := by change 1 ≤ 1; omega
  have add : (WordBinary.code (w := w) .add).memBound ≤ 1 := by change 1 ≤ 1; omega
  have identity : (Realizer.identity (cost := .unit) (width_pos params.wordFits) (word params)).code.memBound = 0 := rfl
  rw [identity] at paired
  omega

theorem skip_buffers : (skipRealizer params positive).code.memBound ≤ 3 := mapped_buffers params

omit [Zero F] in
theorem initial_buffers : (initialCode params).code.memBound ≤ 2 := by
  exact (Assembly.code_names _ 1 (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).2

theorem continuation_buffers : (continuation params positive).code.memBound ≤ 3 := by
  have picked := (Assembly.code_names (w := w) [.read 0 1] 1
    (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).2
  have tag := (Assembly.code_names (w := w) (Construction.taggedOperands 0 1 0) 1
    (by simp [Construction.taggedOperands, Assembly.SourcesBound, Assembly.Operand.SourcesBound, Assembly.reads])).2
  have skipped := skip_buffers params positive
  change max (max (reply params).code.memBound (skipRealizer params positive).code.memBound)
    (Assembly.code (Construction.taggedOperands 0 1 0)).memBound ≤ 3
  change (reply params).code.memBound ≤ 2 at picked
  omega

def caller : Caller (layout params) where
  initial := initial params
  advance := advance params positive
  initialCode := initialCode params
  continuation := continuation params positive
  initialFits := by have := initial_buffers params; have := params.wordFits; unfold Realizer.savedBuffer; omega
  localFits := by have := continuation_buffers params positive; have := params.wordFits; unfold Realizer.savedBuffer; omega

theorem terminates : Terminates (layout params) (caller params positive) 1 := by
  intro value
  change ∀ answer, True
  intro _
  trivial

/-- The replayed caller's exact query program: one uniform query of range
`bound - 1`, mapped past the zero index. -/
theorem original_typed (input : (tape params).unit.Value) :
    original (layout params) (caller params positive) 1 (terminates params positive) input =
      (fun answer : Fin (params.bound - 1 + 1) => scalarOf params positive answer.val) <$>
        (unifSpec.query (params.bound - 1) : ProbComp (Fin (params.bound - 1 + 1))) := by
  have implemented := CallerMachine.ofCaller_implements (spec := unifSpec) Subtype.val (representReply (layout params))
    (advance params positive) (initial params) 1 (terminates params positive) input
  change (do
    let answer ← (unifSpec.query (params.bound - 1) : ProbComp (Fin (params.bound - 1 + 1)))
    pure (some (normalized params positive ((), representReply (layout params) (request params) answer)))) =
      some <$> original (layout params) (caller params positive) 1 (terminates params positive) input at implemented
  apply (map_inj_right (fun h => Option.some.inj h)).mp
  rw [← implemented]
  rfl

/-! ### The direct draw on the uniform port -/

namespace Direct

def finish : Realizer .unit (UniformSampling.output Fresh.randomBound params.wordFits Fresh.randomFits (Direct.request params)).representation
    (scalar params).representation (fun value => scalarOf params positive value.val.val) :=
  ((skipRealizer params positive).viewInput _
    (fun value : (UniformSampling.output Fresh.randomBound params.wordFits Fresh.randomFits (Direct.request params)).Value =>
      BitVec.ofNat w value.val.val) (fun _ => rfl)).viewOutput (scalar params).representation
    (fun value => scalarOf params positive value.val.val) (by
      intro value
      have small : value.val.val < 2 ^ w := by
        have lt : value.val.val < params.bound - 1 + 1 := value.val.isLt
        have := params.rangeFits
        omega
      change _ = (scalar params).representation.encoding.encode
        (scalarOf params positive (BitVec.ofNat w value.val.val).toNat)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small])

def code : Interactive.Code w := .seq (Direct.draw params) (.compute (finish params positive).code)

/-- A uniformly random nonzero scalar, as a query program. -/
def nonzeroSource : ProbComp (scalar params).Value :=
  (fun answer : Fin (params.bound - 1 + 1) => scalarOf params positive answer.val) <$>
    (unifSpec.query (params.bound - 1) : ProbComp (Fin (params.bound - 1 + 1)))

theorem refines : Interactive.Refines (Fresh.port (tape params)) .unit
    (tape params).unit.representation (scalar params).representation (fun _ => nonzeroSource params positive)
    (code params positive) := by
  have drawn := UniformSampling.refines Fresh.randomBound params.wordFits Fresh.randomFits (Direct.request params)
  have composed := drawn.seq (Interactive.Refines.compute (UniformQuery.port Fresh.randomBound params.wordFits Fresh.randomFits)
    .unit (finish params positive))
  change Interactive.Refines (UniformQuery.port Fresh.randomBound params.wordFits Fresh.randomFits) .unit
    (UniformSampling.input (w := w)).representation (scalar params).representation (fun _ => nonzeroSource params positive)
    (code params positive)
  convert composed using 1
  funext value
  simp only [UniformSampling.source, nonzeroSource, bind_pure_comp, Functor.map_map, request]
  rfl

end Direct

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated.Nonzero
