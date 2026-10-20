import Signatures.Runtime.Caliper.SchnorrROMPrivatePairBounds
import Signatures.Runtime.Caliper.WordBinary

/-! A concrete local caller for a uniform scalar represented by its finite
index. The caller asks one uniform query, normalizes the reply with word modulo
and emits the scalar tag. Its code never enumerates the scalar domain.
The shared private replay handler supplies the query, as for adaptive callers. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated
open Caliper BoundedSource OracleComp OracleSpec

structure Parameters (w : Nat) (F : Type) where
  bound : Nat
  index : F ≃ Fin (bound + 1)
  capacity : Nat
  wordFits : 16 < 2 ^ w
  rangeFits : bound + 2 < 2 ^ w
  storageFits : 16 * (4 + (capacity + 2) * 3) < 2 ^ w

variable {w : Nat} {F : Type} (params : Parameters w F)

def scalar : Layout w F := Layout.all
  ((Representation.fin w (params.bound + 1) (width_pos params.wordFits) (by have := params.rangeFits; omega)).transport params.index)
def tape : SchnorrROMTape.Layouts w F where
  scalar := scalar params
  capacity := params.capacity
  wordFits := params.wordFits
  countFits := by have := params.storageFits; omega
  storageFits := params.storageFits
def layout : PrivateSampler.Layouts w F Unit where
  tape := tape params
  state := Pairing.unitRepresentation w
  fits := by
    change 8 * (1 + 0 + 1 + 2 + 1 + ((1 + params.capacity * (1 + (1 + 1))) + (1 + params.capacity * (1 + (1 + 1))))) < 2 ^ w
    have := params.storageFits
    omega

def request : Request (layout params) := ⟨params.bound, by change params.bound < 2 ^ w - 2; have := params.rangeFits; omega⟩
def initial (_ : (tape params).unit.Value) : Head (layout params) := .inr (request params, ())
def normalized (value : Unit × Response (layout params)) : (scalar params).Value :=
  ⟨params.index.symm ⟨value.2.val.2 % (params.bound + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩, trivial⟩
def advance (value : Unit × Response (layout params)) : Head (layout params) := .inl (normalized params value)

def initialCode : Realizer .unit (tape params).unit.representation (CallerStep.next (step (layout params))) (initial params) :=
  Assembly.realizer .unit (by decide) _ _ _ [.literal 1, .literal (BitVec.ofNat w params.bound)] params.wordFits
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro _ _ _ operand member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> trivial)
    (fun _ _ _ => rfl)

def arguments : Realizer .unit (CallerStep.resume (step (layout params))) (WordBinary.pair w params.wordFits)
    (fun value => (BitVec.ofNat w value.2.val.2, BitVec.ofNat w (params.bound + 1))) :=
  Assembly.realizer .unit (by decide) _ _ _ [.read 0 1, .literal (BitVec.ofNat w (params.bound + 1))] params.wordFits
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 2 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [Assembly.Operand.Valid, size, (width_pos params.wordFits).ne'])
    (by
      intro value before holds
      have contents : before.bufs 0 = #[BitVec.ofNat w value.2.val.1, BitVec.ofNat w value.2.val.2] :=
        Array.toList_inj.mp holds.2.1
      change [(before.bufs 0)[1]?.getD 0, BitVec.ofNat w (params.bound + 1)] = _
      rw [contents]
      rfl)

def normalize : Realizer .unit (CallerStep.resume (step (layout params))) (scalar params).representation (normalized params) :=
  ((arguments params).then (WordBinary.realizer .unit .umod params.wordFits)).viewOutput
    (scalar params).representation (normalized params) (by
      intro value
      have replyFits : value.2.val.2 < 2 ^ w := value.2.property.1.2
      have modulusFits : params.bound + 1 < 2 ^ w := by have := params.rangeFits; omega
      change [BitVec.ofNat w (params.index (params.index.symm ⟨value.2.val.2 % (params.bound + 1), _⟩)).val] =
        [BitVec.ofNat w value.2.val.2 % BitVec.ofNat w (params.bound + 1)]
      simp only [Equiv.apply_symm_apply, BitVec.umod_def, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt replyFits, Nat.mod_eq_of_lt modulusFits])

def continuation : Realizer .unit (CallerStep.resume (step (layout params))) (CallerStep.next (step (layout params))) (advance params) :=
  (normalize params).then (inlRealizer .unit (by decide) (scalar params).representation
    ((Reply.range (tape params)).representation.prod (Pairing.unitRepresentation w) (by change 1 + 0 < 2 ^ w; have := params.wordFits; omega))
    params.wordFits (by change 1 + max 1 (1 + 0) < 2 ^ w; have := params.wordFits; omega))

theorem initial_buffers : (initialCode params).code.memBound ≤ 2 := by
  exact (Assembly.code_names _ 1 (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).2
theorem continuation_buffers : (continuation params).code.memBound ≤ 2 := by
  have args := (Assembly.code_names (w := w) [.read 0 1, .literal (BitVec.ofNat w (params.bound + 1))] 1
    (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).2
  have tag := (Assembly.code_names (w := w) (Construction.taggedOperands 0 1 0) 1
    (by simp [Construction.taggedOperands, Assembly.SourcesBound, Assembly.Operand.SourcesBound, Assembly.reads])).2
  change max (max (arguments params).code.memBound (WordBinary.code .umod).memBound)
    (Assembly.code (Construction.taggedOperands 0 1 0)).memBound ≤ 2
  change (arguments params).code.memBound ≤ 2 at args
  have word : (WordBinary.code (w := w) .umod).memBound ≤ 2 := by change 1 ≤ 2; omega
  omega

def caller : Caller (layout params) where
  initial := initial params
  advance := advance params
  initialCode := initialCode params
  continuation := continuation params
  initialFits := by have := initial_buffers params; have := params.wordFits; unfold Realizer.savedBuffer; omega
  localFits := by have := continuation_buffers params; have := params.wordFits; unfold Realizer.savedBuffer; omega

theorem terminates : Terminates (layout params) (caller params) 1 := by
  intro value
  change ∀ answer, True
  intro _
  trivial

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated
