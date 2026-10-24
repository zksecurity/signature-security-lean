import Proofs.Runtime.BackendSchnorrRawUniform
import Proofs.Runtime.BackendDataSize
import Proofs.Runtime.SeedTapeCellBounds

/-! Encoded-size invariants for native dynamic tape draws. Both saved and
remaining lists are charged, including duplicated cells. Width bounds apply to
encoded naturals, not to their numeric magnitude or the number of possible arities. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeUniform

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def CellBound (width : Nat) (cell : TapeCell F) : Prop :=
  Q.size rep.data.nat cell.1 ≤ width ∧
    Q.size (rep.ty scalar) cell.2.1 ≤ width ∧ Q.size rep.data.nat cell.2.2 ≤ width

def TapeBound (width cap : Nat) (cells : List (TapeCell F)) : Prop :=
  (∀ cell ∈ cells, CellBound (Q := Q) rep width cell) ∧ cells.length ≤ cap

def StateBound (width savedCap remainingCap : Nat)
    (state : stateTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  TapeBound (Q := Q) rep width savedCap state.1 ∧
    TapeBound (Q := Q) rep width remainingCap state.2

def InputBound (width savedCap remainingCap : Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  Q.size rep.data.nat input.1 ≤ width ∧ StateBound (Q := Q) rep width savedCap remainingCap input.2

def DrawBound (width savedCap remainingCap : Nat)
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  Q.size rep.data.nat input.1 ≤ width ∧ Q.size rep.data.nat input.2.1 ≤ width ∧
    StateBound (Q := Q) rep width savedCap remainingCap input.2.2

theorem tape_mono (width cap cap' : Nat) (cells : List (TapeCell F))
    (bound : TapeBound (Q := Q) rep width cap cells) (larger : cap ≤ cap') :
    TapeBound (Q := Q) rep width cap' cells := ⟨bound.1, bound.2.trans larger⟩

theorem pop_property (width cap tag : Nat) (fallback : TapeCell F) (cells : List (TapeCell F))
    (bound : TapeBound (Q := Q) rep width cap cells) :
    TapeBound (Q := Q) rep width cap (SeedTape.pop tag fallback cells).2.2 ∧
      ((SeedTape.pop tag fallback cells).1 = true →
        CellBound (Q := Q) rep width (SeedTape.pop tag fallback cells).2.1) := by
  have sub := SeedTape.pop_sublist tag fallback cells
  exact ⟨⟨fun cell member => bound.1 cell (sub.subset member), sub.length_le.trans bound.2⟩,
    fun found => bound.1 _ (SeedTape.pop_answer_mem tag fallback cells found)⟩

theorem prepare_property [Zero F] (width savedCap remainingCap : Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : InputBound (Q := Q) rep width savedCap remainingCap input)
    (tagWidth : Q.size rep.data.nat (input.1 + 2) ≤ width) :
    DrawBound (Q := Q) rep width savedCap remainingCap (prepareValue input).2 := by
  obtain ⟨rest, cell⟩ := pop_property rep width remainingCap (input.1 + 2)
    (0, (0 : F), 0) input.2.2 bound.2.2
  cases found : (SeedTape.pop (input.1 + 2) (0, (0 : F), 0) input.2.2).1 with
  | false => simpa [prepareValue, found, DrawBound, StateBound] using
      And.intro bound.1 (And.intro tagWidth bound.2)
  | true => simpa [prepareValue, found, DrawBound, StateBound] using
      And.intro (cell found).2.2 (And.intro tagWidth (And.intro bound.2.1 rest))

theorem hit_property (width savedCap remainingCap : Nat)
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : DrawBound (Q := Q) rep width savedCap remainingCap input) :
    InputBound (Q := Q) rep width savedCap remainingCap (hitValue input) :=
  ⟨bound.1, bound.2.2⟩

theorem save_property [Zero F] (width savedCap remainingCap : Nat)
    (zeroWidth : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : DrawBound (Q := Q) rep width savedCap remainingCap input) :
    InputBound (Q := Q) rep width (savedCap + 1) remainingCap (saveValue input) := by
  refine ⟨bound.1, ⟨?_, ?_⟩, bound.2.2.2⟩
  · intro cell member
    rcases List.mem_append.mp member with old | fresh
    · exact bound.2.2.1.1 cell old
    · have same : cell = (input.2.1, (0 : F), input.1) := by simpa using fresh
      subst cell
      exact ⟨bound.2.1, zeroWidth, bound.1⟩
  · change (input.2.2.1 ++ [(input.2.1, (0 : F), input.1)]).length ≤ savedCap + 1
    simp only [List.length_append, List.length_singleton]
    exact Nat.add_le_add_right bound.2.2.1.2 1

theorem restart_property (width cap slot : Nat) (answer : F) (state : State F)
    (bound : TapeBound (Q := Q) rep width cap state.saved)
    (replacement : CellBound (Q := Q) rep width (1, answer, 0)) :
    StateBound (Q := Q) rep width (cap + 1) (cap + 1) (encodeState (restart slot answer state)) := by
  have h : TapeBound (Q := Q) rep width (cap + 1)
      (SeedTape.reset 1 slot (1, answer, 0) state.saved) := by
    refine ⟨?_, (SeedTape.reset_length _ _ _ _).trans (Nat.add_le_add_right bound.2 1)⟩
    intro cell member
    rcases List.mem_append.mp member with old | fresh
    · exact bound.1 cell ((SeedTape.trim_sublist 1 slot state.saved).subset old)
    · have same : cell = (1, answer, 0) := by simpa using fresh
      simpa only [same] using replacement
  exact ⟨h, h⟩

section Size

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes

theorem cell_size (width : Nat) (hh : header ≤ width) (cell : TapeCell F)
    (bound : CellBound (Q := Q) rep width cell) :
    Q.size (rep.ty Replay.Mixed.event) cell ≤ 5 * width := by
  obtain ⟨ht, hf, hn⟩ := bound
  have hp := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty, Replay.Mixed.event] at *
  grind only

include lists

theorem tape_size (width cap : Nat) (hh : header ≤ width) (cells : List (TapeCell F))
    (bound : TapeBound (Q := Q) rep width cap cells) :
    Q.size (rep.ty (.list Replay.Mixed.event)) cells ≤ (6 * cap + 1) * width := by
  have h := lists.size_le_cap (rep.ty Replay.Mixed.event) cells (5 * width) cap
    (fun cell member => cell_size rep sizes width hh cell (bound.1 cell member)) bound.2
  change Q.size (rep.ty (.list Replay.Mixed.event)) cells ≤ _ at h
  nlinarith [Nat.mul_le_mul_left cap hh]

theorem state_size (width savedCap remainingCap : Nat) (hh : header ≤ width)
    (state : stateTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : StateBound (Q := Q) rep width savedCap remainingCap state) :
    Q.size (rep.ty stateTy) state ≤ (6 * (savedCap + remainingCap) + 3) * width := by
  have hs := tape_size rep sizes lists width savedCap hh state.1 bound.1
  have hr := tape_size rep sizes lists width remainingCap hh state.2 bound.2
  have hp := sizes.prod_le (rep.ty (.list Replay.Mixed.event)) (rep.ty (.list Replay.Mixed.event)) state
  change Q.size (rep.ty stateTy) state ≤ _ at hp
  nlinarith

theorem input_size (width savedCap remainingCap : Nat) (hh : header ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : InputBound (Q := Q) rep width savedCap remainingCap input) :
    Q.size (rep.ty inputTy) input ≤ (6 * (savedCap + remainingCap) + 5) * width := by
  have hs := state_size rep sizes lists width savedCap remainingCap hh input.2 bound.2
  have hp := sizes.prod_le rep.data.nat (rep.ty stateTy) input
  have hn := bound.1
  change Q.size (rep.ty inputTy) input ≤ _ at hp
  nlinarith

theorem draw_size (width savedCap remainingCap : Nat) (hh : header ≤ width)
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : DrawBound (Q := Q) rep width savedCap remainingCap input) :
    Q.size (rep.ty drawTy) input ≤ (6 * (savedCap + remainingCap) + 7) * width := by
  have hs := input_size rep sizes lists width savedCap remainingCap hh input.2 bound.2
  have hp := sizes.prod_le rep.data.nat (rep.ty inputTy) input
  have hn := bound.1
  change Q.size (rep.ty drawTy) input ≤ _ at hp
  nlinarith

theorem prepare_size [Zero F] (width savedCap remainingCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : InputBound (Q := Q) rep width savedCap remainingCap input)
    (tagWidth : Q.size rep.data.nat (input.1 + 2) ≤ width) :
    Q.size (rep.ty prepareTy) (prepareValue input) ≤ (6 * (savedCap + remainingCap) + 9) * width := by
  have hs := draw_size rep sizes lists width savedCap remainingCap hh (prepareValue input).2
    (prepare_property rep width savedCap remainingCap input bound tagWidth)
  have hp := sizes.prod_le rep.data.bool (rep.ty drawTy) (prepareValue input)
  have hn := hb (prepareValue input).1
  change Q.size (rep.ty prepareTy) (prepareValue input) ≤ _ at hp
  nlinarith

end Size

section Code

variable [C.HasSum] [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {iface : Interface (C := C) unifSpec}
  (ports : UniformSampling.Ports (Q := Q) rep.data (iface := iface))

/-- The actual native program preserves bounded cells, adds at most one saved
cell, and does not grow the remaining tape. No validity assumption is needed
for this size claim; raw-source correspondence separately requires valid tapes. -/
theorem code_property (width savedCap remainingCap arityCap : Nat)
    (hn : ∀ n ≤ arityCap + 2, Q.size rep.data.nat n ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (n : Nat) (state : State F) (arity : n ≤ arityCap)
    (bound : StateBound (Q := Q) rep width savedCap remainingCap (encodeState state))
    (out : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (supported : out ∈ support ((code rep data cost primitive ports).denote (n, encodeState state))) :
    InputBound (Q := Q) rep width (savedCap + 1) remainingCap out := by
  rw [denote] at supported
  obtain ⟨rest, cell⟩ := pop_property rep width remainingCap (n + 2)
    (0, (0 : F), 0) state.remaining bound.2
  cases found : (SeedTape.pop (n + 2) (0, (0 : F), 0) state.remaining).1 with
  | true =>
      simp only [found, ite_true, support_pure, Set.mem_singleton_iff] at supported
      subst out
      exact ⟨(cell found).2.2, tape_mono rep width savedCap (savedCap + 1) state.saved
        bound.1 (by omega), rest⟩
  | false =>
      simp only [found, Bool.false_eq_true, ite_false, support_map, Set.mem_image] at supported
      obtain ⟨answer, _, rfl⟩ := supported
      exact save_property rep width savedCap remainingCap hz
        (answer.val, n + 2, encodeState state)
        ⟨hn answer.val (by have := answer.isLt; omega), hn (n + 2) (by omega), bound⟩

end Code

end Signatures.Runtime.Schnorr.RawTape.NativeUniform
