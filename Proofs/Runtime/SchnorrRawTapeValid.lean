import Proofs.Runtime.SchnorrRawTape

/-! Recorded natural-valued replies fit their request's range. The native
runner can read that stored natural directly on a hit; it need not enumerate
the range or encode an arity-specific decoder in the program. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.RawTape

variable {F : Type} [Zero F]

def ValidCell (cell : TapeCell F) : Prop :=
  ∀ n, cell.1 = n + 2 → cell.2.2 ≤ n

def Valid (cells : List (TapeCell F)) : Prop := ∀ cell ∈ cells, ValidCell cell

theorem encode_valid (i : (Spec F).Domain) (answer : (Spec F).Range i) :
    ValidCell (encode i answer) := by
  rcases i with n | ⟨⟩
  · intro m same
    simp only [encode, encodeReply, Nat.add_right_cancel_iff] at same
    subst m
    exact Nat.le_of_lt_succ answer.isLt
  · intro n same
    simp only [encode, encodeReply] at same
    omega

/-- The scan only removes cells, and a successful result has the requested tag. -/
theorem pop_valid (tag : Nat) (cells : List (TapeCell F)) (valid : Valid cells) :
    Valid (SeedTape.pop tag (0, (0 : F), 0) cells).2.2 ∧
      ((SeedTape.pop tag (0, (0 : F), 0) cells).1 = true →
        ValidCell (SeedTape.pop tag (0, (0 : F), 0) cells).2.1 ∧
          (SeedTape.pop tag (0, (0 : F), 0) cells).2.1.1 = tag) := by
  induction cells with
  | nil => simp [SeedTape.pop, Valid]
  | cons cell cells ih =>
      have head : ValidCell cell := valid cell (by simp)
      have tail : Valid cells := fun x hx => valid x (by simp [hx])
      by_cases same : cell.1 = tag
      · simpa [SeedTape.pop, same] using And.intro tail (And.intro head same)
      · obtain ⟨rest, found⟩ := ih tail
        simp only [SeedTape.pop, same, ite_false]
        refine ⟨?_, found⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact head
        · exact rest x hx

omit [Zero F] in
theorem decode_uniform_val (n : Nat) (cell : TapeCell F) (valid : ValidCell cell)
    (tagged : cell.1 = n + 2) :
    (decode (.inl n) cell).val = cell.2.2 := by
  have bound := valid n tagged
  exact Nat.mod_eq_of_lt (by omega)

theorem oracle_valid (i : (Spec F).Domain) (state : State F)
    (saved : Valid state.saved) (remaining : Valid state.remaining)
    (out : (Spec F).Range i × State F) (supported : out ∈ support ((oracle i).run state)) :
    Valid out.2.saved ∧ Valid out.2.remaining := by
  obtain ⟨rest, _⟩ := pop_valid (tag i) state.remaining remaining
  cases found : (SeedTape.pop (tag i) (0, (0 : F), 0) state.remaining).1 with
  | false =>
      simp only [oracle, found, Bool.false_eq_true, ite_false, StateT.run,
        support_map, Set.mem_image] at supported
      obtain ⟨answer, _, rfl⟩ := supported
      refine ⟨?_, remaining⟩
      intro cell member
      rcases List.mem_append.mp member with old | fresh
      · exact saved cell old
      · have same : cell = encode i answer := by simpa using fresh
        subst cell
        exact encode_valid i answer
  | true =>
      simp only [oracle, found, ite_true, StateT.run, support_pure,
        Set.mem_singleton_iff] at supported
      subst out
      exact ⟨saved, rest⟩

theorem simulate_valid {A : Type} (main : OracleComp (Spec F) A) (state : State F)
    (saved : Valid state.saved) (remaining : Valid state.remaining)
    (out : A × State F) (supported : out ∈ support ((simulateQ oracle main).run state)) :
    Valid out.2.saved ∧ Valid out.2.remaining := by
  induction main using OracleComp.inductionOn generalizing state with
  | pure value =>
      have same : out = (value, state) := by simpa using supported
      subst out
      exact ⟨saved, remaining⟩
  | query_bind i next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨middle, hmiddle, supported⟩ := supported
      obtain ⟨hs, hr⟩ := oracle_valid i state saved remaining middle hmiddle
      exact ih middle.1 middle.2 hs hr supported

omit [Zero F] in
theorem trim_valid (tag slot : Nat) (cells : List (TapeCell F)) (valid : Valid cells) :
    Valid (SeedTape.trim tag slot cells).2 := by
  induction cells generalizing slot with
  | nil => exact valid
  | cons cell cells ih =>
      have head : ValidCell cell := valid cell (by simp)
      have tail : Valid cells := fun x hx => valid x (by simp [hx])
      have keep (n : Nat) : Valid (cell :: (SeedTape.trim tag n cells).2) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact head
        · exact ih n tail x hx
      by_cases tagged : cell.1 = tag <;> cases slot <;>
        simp only [SeedTape.trim, tagged, ite_true, ite_false, Nat.succ_ne_zero, Nat.reduceSub] <;>
        first | exact ih _ tail | exact keep _

theorem restart_valid (slot : Nat) (answer : F) (state : State F)
    (valid : Valid state.saved) :
    Valid (restart slot answer state).saved ∧ Valid (restart slot answer state).remaining := by
  have h : Valid (SeedTape.reset 1 slot (1, answer, 0) state.saved) := by
    intro cell member
    rcases List.mem_append.mp member with old | fresh
    · exact trim_valid 1 slot state.saved valid cell old
    · have same : cell = encode (.inr ()) answer := by simpa [encode, encodeReply] using fresh
      subst cell
      exact encode_valid (.inr ()) answer
  exact ⟨h, h⟩

end Signatures.Runtime.Schnorr.RawTape
