import Signatures.Runtime.SchnorrLazySeed
import Signatures.Runtime.SeededTrace
import Signatures.Schnorr.LazyROMReduction

/-! A finite retained tape for the exact raw oracle interface of the named
Schnorr ROM reduction. Caller and simulator private draws keep their original
uniform-family ordering; no private-family splitting or expansion is performed.
The shared cell representation and scan/reset code are reused directly. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.RawTape

abbrev Spec (F : Type) := unifSpec + (Unit →ₒ F)
abbrev State (F : Type) := LazySeed.State F

def family : Nat ⊕ Unit → (Nat ⊕ Unit) ⊕ Unit
  | .inl n => .inl (.inl n)
  | .inr () => .inr ()

theorem family_injective : Function.Injective family := by
  intro i j same
  rcases i with n | ⟨⟩ <;> rcases j with m | ⟨⟩ <;> simp_all [family]

def tag (i : Nat ⊕ Unit) : Nat := SeedTape.familyTag (family i)

variable {F : Type} [Zero F]

def encode : (i : (Spec F).Domain) → (Spec F).Range i → TapeCell F
  | .inl n, answer => encodeReply (.inl (.inl n)) answer
  | .inr (), answer => encodeReply (.inr ()) answer

def decode : (i : (Spec F).Domain) → TapeCell F → (Spec F).Range i
  | .inl n, cell => decodeReply (.inl (.inl n)) cell
  | .inr (), cell => decodeReply (.inr ()) cell

def values : (i : (Spec F).Domain) → List (TapeCell F) → List ((Spec F).Range i)
  | .inl n, cells => SeedTape.values (.inl (.inl n)) cells
  | .inr (), cells => SeedTape.values (.inr ()) cells

def toSeed (cells : List (TapeCell F)) : QuerySeed (Spec F) := fun i => values i cells

theorem values_pop (i : (Spec F).Domain) (cells : List (TapeCell F)) :
    values i cells =
      let scan := SeedTape.pop (tag i) (0, (0 : F), 0) cells
      if scan.1 then decode i scan.2.1 :: values i scan.2.2 else [] := by
  rcases i with n | ⟨⟩ <;> exact SeedTape.values_pop _ _ _

theorem values_pop_other (i j : (Spec F).Domain) (different : j ≠ i)
    (cells : List (TapeCell F)) :
    values j (SeedTape.pop (tag i) (0, (0 : F), 0) cells).2.2 = values j cells := by
  have h : family j ≠ family i := fun same => different (family_injective same)
  rcases i with n | ⟨⟩ <;> rcases j with m | ⟨⟩ <;>
    exact SeedTape.values_pop_other _ _ h _ _

theorem toSeed_pop (i : (Spec F).Domain) (cells : List (TapeCell F)) :
    toSeed (SeedTape.pop (tag i) (0, (0 : F), 0) cells).2.2 =
      (toSeed cells).update i (values i (SeedTape.pop (tag i) (0, (0 : F), 0) cells).2.2) := by
  funext j
  by_cases same : j = i
  · subst j
    simp [toSeed]
  · rw [QuerySeed.update_of_ne _ _ _ _ same]
    exact values_pop_other i j same cells

/-- A hit consumes one cell; a miss records precisely the fresh raw reply. -/
def oracle : QueryImpl (Spec F) (StateT (State F) (OracleComp (Spec F))) :=
  fun i state =>
    let scan := SeedTape.pop (tag i) (0, 0, 0) state.remaining
    if scan.1 then pure (decode i scan.2.1, { state with remaining := scan.2.2 })
    else (fun answer => (answer, { state with saved := state.saved ++ [encode i answer] })) <$>
      ((Spec F).query i : OracleComp (Spec F) _)

theorem oracle_seeded (i : (Spec F).Domain) :
    StateRefines (fun state : State F => toSeed state.remaining) (oracle i) (seededOracle i) := by
  intro state
  have hv := values_pop i state.remaining
  cases found : (SeedTape.pop (tag i) (0, (0 : F), 0) state.remaining).1 with
  | false =>
      have empty : toSeed state.remaining i = [] := by simpa [toSeed, found] using hv
      rw [seededOracle.run_nil empty]
      simp [oracle, found, StateT.run, Functor.map_map]
  | true =>
      have head : toSeed state.remaining i =
          decode i (SeedTape.pop (tag i) (0, (0 : F), 0) state.remaining).2.1 ::
            values i (SeedTape.pop (tag i) (0, (0 : F), 0) state.remaining).2.2 := by
        simpa [toSeed, found] using hv
      rw [seededOracle.run_cons head]
      simp only [oracle, found, ite_true, StateT.run, map_pure, toSeed_pop]

theorem simulate_seeded {A : Type} (main : OracleComp (Spec F) A) :
    StateRefines (fun state : State F => toSeed state.remaining)
      (simulateQ oracle main) (simulateQ seededOracle main) := by
  induction main using OracleComp.inductionOn with
  | pure a => exact StateRefines.pure _ a
  | query_bind i next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact StateRefines.bind _ (oracle_seeded i) ih

theorem run'_seeded {A : Type} (main : OracleComp (Spec F) A) (state : State F) :
    (simulateQ oracle main).run' state =
      (simulateQ seededOracle main).run' (toSeed state.remaining) := by
  have h := congrArg (Functor.map Prod.fst) (simulate_seeded main state)
  simpa only [Functor.map_map, StateT.run', StateT.run] using h

def encodeLog (log : QueryLog (Spec F)) : List (TapeCell F) :=
  log.map (fun entry => encode entry.1 entry.2)

theorem values_encode_cons (i j : (Spec F).Domain) (answer : (Spec F).Range i)
    (cells : List (TapeCell F)) :
    values j (encode i answer :: cells) =
      if same : j = i then same.symm ▸ (answer :: values i cells) else values j cells := by
  by_cases same : j = i
  · subst j
    rcases i with n | ⟨⟩ <;> simp [values, encode, SeedTape.values_encode_cons]
  · rcases i with n | ⟨⟩ <;> rcases j with m | ⟨⟩ <;>
      simp_all [values, encode, SeedTape.values_encode_cons]

theorem toSeed_encode (log : QueryLog (Spec F)) :
    toSeed (encodeLog log) = SeededTrace.restore log ∅ := by
  induction log with
  | nil =>
      funext i
      rcases i with n | ⟨⟩ <;> rfl
  | cons entry log ih =>
      rcases entry with ⟨i, answer⟩
      change toSeed (encode i answer :: encodeLog log) =
        (SeededTrace.restore log ∅).prependValues [answer]
      rw [← ih]
      funext j
      change values j (encode i answer :: encodeLog log) = _
      rw [values_encode_cons]
      by_cases same : j = i
      · subst j
        simp [toSeed]
      · simp [same, toSeed]

/-- The complete joint first-run output and chronological raw tape. -/
theorem run_log {A : Type} (main : OracleComp (Spec F) A) (saved : List (TapeCell F)) :
    (simulateQ oracle main).run ⟨saved, []⟩ =
      (fun p => (p.1, (⟨saved ++ encodeLog p.2, []⟩ : State F))) <$> main.withQueryLog := by
  induction main using OracleComp.inductionOn generalizing saved with
  | pure a => simp [encodeLog]
  | query_bind i next ih =>
      change (simulateQ oracle (OracleComp.queryBind i next)).run ⟨saved, []⟩ =
        (fun p => (p.1, (⟨saved ++ encodeLog p.2, []⟩ : State F))) <$>
          (OracleComp.queryBind i next).withQueryLog
      rw [Replay.withQueryLog_queryBind]
      change ((fun answer => (answer, (⟨saved ++ [encode i answer], []⟩ : State F))) <$>
        (liftM ((Spec F).query i) : OracleComp (Spec F) _) >>=
          fun p => (simulateQ oracle (next p.1)).run p.2) =
        (fun p => (p.1, (⟨saved ++ encodeLog p.2, []⟩ : State F))) <$>
          ((liftM ((Spec F).query i) : OracleComp (Spec F) _) >>= fun answer =>
            (fun p => (p.1, ⟨i, answer⟩ :: p.2)) <$> (next answer).withQueryLog)
      simp only [bind_map_left, map_bind]
      congr 1
      funext answer
      rw [ih]
      simp only [Functor.map_map, encodeLog, List.map_cons, List.append_assoc,
        List.singleton_append]

/-- Reset only the challenge family; every raw private draw is retained. -/
def restart (slot : Nat) (answer : F) (state : State F) : State F :=
  LazySeed.State.fromTape (SeedTape.reset 1 slot (1, answer, 0) state.saved)

theorem restart_seed (slot : Nat) (answer : F) (state : State F) :
    toSeed (restart slot answer state).remaining =
      ((toSeed state.saved).takeAtIndex (.inr ()) slot).addValue (.inr ()) answer := by
  funext i
  have h := congrFun (SeedTape.toSeed_reset (.inr ()) slot answer state.saved) (family i)
  rcases i with n | ⟨⟩ <;>
    simpa [restart, LazySeed.State.fromTape, toSeed, values, family,
      SeedTape.toSeed, SeedTape.familyTag, encodeReply] using h

end Signatures.Runtime.Schnorr.RawTape
