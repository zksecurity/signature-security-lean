import Signatures.Runtime.SeedTapeScan
import Signatures.Runtime.Refinement
import VCVio.OracleComp.QueryTracking.SeededOracle

/-! An encoded finite tape realizes the typed seeded oracle. The representation
works for every cell list; decoding is total even on malformed input. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.SeedTape

def familyTag : (Nat ⊕ Unit) ⊕ Unit → Nat
  | .inl (.inl n) => n + 2
  | .inl (.inr ()) => 0
  | .inr () => 1

theorem familyTag_injective : Function.Injective familyTag := by
  intro i j h
  rcases i with (n | ⟨⟩) | ⟨⟩ <;> rcases j with (m | ⟨⟩) | ⟨⟩ <;>
    simp_all [familyTag]

variable {F : Type}

def values (i : (replaySpec F).Domain) : List (TapeCell F) → List ((replaySpec F).Range i)
  | [] => []
  | x :: xs => if x.1 = familyTag i then decodeReply i x :: values i xs else values i xs

def toSeed (xs : List (TapeCell F)) : QuerySeed (replaySpec F) := fun i => values i xs

theorem values_pop (i : (replaySpec F).Domain) (fallback : TapeCell F) (xs : List (TapeCell F)) :
    values i xs =
      let r := pop (familyTag i) fallback xs
      if r.1 then decodeReply i r.2.1 :: values i r.2.2 else [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x.1 = familyTag i
      · simp [pop, values, hx]
      · cases hf : (pop (familyTag i) fallback xs).1 <;> simp_all [pop, values]

theorem values_pop_other (i j : (replaySpec F).Domain) (hji : j ≠ i)
    (fallback : TapeCell F) (xs : List (TapeCell F)) :
    values j (pop (familyTag i) fallback xs).2.2 = values j xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x.1 = familyTag i
      · have ht : familyTag i ≠ familyTag j := fun h => hji (familyTag_injective h).symm
        simp [pop, values, hx, ht]
      · simp [pop, values, hx, ih]

theorem pop_miss_rest (tag : Nat) (fallback : TapeCell F) (xs : List (TapeCell F))
    (h : (pop tag fallback xs).1 = false) : (pop tag fallback xs).2.2 = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x.1 = tag
      · simp [pop, hx] at h
      · simp only [pop, hx, ite_false] at h ⊢
        rw [ih h]

theorem toSeed_pop (i : (replaySpec F).Domain) (fallback : TapeCell F) (xs : List (TapeCell F)) :
    toSeed (pop (familyTag i) fallback xs).2.2 =
      (toSeed xs).update i (values i (pop (familyTag i) fallback xs).2.2) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [toSeed]
  · rw [QuerySeed.update_of_ne _ _ _ _ hj]
    exact values_pop_other i j hj fallback xs

/-- A typed request consumes its own family's next cell. On a miss the
underlying oracle is queried and the tape is left unchanged. -/
def oracle [Zero F] : QueryImpl (replaySpec F) (StateT (List (TapeCell F)) (OracleComp (replaySpec F))) :=
  fun i xs =>
    let r := pop (familyTag i) (0, 0, 0) xs
    if r.1 then pure (decodeReply i r.2.1, r.2.2)
    else (fun reply => (reply, xs)) <$> ((replaySpec F).query i : OracleComp (replaySpec F) _)

variable [Zero F]

theorem oracle_refines (i : (replaySpec F).Domain) : StateRefines toSeed (oracle i) (seededOracle i) := by
  intro xs
  have hv := values_pop i (0, (0 : F), 0) xs
  cases hf : (pop (familyTag i) (0, (0 : F), 0) xs).1 with
  | false =>
      have hv' : toSeed xs i = [] := by simpa [toSeed, hf] using hv
      rw [seededOracle.run_nil hv']
      simp [oracle, hf, StateT.run, Functor.map_map]
  | true =>
      have hv' : toSeed xs i = decodeReply i (pop (familyTag i) (0, (0 : F), 0) xs).2.1 ::
          values i (pop (familyTag i) (0, (0 : F), 0) xs).2.2 := by
        simpa [toSeed, hf] using hv
      rw [seededOracle.run_cons hv']
      simp only [oracle, hf, ite_true, StateT.run, map_pure, toSeed_pop]

theorem simulate_refines {A : Type} (main : OracleComp (replaySpec F) A) :
    StateRefines toSeed (simulateQ oracle main) (simulateQ seededOracle main) := by
  induction main using OracleComp.inductionOn with
  | pure x => exact StateRefines.pure toSeed x
  | query_bind i next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact StateRefines.bind toSeed (oracle_refines i) ih

theorem run'_eq {A : Type} (main : OracleComp (replaySpec F) A) (xs : List (TapeCell F)) :
    (simulateQ oracle main).run' xs = (simulateQ seededOracle main).run' (toSeed xs) := by
  have h := congrArg (Functor.map Prod.fst) (simulate_refines main xs)
  simpa only [Functor.map_map, StateT.run', StateT.run] using h

theorem familyTag_encode (i : (replaySpec F).Domain) (answer : (replaySpec F).Range i) :
    (encodeReply i answer).1 = familyTag i := by
  rcases i with (n | ⟨⟩) | ⟨⟩ <;> rfl

theorem values_encode_cons (i j : (replaySpec F).Domain) (answer : (replaySpec F).Range i)
    (xs : List (TapeCell F)) :
    values j (encodeReply i answer :: xs) =
      if h : j = i then h.symm ▸ (answer :: values i xs) else values j xs := by
  by_cases h : j = i
  · subst j; simp [values, familyTag_encode, decode_encode]
  · have ht : familyTag i ≠ familyTag j := fun ht => h (familyTag_injective ht).symm
    simp [values, familyTag_encode, ht, h]

end Signatures.Runtime.Schnorr.SeedTape
