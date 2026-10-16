import Signatures.BLS.CoCDH.Proofs.QueryBound

/-! Signing-only budgets must ignore randomness, hash queries, and the final verification hash. -/

open BLS.ROM

open OracleComp OracleSpec BLS.CoCDH.Tight

namespace SignaturesTest.CoronBudget

-- Zero signing queries must not make the multiplicative bound infinite or vacuous.
example : Model.coronFactor 0 = 1 := by simp [Model.coronFactor]

private def repeatedSigning : OracleComp (advSpec Nat Nat) (Nat × Nat) := do
  let a : Nat ← liftM ((advSpec Nat Nat).query (.inr 7))
  let b : Nat ← liftM ((advSpec Nat Nat).query (.inr 7))
  pure (8, a + b)

private def hashesAndRandomness : OracleComp (advSpec Nat Nat) (Nat × Nat) := do
  let _ ← liftM ((advSpec Nat Nat).query (.inl (.inl 4)))
  let a : Nat ← liftM ((advSpec Nat Nat).query (.inl (.inr 7)))
  let b : Nat ← liftM ((advSpec Nat Nat).query (.inl (.inr 8)))
  pure (8, a + b)

example : IsQueryBoundP repeatedSigning (fun i => Sum.isRight i = true) 2 := by
  simp [repeatedSigning]

example : ¬ IsQueryBoundP repeatedSigning (fun i => Sum.isRight i = true) 1 := by
  simp [repeatedSigning]

example : IsQueryBoundP hashesAndRandomness (fun i => Sum.isRight i = true) 0 := by
  simp [hashesAndRandomness]

example : IsQueryBoundP (cacheForgery hashesAndRandomness)
    (fun i => Sum.isRight i = true) 0 := by
  simp [cacheForgery, hashesAndRandomness]

-- Generated keys need not cover G₂: the second coordinate here is always zero.
private def keyDependent {F : Type} [Field F] [DecidableEq F] : AdversaryPK Nat Nat (F × F) :=
  fun pk => if pk.2 = 0 then hashesAndRandomness else repeatedSigning

example {F : Type} [Field F] [DecidableEq F] (x : F) :
    IsQueryBoundP (keyDependent (x • ((1, 0) : F × F)))
      (fun i => Sum.isRight i = true) 0 := by
  simp [keyDependent, hashesAndRandomness]

example {F : Type} [Field F] [DecidableEq F] :
    ¬ (∀ pk : F × F, IsQueryBoundP (keyDependent pk)
      (fun i => Sum.isRight i = true) 0) := by
  intro h
  simpa [keyDependent, repeatedSigning] using h (0, 1)

-- Cache hits draw no new randomness; misses sample once without changing prior signing history.
example : (BLS.ROM.Internal.getDlogS (F := Fin 5) 7).run ((fun _ : Nat => some 2), {3}) =
    pure (2, (fun _ => some 2), {3}) := by
  rw [getDlogS_run]

example : (BLS.ROM.Internal.getDlogS (F := Fin 5) 7).run ((fun _ : Nat => none), {3}) =
    (do let ρ ← ($ᵗ (Fin 5) : ProbComp (Fin 5))
        pure (ρ, Function.update (fun _ => none) 7 (some ρ), {3})) := by
  rw [getDlogS_run]

end SignaturesTest.CoronBudget
