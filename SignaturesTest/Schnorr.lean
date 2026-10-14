import Signatures.Schnorr.Proofs.ROM
import Signatures.Runtime.Schnorr
import VCVio.CryptoFoundations.ReplayForkCost
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Schnorr query, cache, extraction, and probability-theorem regressions. -/

open OracleComp OracleSpec

section QueryCaps

variable {F G M : Type}

-- The nested sum distinguishes hash and signing calls; neither can spend the other's cap.
example (m : M) (R : G) : FiatShamir.signHashQueryBound (M := M)
    (oa := OracleComp.queryBind (spec := Schnorr.ROM.advSpec F G M)
      (.inl (.inr (m, R))) (fun _ => pure ())) 0 1 := by
  exact ⟨⟨Or.inl (by simp), fun _ => trivial⟩,
    ⟨Or.inr (by decide), fun _ => trivial⟩⟩

example (m : M) : FiatShamir.signHashQueryBound (M := M)
    (oa := OracleComp.queryBind (spec := Schnorr.ROM.advSpec F G M)
      (.inr m) (fun _ => pure ())) 1 0 := by
  exact ⟨⟨Or.inr (by decide), fun _ => trivial⟩,
    ⟨Or.inl (by simp), fun _ => trivial⟩⟩

end QueryCaps

section Cache

variable {M G F : Type} [DecidableEq M] [DecidableEq G] [SampleableType F]

-- An existing message/commitment query reuses its scalar, without another sample.
example (m : M) (R : G) (c : F) (cache : (M × G →ₒ F).QueryCache)
    (hc : cache (m, R) = some c) :
    ((M × G →ₒ F).randomOracle (m, R)).run cache = pure (c, cache) := by
  rw [randomOracle.run_eq, hc]

end Cache

section Extraction

open Signatures.Runtime

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

-- Zero is a valid secret: extraction does not assume an invertible secret key.
example : (Schnorr.extract.run (arithmetic F F F Unit Unit PrimitiveCosts.unit)
    (2, 2, 1, 3, ())).value = 0 := by
  rw [Schnorr.extract_run]
  simp

-- Division in Lean is total. Without the unequal-challenge guard the result need not
-- be the secret: this pair is one accepting transcript repeated, for secret one.
example : (2 : F) = 1 + 1 * 1 := by decide
example : (Schnorr.extract.run (arithmetic F F F Unit Unit PrimitiveCosts.unit)
    (2, 2, 1, 1, ())).value ≠ (1 : F) := by
  rw [Schnorr.extract_run]
  simp

end Extraction

-- A source-bound certificate for query calls also bounds rejected replay attempts.
example {I A : Type} [DecidableEq I] {spec : OracleSpec I}
    [∀ i, DecidableEq (spec.Range i)] (main : OracleComp spec A)
    (budgets : I → Nat) (target : I) (select : A → Option (Fin (budgets target + 1)))
    (p : I → Prop) [DecidablePred p] (n : Nat) (h : IsQueryBoundP main p n) :
    IsQueryBoundP (contextFork main budgets target select) p (n + n) :=
  isQueryBoundP_contextFork p main budgets target select n h

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``Schnorr.ROM.Proofs.security, ``Schnorr.signature_complete,
      ``Signatures.Runtime.Schnorr.extract_sound, ``Signatures.Runtime.Schnorr.extract_run,
      ``Signatures.Runtime.Schnorr.simulatedCommit_run] do
    let axioms ← collectAxioms name
    let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
    unless axioms.all allowed.contains do
      throwError "{name}: unexpected axiom footprint {axioms}"
