import Proofs.Schnorr.LazyROMReduction
import Proofs.Schnorr.FixedTapeExtraction
import Proofs.Runtime.FiniteQueryCover
import Mathlib.Data.Finset.Sum

/-! Derive the reference experiment's finite seed cover from the ordinary
Schnorr adversary and its hash allowance. The cover is used only in proofs;
its cardinality is not a runtime bound for the lazy reduction. -/

open OracleComp OracleSpec DiffieHellman

namespace Schnorr.LazyROM

variable {F G M : Type} [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [DecidableEq M]

/-- The final verification lookup contributes the single extra hash slot.
Private uniform draws and signing simulation do not increase this count. -/
theorem main_hashBound (g pk : G) (adv : ROM.Adversary (F := F) (M := M) g)
    (qS qH : Nat)
    (queries : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH) :
    IsQueryBoundP (main g pk adv) (· = Sum.inr ()) (qH + 1) := by
  have before := FiatShamir.Stateful.nmaAdvFromCma_nmaHashQueryBound
    (Schnorr.sigma F G g) (dlogGenerable F g) M adv
    (Schnorr.simTranscript F G g) qS qH queries pk
  have finalQuery : FiatShamir.nmaHashQueryBound (M := M)
      (oa := (FiatShamir.cmaToNmaAdv (Schnorr.sigma F G g) (dlogGenerable F g) M
        (Schnorr.simTranscript F G g) adv).main pk) (qH + 1) := by
    apply isQueryBoundP_bind before
    intro result _
    simp
  unfold main FiatShamir.Fork.runTrace
  refine isQueryBoundP_bind (n := qH + 1) (m := 0) ?_ ?_
  swap
  · rintro ⟨⟨forgery, advCache⟩, roCache, log⟩ _
    simp
  apply finalQuery.simulateQ_run_of_step
  · intro i hi state
    rcases i with n | mc
    · simp at hi
    · rcases state with ⟨cache, log⟩
      simp only [QueryImpl.add_apply_inr]
      cases hcache : cache mc with
      | none =>
          rw [FiatShamir.Fork.roImpl_run_none (M := M) (Commit := G) (Chal := F)
            mc cache log hcache]
          simp [FiatShamir.Fork.wrappedChallengeQuery]
      | some answer =>
          rw [FiatShamir.Fork.roImpl_run_some (M := M) (Commit := G) (Chal := F)
            mc cache log answer hcache]
          simp
  · intro i hi state
    rcases i with n | mc
    · simp [QueryImpl.add_apply_inl, FiatShamir.Fork.unifForward_run,
        FiatShamir.Fork.wrappedUniformQuery]
    · simp at hi

/-- The finite field and generating point imply finitely many public keys.
Together with finite reply branching this gives one proof-only seed cover for
all keys, while the hash coordinate retains its actual `qH + 1` allowance. -/
theorem exists_seed_bound [Fintype F] (g : G)
    (generates : Function.Bijective (fun x : F => x • g))
    (adv : ROM.Adversary (F := F) (M := M) g) (qS qH : Nat)
    (queries : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH) :
    ∃ (privateFamilies : List Nat) (qR : Nat), ∀ pk,
      IsPerIndexQueryBound (main g pk adv)
        (FixedTape.finiteBounds privateFamilies qR (qH + 1)) := by
  classical
  let : Finite G := Finite.of_surjective (fun x : F => x • g) generates.2
  let : ∀ i, Finite ((FixedTape.Spec F).Range i) := fun i => by
    cases i <;> infer_instance
  obtain ⟨families, qR, bounded⟩ :=
    Signatures.Runtime.FiniteQueryCover.exists_bound_family (fun pk => main g pk adv)
  refine ⟨families.toLeft.toList, qR, fun pk => ?_⟩
  apply (Signatures.Runtime.FiniteQueryCover.replace_bound (main g pk adv) _ (.inr ())
    (qH + 1) (bounded pk) (main_hashBound g pk adv qS qH queries)).mono
  intro i
  rcases i with n | ⟨⟩ <;> simp [FixedTape.finiteBounds]

end Schnorr.LazyROM
