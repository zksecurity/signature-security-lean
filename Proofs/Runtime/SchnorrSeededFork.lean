import Proofs.Runtime.SchnorrSeedReachability
import Proofs.Runtime.SeededReplay
import Proofs.Schnorr.FixedTapeExtraction

/-! A complete fixed-private-tape fork of the typed source simulation. Its
family list, seed coverage, and selector reachability are derived from source
syntax and its resource certificate. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.Seeded

def capacity (localTime : Nat) (queries : Fin 3 → Nat) (qH : Nat) : Nat :=
  max (sourceSeedCapacity localTime queries) qH

def budget {randomBound Γ a} (code : Program CryptoOp (Command randomBound) Γ a)
    (localTime : Nat) (queries : Fin 3 → Nat) (qH : Nat) : (Nat ⊕ Unit) ⊕ Unit → Nat := by
  letI : BEq ((Nat ⊕ Unit) ⊕ Unit) := instBEqOfDecidableEq
  exact fun i => if i ∈ sourceFamilies code then capacity localTime queries qH else 0

theorem target_le {randomBound Γ a} (code : Program CryptoOp (Command randomBound) Γ a)
    (localTime : Nat) (queries : Fin 3 → Nat) (qH : Nat) :
    qH ≤ budget code localTime queries qH (.inr ()) := by
  simp only [budget, sourceFamilies, List.mem_cons_self, ite_true]
  exact Nat.le_max_right _ _

theorem budget_cover {randomBound Γ a} (code : Program CryptoOp (Command randomBound) Γ a)
    (localTime : Nat) (queries : Fin 3 → Nat) (qH : Nat) (i)
    (hi : 0 < budget code localTime queries qH i) : i ∈ sourceFamilies code := by
  classical
  by_contra h
  simp [budget, h] at hi

instance unifSubSpec (F : Type) : unifSpec ⊂ₒ replaySpec F :=
  SubSpec.trans (inferInstance : unifSpec ⊂ₒ privateSpec F)
    (inferInstance : privateSpec F ⊂ₒ replaySpec F)

instance lawfulUnifSubSpec (F : Type) : unifSpec ˡ⊂ₒ replaySpec F where
  onResponse_bijective _ := Function.bijective_id

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

abbrev main (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁) :=
  cacheTrace <$> (macroPass cost randomBound code env).run ((g, pk), [], [])

theorem main_bound (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁)
    (localTime : Nat) (queries : Fin 3 → Nat) (qH : Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      code env localTime queries) :
    IsPerIndexQueryBound (main cost randomBound code env g pk) (budget code localTime queries qH) := by
  apply (isPerIndexQueryBound_map_iff _ _ _).2
  apply (macroPass_seedBudget cost randomBound code env localTime queries hsource _).mono
  intro i
  simp only [sourceSeedBudget, budget]
  split
  · exact Nat.le_max_left _ _
  · exact le_rfl

variable [SampleableType F]

/-- The typed scalar tape fixes each simulator draw as a whole, even when its
eventual raw sampler uses several uniform queries. -/
def fork (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁)
    (localTime : Nat) (queries : Fin 3 → Nat) (qH : Nat) :
    OracleComp (replaySpec F) (Option (FiatShamir.Fork.Trace G₁ F F M × FiatShamir.Fork.Trace G₁ F F M)) :=
  seededFork (main cost randomBound code env g pk) (budget code localTime queries qH)
    (sourceFamilies code) (.inr ())
    (Option.map (Fin.castLE (Nat.succ_le_succ (target_le code localTime queries qH))) ∘
      FiatShamir.Fork.forkPoint G₁ F F M qH)

/-- Both executions consume their entire private randomness from the same
seed. Only hash challenges after the selected slot can remain live. -/
theorem replay_live_bound (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁)
    (localTime : Nat) (queries : Fin 3 → Nat) (qH : Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      code env localTime queries)
    (seed : QuerySeed (replaySpec F))
    (hs : seed ∈ support (generateSeed (replaySpec F) (budget code localTime queries qH)
      (sourceFamilies code))) (slot : Fin (qH + 1)) (fresh : F) :
    IsPerIndexQueryBound ((simulateQ seededOracle (main cost randomBound code env g pk)).run' seed) 0 ∧
    IsPerIndexQueryBound ((simulateQ seededOracle (main cost randomBound code env g pk)).run'
      ((seed.takeAtIndex (.inr ()) slot.val).addValue (.inr ()) fresh))
      (Function.update 0 (.inr ()) (budget code localTime queries qH (.inr ()) - (slot.val + 1))) := by
  have hmain := main_bound cost randomBound code env g pk localTime queries qH hsource
  have hcover : ∀ i, budget code localTime queries qH i ≤ (seed i).length := fun i =>
    le_length_of_mem_support_generateSeed_of_covers (replaySpec F) (budget code localTime queries qH)
      (sourceFamilies code) seed i hs (budget_cover code localTime queries qH)
  exact ⟨seededOracle.isPerIndexQueryBound_run'_zero hmain hcover,
    seededOracle.isPerIndexQueryBound_run'_takeAtIndex_addValue (i := Sum.inr ()) hmain hcover
      (slot.castLE (Nat.succ_le_succ (target_le code localTime queries qH))) fresh⟩

theorem fork_support_context (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁)
    (localTime : Nat) (queries : Fin 3 → Nat) (qH : Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      code env localTime queries) {x₁ x₂ : FiatShamir.Fork.Trace G₁ F F M}
    (h : some (x₁, x₂) ∈ support (fork cost randomBound code env g pk localTime queries qH)) :
    some (x₁, x₂) ∈ support (contextFork (main cost randomBound code env g pk)
      (fun _ => qH) (.inr ()) (FiatShamir.Fork.forkPoint G₁ F F M qH)) := by
  have hreach : PathCfReachable (main cost randomBound code env g pk)
      (budget code localTime queries qH) (.inr ())
      (Option.map (Fin.castLE (Nat.succ_le_succ (target_le code localTime queries qH))) ∘
        FiatShamir.Fork.forkPoint G₁ F F M qH) := by
    intro path s hs
    simp only [Function.comp_def, Option.map_eq_some_iff] at hs
    obtain ⟨slot, hs, rfl⟩ := hs
    exact macroPass_forkPoint_reachable cost randomBound code env g pk qH path slot hs
  unfold fork at h
  have hcontext := SeededReplay.seededFork_support_context
    (main cost randomBound code env g pk) (budget code localTime queries qH)
    (sourceFamilies code) (.inr ())
    (Option.map (Fin.castLE (Nat.succ_le_succ (target_le code localTime queries qH))) ∘
      FiatShamir.Fork.forkPoint G₁ F F M qH)
    (main_bound cost randomBound code env g pk localTime queries qH hsource)
    (budget_cover code localTime queries qH) hreach h
  exact SeededReplay.contextFork_support_castLE (main cost randomBound code env g pk)
    (fun _ => qH) (budget code localTime queries qH) (Sum.inr ())
    (target_le code localTime queries qH) (FiatShamir.Fork.forkPoint G₁ F F M qH) hcontext

variable [Fintype F]

local instance : Inhabited F := ⟨0⟩

noncomputable local instance : IsUniformSpec (Unit →ₒ F) :=
  IsUniformSpec.ofFintypeInhabited _

/-- The source-derived seed capacity does not enlarge the number of selectable
fork positions in the Bellare–Neven bound. -/
theorem fork_success_bound (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁)
    (localTime : Nat) (queries : Fin 3 → Nat) (qH : Nat) :
    let acc : ENNReal := ∑ s, Pr[= some s | FiatShamir.Fork.forkPoint G₁ F F M qH <$>
      main cost randomBound code env g pk]
    acc * (acc / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr[fun r => r.isSome | fork cost randomBound code env g pk localTime queries qH] := by
  have hcard : Fintype.card ((replaySpec F).Range (.inr ())) = Fintype.card F :=
    Fintype.card_congr (Equiv.refl F)
  simpa only [fork, hcard, Nat.cast_add, Nat.cast_one] using
    SeededReplay.seededFork_success_bound_labels (main cost randomBound code env g pk)
      (budget code localTime queries qH) (sourceFamilies code) (.inr ())
      (FiatShamir.Fork.forkPoint G₁ F F M qH)
      (Fin.castLE (Nat.succ_le_succ (target_le code localTime queries qH)))
      (Fin.castLE_injective _)

end Signatures.Runtime.Schnorr.Seeded
