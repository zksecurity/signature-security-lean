import Signatures.OOPS.Spec.LazyAGM
import Signatures.OOPS.Proofs.Adaptive
import Signatures.BLS.Proofs.Nondegeneracy
import Signatures.Proximity.Proofs.LazyAGM
import Mathlib.Algebra.Field.ZMod

/-! Degree, freshness, token, and collision-event boundaries of the lazy games. -/

open OracleComp Model.LazyAGM

namespace SignaturesTest.GameBoundaries

open AlgebraicGroupModel.LinFunctional

-- These hold for any distribution of adaptive transcripts, including the lazy games.
-- Symbolic collision means every coefficient vanishes, not that sampled hashes coincide.
example {F M : Type} [Field F] [DecidableEq M]
    (experiment : ProbComp (DynForgery F M M)) :
    Pr[fun fo => fo.Fresh ∧ ∀ k, dynDenomCoeff BLS.Proofs.indicatorWeight fo k = 0 |
      experiment] = 0 := by
  apply probEvent_eq_zero
  intro fo _ h
  exact BLS.Proofs.fresh_coefficient fo h.1 (h.2 fo.2.mstar)

-- The OOPS degree rule is part of winning, not an assumed property of the adversary.
example {F T : Type} [Field F] [DecidableEq F] [DecidableEq T] (d : ℕ)
    (experiment : ProbComp (DynForgery F (F × T) (T × Fin (d + 1)))) :
    Pr[fun fo => (OOPS.Handle.targetMessages fo.2.v fo.2.mstar.2).card ≤ d ∧
      fo.Fresh ∧ ∀ k, dynDenomCoeff (OOPS.Handle.oopsWMulti d) fo k = 0 |
      experiment] = 0 := by
  apply probEvent_eq_zero
  intro fo _ h
  obtain ⟨j, hj⟩ := OOPS.Handle.forgery_coeff_ne_zero_multi
    fo.2.v fo.2.mstar fo.2.ξ h.1 h.2.1
  exact hj (h.2.2 (fo.2.mstar.2, j))

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def signedMessages : List (ZMod 5 × Bool) :=
  [(1, true), (1, true), (2, false), (3, false)]

-- Repetition and other topics do not consume the final target topic's degree budget.
example : OOPS.LazyAGM.admissible 1 (2, true) signedMessages := by
  unfold OOPS.LazyAGM.admissible
  decide +kernel
example : ¬ OOPS.LazyAGM.admissible 1 (4, false) signedMessages := by
  unfold OOPS.LazyAGM.admissible
  decide +kernel

-- Freshness checks the complete message/topic pair.
example : ((1, true) : ZMod 5 × Bool) ∈ signedMessages := by decide
example : ((1, false) : ZMod 5 × Bool) ∉ signedMessages := by decide
example : tokenCoeff ([2] : List (ZMod 5)) 1 = 0 := by decide

-- In dimension zero every fresh output has colliding vectors.
example {F : Type} [Field F] (fo : AlgebraicGroupModel.LinFunctional.DynForgery F
    ((Fin 0 → F) × Bool) (Option (Fin 0) × Bool)) :
    ¬ Proximity.Proofs.Noncollision fo := by
  intro h
  apply h
  funext k
  exact Fin.elim0 k

private def keyOutput (pk : ZMod 5 × ZMod 5) : Output (ZMod 5) ((Fin 1 → ZMod 5) × Unit) where
  mstar := (fun _ => if pk.2 = 0 then 1 else 0, ())
  β := 0
  γ := []
  ξ := []

private def keyProbe : Adversary (ZMod 5) (Option (Fin 1) × Unit)
    ((Fin 1 → ZMod 5) × Unit) (ZMod 5) (ZMod 5 × ZMod 5) where
  main pk := pure (keyOutput pk)

-- The measured probability uses generated keys, including the zero key.
example : 𝒟[Proximity.LazyAGM.collisionGame ((1, 0) : ZMod 5 × ZMod 5) keyProbe] {true} = 0 := by
  rw [Proximity.LazyAGM.Proofs.collision_eq_realGame]
  simp [AlgebraicGroupModel.LinFunctional.realGameDynAdaptive, Model.LazyAGM.Proofs.extracted,
    fixedRun, fixedImpl, keyProbe, keyOutput, Model.LazyAGM.Proofs.toForgery,
    Proximity.Proofs.Noncollision, probEvent_bind_eq_tsum]
  intro _ h
  exact one_ne_zero (congrFun h 0)

-- A key outside that image can produce a fresh colliding output.
example :
    let z := (keyOutput (0, 1),
      (([], []) : Transcript (Option (Fin 1) × Unit) ((Fin 1 → ZMod 5) × Unit) (ZMod 5)))
    z ∈ support (run Proximity.LazyAGM.terms 0 keyProbe (0, 1)) ∧
      z.1.mstar ∉ z.2.2.map Prod.fst ∧
      z.1.mstar.1 = fun k => (z.2.2.mapIdx fun n q => tokenCoeff z.1.ξ n * q.1.1 k).sum := by
  simp [run, keyProbe, keyOutput]

private def vectorOutput (x : ZMod 5) (coeff : List (ZMod 5)) :
    Output (ZMod 5) ((Fin 1 → ZMod 5) × Bool) := ⟨(fun _ => x, true), 0, [], coeff⟩

-- Repeated signing calls contribute separately to the linear combination.
example : Proximity.LazyAGM.Collision (vectorOutput 2 [1, 1])
    [(fun _ => 1, true), (fun _ => 1, true)] := by
  unfold Proximity.LazyAGM.Collision vectorOutput
  decide +kernel

-- Other slots still contribute to the vector relation; freshness uses the complete pair.
example : Proximity.LazyAGM.Collision (vectorOutput 2 [2]) [(fun _ => 1, false)] := by
  unfold Proximity.LazyAGM.Collision vectorOutput
  decide +kernel

-- A repeated vector/slot output is not a fresh collision, even when its relation matches.
example : ¬ Proximity.LazyAGM.Collision (vectorOutput 1 [1]) [(fun _ => 1, true)] := by
  unfold Proximity.LazyAGM.Collision vectorOutput
  decide +kernel

-- Missing coefficients are zero, not an arbitrary witness of a linear relation.
example : ¬ Proximity.LazyAGM.Collision (vectorOutput 2 []) [(fun _ => 1, false)] := by
  unfold Proximity.LazyAGM.Collision vectorOutput
  decide +kernel

private def zeroProbe : Adversary (ZMod 5) (Option (Fin 1) × Bool)
    ((Fin 1 → ZMod 5) × Bool) (ZMod 5) (ZMod 5) where
  main _ := pure (vectorOutput 0 [])

-- The collision term need not be small: a fresh zero-vector output collides with the empty sum.
example : 𝒟[Proximity.LazyAGM.collisionGame (1 : ZMod 5) zeroProbe] {true} = 1 := by
  rw [Proximity.LazyAGM.Proofs.collision_eq_realGame]
  simp [AlgebraicGroupModel.LinFunctional.realGameDynAdaptive, Model.LazyAGM.Proofs.extracted,
    fixedRun, fixedImpl, zeroProbe, vectorOutput, Model.LazyAGM.Proofs.toForgery,
    Proximity.Proofs.Noncollision, AlgebraicGroupModel.LinFunctional.DynForgery.Fresh]
  rintro _ _ _ _ _ _ rfl rfl rfl rfl
  simp

example {F S : Type} [Semiring F] (out : Output F ((Fin 0 → F) × S)) (signed) :
    Proximity.LazyAGM.Collision out signed ↔ out.mstar ∉ signed := by
  exact ⟨And.left, fun h => ⟨h, funext fun k => Fin.elim0 k⟩⟩

end SignaturesTest.GameBoundaries
