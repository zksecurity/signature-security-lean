import Proofs.Schnorr.AGMCacheBound
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.EvalDist.Monad.Disagreement

/-! Honest signing on the reduction's instrumented state. A padded independent
challenge gives an explicit coupling to the simulator, with disagreement only
when the signing nonce hits a cached message/commitment point. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction OracleComp.DeferredSampling
open scoped ENNReal

namespace Schnorr.AGM.Reduction

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

def signingOutput (g pk : G) (s : State F G M) (m : M) (c z : F) :
    Message F (Group G) × State F G M :=
  (signingReply (z • g - c • pk) z, signedState s g pk m c z)

def simulatedSign (g pk : G) (s : State F G M) (m : M) :
    ProbComp (Message F (Group G) × State F G M) := do
  let c ← $ᵗ F
  let z ← $ᵗ F
  pure (signingOutput g pk s m c z)

def nonceSign (g : G) (x : F) (s : State F G M) (m : M) :
    ProbComp (Message F (Group G) × State F G M) := do
  let c ← $ᵗ F
  let r ← $ᵗ F
  pure (signingOutput g (x • g) s m c (r + c * x))

def honestSign (g : G) (x : F) (s : State F G M) (m : M) :
    ProbComp (Message F (Group G) × State F G M) := do
  let c ← $ᵗ F
  let r ← $ᵗ F
  let d := (s.cache (m, r • g)).map Entry.challenge |>.getD c
  pure (signingOutput g (x • g) s m d (r + d * x))

theorem nonceSign_bind {B : Type} (g : G) (x : F) (s : State F G M) (m : M)
    (next : Message F (Group G) × State F G M → ProbComp B) :
    𝒮[nonceSign g x s m >>= next] = 𝒮[simulatedSign g (x • g) s m >>= next] := by
  simp only [nonceSign, simulatedSign, bind_assoc, pure_bind]
  apply evalSPMF_bind_congr_left
  intro c
  simpa only [id_eq] using evalSPMF_bind_bijective_add_right_uniform (α := F) id
    Function.bijective_id (c * x) (fun z => next (signingOutput g (x • g) s m c z))

/-- A common continuation sees identical replies and state off the nonce-collision set.
Different continuations may contribute their own already-proved uniform tail error. -/
theorem honestSign_bind_le [Fintype F] {B : Type}
    (g : G) (hg : Function.Injective (fun r : F => r • g))
    (x : F) (s : State F G M) (m : M) (k : Nat) (hk : CacheBound s k)
    (contL contR : Message F (Group G) × State F G M → ProbComp B)
    (event : B → Prop) (epsilon : ENNReal)
    (hnext : ∀ c z, Pr[event | contL (signingOutput g (x • g) s m c z)] ≤
      Pr[event | contR (signingOutput g (x • g) s m c z)] + epsilon) :
    Pr[event | honestSign g x s m >>= contL] ≤
      Pr[event | simulatedSign g (x • g) s m >>= contR] +
        (k : ENNReal) * (Fintype.card F : ENNReal)⁻¹ + epsilon := by
  rw [← probEvent_congr' (fun _ _ => Iff.rfl) (nonceSign_bind g x s m contR)]
  simp only [honestSign, nonceSign, bind_assoc, pure_bind]
  rw [add_assoc]
  apply probEvent_bind_congr_le_add
  intro c _
  have h := probEvent_bind_le_add_of_disagree
    (mx := ($ᵗ F)) (D := fun r => s.cache (m, r • g) ≠ none)
    (my := fun r => contL (signingOutput g (x • g) s m
      ((s.cache (m, r • g)).map Entry.challenge |>.getD c)
      (r + ((s.cache (m, r • g)).map Entry.challenge |>.getD c) * x)))
    (oc := fun r => contR (signingOutput g (x • g) s m c (r + c * x)))
    (q := event) (ε₁ := (k : ENNReal) * (Fintype.card F : ENNReal)⁻¹)
    (ε₂ := epsilon) (nonce_collision g hg s k hk m) (by
      intro r _ hfresh
      have hc : s.cache (m, r • g) = none := not_not.mp hfresh
      simpa only [hc, Option.map_none, Option.getD_none] using hnext c (r + c * x))
  simpa only [add_assoc] using h

/-- The instrumented honest handler differs only in well-shaped signing calls. -/
def honestHandler (g : G) (x : F) :
    QueryImpl (explainedSpec F (Group G) (Request M) (Reply F M))
      (StateT (State F G M) ProbComp) := by
  intro ⟨⟨request, groups⟩, coeffs⟩
  cases request with
  | random n => exact handler g (x • g) ⟨⟨.random n, groups⟩, coeffs⟩
  | hash m => exact handler g (x • g) ⟨⟨.hash m, groups⟩, coeffs⟩
  | sign m => exact fun (s : State F G M) =>
      if groups () ≠ [] then pure (scalarReply (G := G) (0 : F), rejected s)
      else honestSign (F := F) g x s m

def honestRun (g : G) (x : F) (adv : Adversary F G M) :
    ProbComp ((Bool × F) × State F G M) :=
  (do
    let out ← simulateQ (honestHandler g x) (adv.main (initial g (x • g)))
    finish g (x • g) out).run {}

def honestGame (g : G) (adv : Adversary F G M) : ProbComp Bool := do
  let x ← $ᵗ F
  let p ← honestRun g x adv
  pure p.1.1

end Schnorr.AGM.Reduction
