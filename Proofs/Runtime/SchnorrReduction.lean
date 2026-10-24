import Proofs.Runtime.SchnorrTrace

/-! Exact correspondence between the costed replay machine and Schnorr's reduction. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr

attribute [local implicit_reducible] FiatShamir.nmaForkBudget

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

omit [SampleableType F] in
theorem selectPass_trace (cost : PrimitiveCosts) (qH : Nat)
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) :
    selectPass cost qH p = FiatShamir.Fork.forkPoint G₁ F F M qH (cacheTrace p) := by
  unfold selectPass
  rw [selectionRun_value]
  exact selectValue_forkPoint _ _ _ _ _ _ _

variable [SampleableType G₁]

omit [Field F] [SampleableType F] [DecidableEq F] in
theorem liftRandom_eq_liftComp {A : Type} (main : ProbComp A) :
    liftRandom (F := F) main = liftComp main (expandedSpec F) := by
  induction main using OracleComp.inductionOn with
  | pure value => simp [liftRandom, liftComp]
  | query_bind n next ih =>
    have hq : (liftM (unifSpec.query n) : OracleComp (expandedSpec F) _) =
        liftM ((expandedSpec F).query (.inl n)) := by
      rw [OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query]
    simpa only [liftRandom, liftComp, simulateQ_bind, simulateQ_spec_query, hq] using
      congrArg (fun k : Fin (n + 1) → OracleComp (expandedSpec F) A =>
        (liftM ((expandedSpec F).query (.inl n)) : OracleComp (expandedSpec F) _) >>= k) (funext ih)

omit [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] in
theorem extractFork_trace (g : G₁)
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (hfirst : (listQueryCache first.2.2.2) (first.1.1.1, first.1.1.2.1) = some first.1.2)
    (hsecond : (listQueryCache second.2.2.2) (second.1.1.1, second.1.1.2.1) = some second.1.2) :
    liftRandom (extractFork (some (first, second))) =
      FiatShamir.nmaForkExtractBranch (M := M) (_root_.Schnorr.sigma F G₁ g)
        (some (cacheTrace first, cacheTrace second)) := by
  simp only [FiatShamir.nmaForkExtractBranch, cacheTrace, nativeTrace, nativeRepr,
    liveState, hfirst, hsecond, extractFork, extractValues]
  by_cases hc : first.1.1.2.1 = second.1.1.2.1 <;>
    by_cases hd : first.1.2 = second.1.2 <;>
    simp [hc, hd, _root_.Schnorr.sigma, liftRandom_eq_liftComp, div_eq_mul_inv]

theorem expandedFork_extract (cost : PrimitiveCosts) {dataTy} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) (g pk : G₁) (qH : Nat) :
    (contextFork (simulateQ (Replay.expandPrivate privateImpl)
      ((macroPass cost randomBound code (pk, data, ())).run ((g, pk), [], [])))
      (fun _ => qH) (.inr ()) (selectPass cost qH) >>= fun p => liftRandom (extractFork p)) =
    (contextFork (cacheTrace <$> simulateQ (Replay.expandPrivate privateImpl)
      ((macroPass cost randomBound code (pk, data, ())).run ((g, pk), [], [])))
      (FiatShamir.nmaForkBudget qH) (.inr ()) (FiatShamir.Fork.forkPoint G₁ F F M qH) >>=
      FiatShamir.nmaForkExtractBranch (M := M) (_root_.Schnorr.sigma F G₁ g)) := by
  rw [Replay.contextFork_map]
  have hs : (FiatShamir.Fork.forkPoint G₁ F F M qH ∘
      cacheTrace (G₂ := G₂) (K := K)) = selectPass cost qH := by
    funext p
    exact (selectPass_trace cost qH p).symm
  rw [hs, bind_map_left]
  have hb (main : OracleComp (expandedSpec F) (cachePassOutput.Value (cryptoBase F G₁ G₂ K M))) :
      contextFork main (FiatShamir.nmaForkBudget qH) (.inr ()) (selectPass cost qH) =
      contextFork main (fun _ => qH) (.inr ()) (selectPass cost qH) := by
    rw [← Replay.loggedFork_eq_contextFork, ← Replay.loggedFork_eq_contextFork]
    simp only [Replay.loggedFork, FiatShamir.nmaForkBudget]
    congr 1
    funext first
    cases selectPass cost qH first.1 with
    | none => rfl
    | some index =>
      cases Replay.splitBefore (Sum.inr ()) index first.2 with
      | none => rfl
      | some prior =>
        congr 1
  rw [hb]
  apply bind_congr_of_forall_mem_support
  intro result hr
  cases result with
  | none => rfl
  | some pair =>
    obtain ⟨hfirst, hsecond⟩ := Replay.contextFork_outputs _ _ _ _ hr
    exact extractFork_trace g pair.1 pair.2
      (macroPass_valid cost randomBound code (pk, data, ()) g pk [] [] pair.1 hfirst).2
      (macroPass_valid cost randomBound code (pk, data, ()) g pk [] [] pair.2 hsecond).2

theorem SourceCertificate.reduction {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    {randomBound localTime : Nat} {queries : Fin 3 → Nat} (g : G₁)
    {adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g}
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (pk : G₁) (qH : Nat) :
    Run.value <$> (forkCode randomBound cert.code).run cost sampling (pk, g, qH, cert.data, ()) =
      _root_.Schnorr.dlogReduction F G₁ g M adv qH g pk := by
  rw [forkCode_context]
  have he := congrArg (simulateQ (sampleExpanded (F := F)))
    (expandedFork_extract cost randomBound cert.code cert.data g pk qH)
  simp only [simulateQ_bind, sampleExpanded_liftRandom] at he
  rw [he, cert.trace]
  rw [← simulateQ_bind]
  unfold _root_.Schnorr.dlogReduction FiatShamir.cmaReduction FiatShamir.nmaReduction
  congr 1
  funext i
  cases i <;> rfl

/-- Complete two-pass bound, including source work, caches, replay tape, scans,
verification, extraction, fallback sampling, and loading fixed data. -/
def SourceCertificate.targetBudget {cost : PrimitiveCosts} {randomBound localTime : Nat}
    {queries : Fin 3 → Nat} {adv}
    (cert : SourceCertificate (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      cost randomBound localTime queries adv)
    (sampling : Machine.SamplingCosts) (qH : Nat) : Nat :=
  forkPrice cost sampling randomBound localTime queries +
    (cert.dataTy.load cert.data).steps + qH + 9

/-- Fixed-generator DLog algorithms implemented by the general closed machine. -/
def dlogWithin (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g : G₁) (budget : Nat) (solver : DiffieHellman.DLogAdversary F G₁) : Prop :=
  Machine.Within (G₂ := G₂) (K := K) (M := M) cost sampling [point₁] scalar budget
    (fun env => solver g env.1)

theorem SourceCertificate.within {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    {randomBound localTime : Nat} {queries : Fin 3 → Nat} (g : G₁)
    {adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g}
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (qH : Nat) :
    dlogWithin (G₂ := G₂) (K := K) (M := M) cost sampling g (cert.targetBudget sampling qH)
      (_root_.Schnorr.dlogReduction F G₁ g M adv qH) := by
  refine ⟨forkPackage randomBound cert.code g qH cert.data, ?_, ?_⟩
  · rintro ⟨pk, _⟩
    rw [Machine.Package.run_eq]
    simpa only [Functor.map_map, forkPackage, Env.append] using
      cert.reduction sampling g pk qH
  · rintro ⟨pk, _⟩ out hout
    have hb := forkPackage_bound cost sampling randomBound cert.code pk g qH cert.data
      localTime queries (cert.budget pk) out hout
    dsimp only [SourceCertificate.targetBudget, Env.load, Ty.load, point₁] at hb ⊢
    omega

end Signatures.Runtime.Schnorr
