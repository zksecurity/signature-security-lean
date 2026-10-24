import Proofs.Runtime.AGMExecution
import Proofs.Runtime.AGMExtractionRefinement

/-! Exact native semantics of the compiled simulation/extraction phases. Canonical private
tables are interpreted through the supplied equivalences. The source runs at the provided
public key; the bad setup must provide kappa*g2, not the DLog challenge's X2. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.AGM

variable {F G₁ G₂ K M I N : Type} [Field F] [SampleableType F] [Fintype I] [DecidableEq I]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  {indexTy messageTy : Ty CryptoAtom}
  [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
  {cost : PrimitiveCosts}
  {index : indexTy.Value (cryptoBase F G₁ G₂ K M) ≃ I}
  {message : messageTy.Value (cryptoBase F G₁ G₂ K M) ≃ N}
  {randomBound localTime gammaLength xiLength : Nat} {queries : Fin 3 → Nat}
  {adv : Model.LazyAGM.Adversary F I N G₁ G₂}

omit [DecidableEq I] in
theorem SourceCertificate.goodSimulation_erase
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : I → N → F)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value = w (index i) (message m))
    (rho : I → F) (g X : G₁) (pk : G₂) :
    (fun z => (decodeOutput message z.1.value, transcriptView index message z.2.2)) <$>
      (((cert.code.inline (machineRoutines (goodHash eq) (goodSign weight) randomBound)).run
        (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (goodConfig indexTy)))
        (pk, cert.data, ())).run ((g, X, canonicalKeys fun i => (index.symm i, rho i)), [], [])) =
      Model.LazyAGM.fixedRun adv pk (fun i => rho i • g) (fun m => (∑ i, rho i * w i m) • X) := by
  have h := cert.simulation_erase sampling (goodHash eq) (goodSign weight)
    (fun cfg i => (goodHash eq).denote (arithmetic F G₁ G₂ K M cost) (index.symm i, cfg, ()))
    (fun cfg m => (goodSign weight).denote (arithmetic F G₁ G₂ K M cost) (message.symm m, cfg, ()))
    (by intro cfg i; simp only [Equiv.symm_apply_apply])
    (by intro cfg m; simp only [Equiv.symm_apply_apply])
    (g, X, canonicalKeys fun i => (index.symm i, rho i)) pk
  have hh (i : I) : (goodHash eq).denote (arithmetic F G₁ G₂ K M cost)
      (index.symm i, (g, X, canonicalKeys fun j => (index.symm j, rho j)), ()) = rho i • g := by
    simpa only [Expr.run_value] using
      goodHash_native cost eq heq index.symm index.symm.injective rho g X i
  have hs (m : N) : (goodSign weight).denote (arithmetic F G₁ G₂ K M cost)
      (message.symm m, (g, X, canonicalKeys fun j => (index.symm j, rho j)), ()) =
      (∑ i, rho i * w i m) • X := by
    have h := goodSign_native cost weight index.symm rho g X (message.symm m)
    simpa only [hw, Equiv.apply_symm_apply, Expr.run_value] using h
  simpa only [hh, hs] using h

omit [DecidableEq I] in
theorem SourceCertificate.badSimulation_erase
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : I → N → F)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value = w (index i) (message m))
    (H : I → G₁) (kappa : F) (pk : G₂) :
    (fun z => (decodeOutput message z.1.value, transcriptView index message z.2.2)) <$>
      (((cert.code.inline (machineRoutines (badHash eq) (badSign weight) randomBound)).run
        (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
        (pk, cert.data, ())).run ((kappa, canonicalKeys fun i => (index.symm i, H i)), [], [])) =
      Model.LazyAGM.fixedRun adv pk H (fun m => kappa • ∑ i, w i m • H i) := by
  have h := cert.simulation_erase sampling (badHash eq) (badSign weight)
    (fun cfg i => (badHash eq).denote (arithmetic F G₁ G₂ K M cost) (index.symm i, cfg, ()))
    (fun cfg m => (badSign weight).denote (arithmetic F G₁ G₂ K M cost) (message.symm m, cfg, ()))
    (by intro cfg i; simp only [Equiv.symm_apply_apply])
    (by intro cfg m; simp only [Equiv.symm_apply_apply])
    (kappa, canonicalKeys fun i => (index.symm i, H i)) pk
  have hh (i : I) : (badHash eq).denote (arithmetic F G₁ G₂ K M cost)
      (index.symm i, (kappa, canonicalKeys fun j => (index.symm j, H j)), ()) = H i := by
    simpa only [Expr.run_value] using
      badHash_native cost eq heq index.symm index.symm.injective H kappa i
  have hs (m : N) : (badSign weight).denote (arithmetic F G₁ G₂ K M cost)
      (message.symm m, (kappa, canonicalKeys fun j => (index.symm j, H j)), ()) =
      kappa • ∑ i, w i m • H i := by
    have h := badSign_native cost weight index.symm H kappa (message.symm m)
    simpa only [hw, Equiv.apply_symm_apply, Expr.run_value] using h
  simpa only [hh, hs] using h

theorem SourceCertificate.goodExecution_erase
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : I → N → F)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value = w (index i) (message m))
    (rho : I → F) (g X : G₁) (pk : G₂) :
    (fun z => z.1.value) <$>
      (((goodExecution eq weight cert.code).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (goodConfig indexTy)))
        (pk, cert.data, canonicalKeys (fun i => (index.symm i, rho i)), ())).run
        ((g, X, canonicalKeys fun i => (index.symm i, rho i)), [], [])) =
      (fun p => goodResult w rho p.1 p.2) <$>
        Model.LazyAGM.fixedRun adv pk (fun i => rho i • g) (fun m => (∑ i, rho i * w i m) • X) := by
  have h := congrArg (Functor.map (fun p => goodResult w rho p.1 p.2))
    (cert.goodSimulation_erase sampling eq heq weight w hw rho g X pk)
  rw [goodExecution_run]
  simp only [bind_pure_comp]
  simp only [goodExtract_native (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost index message eq heq weight w hw]
  simpa only [Functor.map_map, Function.comp_def] using h

omit [DecidableEq I] in
theorem SourceCertificate.badExecution_erase
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : I → N → F)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value = w (index i) (message m))
    (a b : I → F) (H : I → G₁) (kappa : F) (pk : G₂) :
    (fun z => z.1.value) <$>
      (((badExecution eq weight cert.code).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
        (pk, cert.data, canonicalKeys (fun i => (index.symm i, a i)),
          canonicalKeys (fun i => (index.symm i, b i)), ())).run
        ((kappa, canonicalKeys fun i => (index.symm i, H i)), [], [])) =
      (fun p => badResult w a b p.1 p.2) <$>
        Model.LazyAGM.fixedRun adv pk H (fun m => kappa • ∑ i, w i m • H i) := by
  have h := congrArg (Functor.map (fun p => badResult w a b p.1 p.2))
    (cert.badSimulation_erase sampling eq heq weight w hw H kappa pk)
  rw [badExecution_run]
  simp only [bind_pure_comp]
  simp only [badExtract_native (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost index message weight w hw]
  simpa only [Functor.map_map, Function.comp_def] using h

end Signatures.Runtime.AGM
