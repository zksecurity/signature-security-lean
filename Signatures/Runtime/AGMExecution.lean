import Signatures.Runtime.AGMSource

/-! Compiled source execution followed by the actual AGM extractor. The source call frame
contains only the public key and fixed data. Private tables stay in the target's registers
and oracle store. Setup and fixed-data loading are handled by the enclosing package. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.AGM

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
private def v5 {a b c d e f Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: Γ) f :=
  .var (.there (.there (.there (.there (.there .here)))))

variable {indexTy messageTy dataTy : Ty CryptoAtom} {randomBound : Nat}

def goodExecution (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (source : Program CryptoOp (Command indexTy messageTy randomBound)
      [point₂, dataTy] (outputTy messageTy)) :
    Program CryptoOp (Machine.Effect (oracleStore indexTy messageTy (goodConfig indexTy)))
      [point₂, dataTy, tableTy indexTy] scalar :=
  .bind (.call (source.inline (machineRoutines (goodHash eq) (goodSign weight) randomBound))
    (.cons v0 (.cons v1 .nil)))
    (.bind (.query .read .unit)
      (.call (.ret (goodExtract eq weight)) (.cons v1 (.cons (.snd v0) (.cons v4 .nil)))))

def badExecution (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (source : Program CryptoOp (Command indexTy messageTy randomBound)
      [point₂, dataTy] (outputTy messageTy)) :
    Program CryptoOp (Machine.Effect (oracleStore indexTy messageTy (badConfig indexTy)))
      [point₂, dataTy, tableTy indexTy, tableTy indexTy] scalar :=
  .bind (.call (source.inline (machineRoutines (badHash eq) (badSign weight) randomBound))
    (.cons v0 (.cons v1 .nil)))
    (.bind (.query .read .unit)
      (.call (.ret (badExtract weight)) (.cons v1 (.cons (.snd v0) (.cons v4 (.cons v5 .nil))))))

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

theorem goodExecution_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (source : Program CryptoOp (Command indexTy messageTy randomBound)
      [point₂, dataTy] (outputTy messageTy))
    (pk : G₂) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (rho : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M))
    (state : (oracleStore indexTy messageTy (goodConfig indexTy)).Value (cryptoBase F G₁ G₂ K M)) :
    ((goodExecution eq weight source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling (oracleStore indexTy messageTy (goodConfig indexTy)))
      (pk, data, rho, ())).run state = (do
        let z ← ((source.inline (machineRoutines (goodHash eq) (goodSign weight) randomBound)).run
          (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling (oracleStore indexTy messageTy (goodConfig indexTy)))
          (pk, data, ())).run state
        let r := (goodExtract eq weight).run (arithmetic F G₁ G₂ K M cost) (z.1.value, z.2.2, rho, ())
        pure (⟨r.value, z.1.steps + r.steps + 29⟩, z.2)) := by
  unfold goodExecution
  generalize goodExtract eq weight = finish
  dsimp [Program.run, Args.run, Expr.run, v0, v1, v4,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure, Machine.effects]
  simp only [pure_bind, bind_assoc]
  congr 1
  funext z
  apply congrArg pure
  apply congrArg (fun r => (r, z.2))
  apply congrArg (Run.mk _)
  omega

theorem badExecution_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (source : Program CryptoOp (Command indexTy messageTy randomBound)
      [point₂, dataTy] (outputTy messageTy))
    (pk : G₂) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (a b : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M))
    (state : (oracleStore indexTy messageTy (badConfig indexTy)).Value (cryptoBase F G₁ G₂ K M)) :
    ((badExecution eq weight source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
      (pk, data, a, b, ())).run state = (do
        let z ← ((source.inline (machineRoutines (badHash eq) (badSign weight) randomBound)).run
          (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
          (pk, data, ())).run state
        let r := (badExtract weight).run (arithmetic F G₁ G₂ K M cost) (z.1.value, z.2.2, a, b, ())
        pure (⟨r.value, z.1.steps + r.steps + 36⟩, z.2)) := by
  unfold badExecution
  generalize badExtract weight = finish
  dsimp [Program.run, Args.run, Expr.run, v0, v1, v4, v5,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure, Machine.effects]
  simp only [pure_bind, bind_assoc]
  congr 1
  funext z
  apply congrArg pure
  apply congrArg (fun r => (r, z.2))
  apply congrArg (Run.mk _)
  omega

def goodExecutionBound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime n : Nat) (queries : Fin 3 → Nat) (gamma xi e w : Nat) : Nat :=
  localTime + (∑ k, queries k * machinePrices sampling randomBound
    (goodHashBound cost n e) (goodSignBound cost n w) k) +
    goodExtractBound cost n (∑ k, queries k) (∑ k, queries k) gamma xi e w + 29

def badExecutionBound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime n na nb : Nat) (queries : Fin 3 → Nat) (xi e w : Nat) : Nat :=
  localTime + (∑ k, queries k * machinePrices sampling randomBound
    (badHashBound cost n e) (badSignBound cost n w) k) +
    badExtractBound cost na nb (∑ k, queries k) xi w + 36

variable {I N : Type}
  {cost : PrimitiveCosts}
  {index : indexTy.Value (cryptoBase F G₁ G₂ K M) ≃ I}
  {message : messageTy.Value (cryptoBase F G₁ G₂ K M) ≃ N}
  {localTime gammaLength xiLength : Nat} {queries : Fin 3 → Nat}
  {adv : Model.LazyAGM.Adversary F I N G₁ G₂}

theorem SourceCertificate.goodExecution_bound
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (e w : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ w)
    (g X : G₁) (pk : G₂) (rho : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M))
    (z : Run F × (oracleStore indexTy messageTy (goodConfig indexTy)).Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((goodExecution eq weight cert.code).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling (oracleStore indexTy messageTy (goodConfig indexTy)))
      (pk, cert.data, rho, ())).run ((g, X, rho), [], []))) :
    z.2.1 = (g, X, rho) ∧ transcriptSize z.2 ≤ ∑ k, queries k ∧
      z.1.steps ≤ goodExecutionBound cost sampling randomBound localTime rho.length queries
        gammaLength xiLength e w := by
  rw [goodExecution_run] at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have hs := goodSimulation_bound cost sampling eq weight randomBound e w heq hw g X rho
    cert.code (pk, cert.data, ()) localTime queries (cert.budget pk) r hr
  have ho := cert.simulated_output_sizes sampling (goodHash eq) (goodSign weight)
    (goodHashBound cost rho.length e) (goodSignBound cost rho.length w) (g, X, rho)
    (fun i => goodHash_steps_le cost eq e heq i g X rho)
    (fun m => goodSign_steps_le cost weight w m (fun i => hw i m) g X rho)
    pk ([], []) r hr
  have he := goodExtract_steps_le cost eq weight e w heq hw r.1.value r.2.2 rho
  have hh : r.2.2.1.length ≤ ∑ k, queries k := by
    have h := hs.2.1
    dsimp [transcriptSize] at h
    omega
  have hsig : r.2.2.2.length ≤ ∑ k, queries k := by
    have h := hs.2.1
    dsimp [transcriptSize] at h
    omega
  have hb := he.trans (goodExtractBound_mono cost rho.length e w hh hsig ho.1 ho.2)
  refine ⟨hs.1, hs.2.1, ?_⟩
  dsimp only [goodExecutionBound]
  exact Nat.add_le_add_right (Nat.add_le_add hs.2.2 hb) 29

theorem SourceCertificate.badExecution_bound
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (e w : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ w)
    (kappa : F) (pk : G₂) (H : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁))
    (a b : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M))
    (z : Run F × (oracleStore indexTy messageTy (badConfig indexTy)).Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((badExecution eq weight cert.code).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
      (pk, cert.data, a, b, ())).run ((kappa, H), [], []))) :
    z.2.1 = (kappa, H) ∧ transcriptSize z.2 ≤ ∑ k, queries k ∧
      z.1.steps ≤ badExecutionBound cost sampling randomBound localTime H.length a.length b.length queries
        xiLength e w := by
  rw [badExecution_run] at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have hs := badSimulation_bound cost sampling eq weight randomBound e w heq hw kappa H
    cert.code (pk, cert.data, ()) localTime queries (cert.budget pk) r hr
  have ho := cert.simulated_output_sizes sampling (badHash eq) (badSign weight)
    (badHashBound cost H.length e) (badSignBound cost H.length w) (kappa, H)
    (fun i => badHash_steps_le cost eq e heq i kappa H)
    (fun m => badSign_steps_le cost weight w m (fun i => hw i m) kappa H)
    pk ([], []) r hr
  have he := badExtract_steps_le cost weight w hw r.1.value r.2.2 a b
  have hsig : r.2.2.2.length ≤ ∑ k, queries k := by
    have h := hs.2.1
    dsimp [transcriptSize] at h
    omega
  have hb := he.trans (badExtractBound_mono cost a.length b.length w hsig ho.2)
  refine ⟨hs.1, hs.2.1, ?_⟩
  dsimp only [badExecutionBound]
  exact Nat.add_le_add_right (Nat.add_le_add hs.2.2 hb) 36

end Signatures.Runtime.AGM
