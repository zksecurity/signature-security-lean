import Proofs.Runtime.BackendLazyAGMRead
import Proofs.Runtime.LazyAGMEvaluateSource
import Proofs.Runtime.BackendLanguageCorrectness
import Proofs.BLS.LazyAGMQueries

/-! Compile the bounded coefficient evaluator into the common backend with
actual private-cache effects. Exact correspondence preserves the accumulated
answer and private cache jointly, including empty inputs and repeated messages.
The complete evaluator runtime certificate is a separate obligation. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {value : Ty CryptoAtom}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
  (fallback : Expr CryptoOp [message, cacheTy value] value)

def readEffect : {a b : Ty CryptoAtom} → EvalCmd value a b →
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty (cacheTy value)))
      (StepClass.HasProd.prod (rep.ty b) (rep.ty (cacheTy value))) := fun instr =>
  match instr with
  | .lookup => backendRead rep data cost primitive sampler fallback

@[irreducible] def backendEvaluate
    (zero : Expr CryptoOp [.list evalRowTy, evalRowTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value) :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [.list evalRowTy, evalRowTy]) (rep.ty (cacheTy value)))
      (rep.ty (.pair value (cacheTy value))) :=
  Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy value))
    (readEffect rep data cost primitive sampler fallback) (evaluateRows zero combine)

variable [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))]
  (hsample : sampler.denote () = ($ᵗ (value.Value (cryptoBase F G₁ G₂ M M)) : ProbComp _))

include hsample in
theorem compileRead_denote {Γ : List (Ty CryptoAtom)} {result : Ty CryptoAtom}
    (program : Program CryptoOp (EvalCmd value) Γ result)
    (env : Env (cryptoBase F G₁ G₂ M M) Γ)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M))) :
    (Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy value))
      (readEffect rep data cost primitive sampler fallback) program).denote (env, cache) =
      (program.denote (arithmetic F G₁ G₂ M M cost)
        (evalSemantics (fun m => BLS.LazyAGM.Reduction.privateListOracle (.inr m))) env).run cache := by
  apply Language.compile_denote
  intro a b instr input saved
  cases instr
  exact backendRead_denote rep data cost primitive sampler fallback hsample input saved

include hsample in
theorem backendEvaluate_denote
    (zero : Expr CryptoOp [.list evalRowTy, evalRowTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M))) :
    (backendEvaluate rep data cost primitive sampler fallback zero combine).denote ((rows, default, ()), cache) =
      ((evaluateRows zero combine).denote (arithmetic F G₁ G₂ M M cost)
        (evalSemantics (fun m => BLS.LazyAGM.Reduction.privateListOracle (.inr m)))
        (rows, default, ())).run cache := by
  rw [backendEvaluate]
  apply Language.compile_denote
  intro a b instr input saved
  cases instr
  exact backendRead_denote rep data cost primitive sampler fallback hsample input saved

include hsample in
theorem backendEvaluate_source
    [AddCommMonoid (value.Value (cryptoBase F G₁ G₂ M M))]
    [SMul F (value.Value (cryptoBase F G₁ G₂ M M))]
    (zero : Expr CryptoOp [.list evalRowTy, evalRowTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (hz : zero.denote (arithmetic F G₁ G₂ M M cost) (rows, default, ()) = 0)
    (hc : ∀ answer coeff acc, combine.denote (arithmetic F G₁ G₂ M M cost) (answer, coeff, acc, ()) =
      acc + coeff • answer) :
    (backendEvaluate rep data cost primitive sampler fallback zero combine).denote ((rows, default, ()), cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M)
        (R := value.Value (cryptoBase F G₁ G₂ M M)))
        (evalTerms (rows.map (fun row => (row.1.1, row.2))))).run cache := by
  rw [backendEvaluate_denote rep data cost primitive sampler fallback hsample]
  rw [evaluateRows_source cost _ zero combine rows default hz hc]

omit [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))] in
@[irreducible] def backendEvaluateGood [SampleableType F]
    (samplingCode : MachineCompiler.SamplingImplementation Q iface rep) :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [.list evalRowTy, evalRowTy]) (rep.ty (cacheTy scalar)))
      (rep.ty (.pair scalar (cacheTy scalar))) :=
  backendEvaluate rep data cost primitive samplingCode.scalar (.op .zero .unit) (.op .zero .unit) goodCombine

omit [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))] in
@[irreducible] def backendEvaluateBad [SampleableType F]
    (samplingCode : MachineCompiler.SamplingImplementation Q iface rep) :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [.list evalRowTy, evalRowTy]) (rep.ty (cacheTy (.pair scalar scalar))))
      (rep.ty (.pair (.pair scalar scalar) (cacheTy (.pair scalar scalar)))) :=
  backendEvaluate rep data cost primitive (pairSampler rep data samplingCode)
    (.pair (.op .zero .unit) (.op .zero .unit)) (.pair (.op .zero .unit) (.op .zero .unit)) badCombine

omit [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))] in
theorem backendEvaluateGood_source [SampleableType F]
    (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F) (cache : List (M × F)) :
    (backendEvaluateGood rep data cost primitive samplingCode).denote ((rows, default, ()), cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F))
        (evalTerms (rows.map (fun row => (row.1.1, row.2))))).run cache := by
  rw [backendEvaluateGood]
  exact backendEvaluate_source rep data cost primitive samplingCode.scalar (.op .zero .unit)
    (samplingCode.scalar_denote ()) (.op .zero .unit) goodCombine rows default cache rfl
    (fun answer coeff acc => goodCombine_denote (G₁ := G₁) (G₂ := G₂) (M := M) cost answer coeff acc)

omit [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))] in
theorem backendEvaluateBad_source [SampleableType F]
    (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F) (cache : List (M × (F × F))) :
    (backendEvaluateBad rep data cost primitive samplingCode).denote ((rows, default, ()), cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × F))
        (evalTerms (rows.map (fun row => (row.1.1, row.2))))).run cache := by
  rw [backendEvaluateBad]
  exact backendEvaluate_source rep data cost primitive (pairSampler rep data samplingCode)
    (.pair (.op .zero .unit) (.op .zero .unit)) (pairSampler_denote rep data samplingCode ())
    (.pair (.op .zero .unit) (.op .zero .unit)) badCombine rows default cache rfl
    (fun answer coeff acc => badCombine_denote (G₁ := G₁) (G₂ := G₂) (M := M) cost answer acc coeff)

end Signatures.Runtime.LazyAGM
