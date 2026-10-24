import Proofs.Runtime.WeightedEvaluateSource
import Proofs.Runtime.BackendWeightedRead
import Proofs.Runtime.BackendLanguageCorrectness

/-! Native evaluation of weighted term lists with actual private-cache reads.
The correctness law preserves the complete value/cache distribution and the
source's query order, including repeated keys and zero coefficients. Complete
evaluator time bounds are derived separately in `BackendWeightedGoodEvaluate`
and `BackendWeightedBadEvaluate` from individual operation contracts. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM

namespace Signatures.Runtime.WeightedAGM.Evaluate

open BackendProgram Read

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {indexTy value : Ty CryptoAtom}
  (reader : Code Q unifSpec iface (rep.ty (inputTy indexTy value))
    (rep.ty (.pair value (cacheTy indexTy value))))

def readEffect {a b : Ty CryptoAtom} (instr : EvalCmd indexTy value a b) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty (cacheTy indexTy value)))
      (StepClass.HasProd.prod (rep.ty b) (rep.ty (cacheTy indexTy value))) :=
  match instr with | .lookup => reader

@[irreducible] def backendEvaluate
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value) :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [.list (evalRowTy indexTy), evalRowTy indexTy]) (rep.ty (cacheTy indexTy value)))
      (rep.ty (.pair value (cacheTy indexTy value))) :=
  Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (rep.ty (cacheTy indexTy value))
    (readEffect rep reader) (evaluateRows zero combine)

theorem backendEvaluate_source [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    [SampleableType (value.Value (cryptoBase F G₁ G₂ K M))]
    [AddCommMonoid (value.Value (cryptoBase F G₁ G₂ K M))]
    [SMul F (value.Value (cryptoBase F G₁ G₂ K M))]
    (hreader : ∀ k cache, reader.denote (k, cache) =
      ((BLS.LazyAGM.Reduction.privateListOracle
        (M := indexTy.Value (cryptoBase F G₁ G₂ K M)) (R := value.Value (cryptoBase F G₁ G₂ K M))) (.inr k)).run cache)
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (hz : zero.denote (arithmetic F G₁ G₂ K M cost) (rows, default, ()) = 0)
    (hc : ∀ answer coeff acc, combine.denote (arithmetic F G₁ G₂ K M cost) (answer, coeff, acc, ()) = acc + coeff • answer) :
    (backendEvaluate rep data cost primitive reader zero combine).denote ((rows, default, ()), cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle
        (M := indexTy.Value (cryptoBase F G₁ G₂ K M)) (R := value.Value (cryptoBase F G₁ G₂ K M)))
        (evalTerms rows)).run cache := by
  let impl := BLS.LazyAGM.Reduction.privateListOracle
    (M := indexTy.Value (cryptoBase F G₁ G₂ K M)) (R := value.Value (cryptoBase F G₁ G₂ K M))
  have hcompile := Language.compile_denote rep data (arithmetic F G₁ G₂ K M cost) primitive
    (rep.ty (cacheTy indexTy value)) (readEffect rep reader) (evalSemantics (fun k => impl (.inr k)))
    (by intro a b instr input saved; cases instr; exact hreader input saved)
    (evaluateRows zero combine) (rows, default, ()) cache
  rw [backendEvaluate, hcompile, evaluateRows_source cost impl zero combine rows default hz hc]

variable [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)

def backendGood : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.env [.list (evalRowTy index.ty), evalRowTy index.ty]) (rep.ty (cacheTy index.ty scalar)))
    (rep.ty (.pair scalar (cacheTy index.ty scalar))) :=
  backendEvaluate rep data cost primitive (goodRead rep data cost primitive sampling index) (.op .zero .unit) goodCombine

def backendBad : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.env [.list (evalRowTy index.ty), evalRowTy index.ty]) (rep.ty (cacheTy index.ty (.pair scalar scalar))))
    (rep.ty (.pair (.pair scalar scalar) (cacheTy index.ty (.pair scalar scalar)))) :=
  backendEvaluate rep data cost primitive (badRead rep data cost primitive sampling index)
    (.pair (.op .zero .unit) (.op .zero .unit)) badCombine

theorem backendGood_source
    (rows : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) (default : index.ty.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (backendGood rep data cost primitive sampling index).denote ((rows, default, ()), cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle
        (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F)) (evalTerms rows)).run cache :=
  backendEvaluate_source rep data cost primitive (goodRead rep data cost primitive sampling index)
    (goodRead_denote rep data cost primitive sampling index) (.op .zero .unit) goodCombine rows default cache rfl
    (fun answer coeff acc => goodCombine_denote cost answer coeff acc)

theorem backendBad_source
    (rows : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) (default : index.ty.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))) :
    (backendBad rep data cost primitive sampling index).denote ((rows, default, ()), cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle
        (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F × F)) (evalTerms rows)).run cache :=
  backendEvaluate_source rep data cost primitive (badRead rep data cost primitive sampling index)
    (badRead_denote rep data cost primitive sampling index) (.pair (.op .zero .unit) (.op .zero .unit)) badCombine
    rows default cache rfl (fun answer coeff acc => badCombine_denote cost answer acc coeff)

end Signatures.Runtime.WeightedAGM.Evaluate
