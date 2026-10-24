import Proofs.Runtime.BackendLazyAGMCallerResources
import Proofs.Runtime.BackendLazyAGMExtraction

/-! Complete native good/bad AGM programs. Challenge setup constructs empty
caches and transcripts; the bad branch samples its signing key. The general
caller uses native dispatch, and terminal code adapts its algebraic output to
the native extractor. A cutoff has an explicit zero result. Component semantics
are proved here; complete resource composition is a separate obligation. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram Coron NativeHandler ReplySyntax

abbrev inputTypes : List (Ty CryptoAtom) := [point₁, point₁, point₂, point₂]

def initialGood : Expr CryptoOp inputTypes (.pair point₂ (storeTy scalar goodConfigTy)) :=
  .pair v3 (.pair (.pair v0 v1) (.pair .nil (.pair .nil .nil)))

def initialBad : Expr CryptoOp (scalar :: inputTypes) (.pair point₂ (storeTy (.pair scalar scalar) badConfigTy)) :=
  .pair (.op .scale₂ (.pair v0 v3)) (.pair (.pair v0 (.pair v1 v2)) (.pair .nil (.pair .nil .nil)))

def extractionArgs (value config : Ty CryptoAtom) :
    Expr CryptoOp [.pair (AGM.outputTy message) (storeTy value config)]
      (.pair (.pair (AGM.outputTy message) (.pair transcriptTy .unit)) (cacheTy value)) :=
  .pair (.pair (.fst v0) (.pair (.snd (.snd (.snd v0))) .unit)) (.fst (.snd (.snd v0)))

def optionView {A : Type} : Option A → Unit ⊕ A
  | none => .inl ()
  | some value => .inr value

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))

/-- Actual encoding and option-inspection code at the solver boundary. These
ports carry no assumption about the complete solver's efficiency. -/
structure DataPorts where
  key : Q.Realizer (rep.ty point₂) bd.input id
  output : Q.Realizer bd.out (rep.ty (AGM.outputTy message)) id
  optional : Q.Realizer (StepClass.HasOption.option bd.out)
    (StepClass.HasSum.sum rep.data.unit bd.out) optionView

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  [Field F] [SampleableType F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def setupGood : Code Q unifSpec iface (rep.env inputTypes)
    (StepClass.HasProd.prod bd.input (rep.ty (storeTy scalar goodConfigTy))) :=
  .seq (.atomic (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive initialGood))
    (.first (rep.ty (storeTy scalar goodConfigTy)) (.atomic boundary.key))

def setupBad : Code Q unifSpec iface (rep.env inputTypes)
    (StepClass.HasProd.prod bd.input (rep.ty (storeTy (.pair scalar scalar) badConfigTy))) :=
  .seq (.atomic (QP.pair (data.unit (rep.env inputTypes)) (Q.identity (rep.env inputTypes))))
    (.seq (.first (rep.env inputTypes) sampling.scalar)
      (.seq (.atomic (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive initialBad))
        (.first (rep.ty (storeTy (.pair scalar scalar) badConfigTy)) (.atomic boundary.key))))

def extractionArgsCode (value config : Ty CryptoAtom) :=
  Q.compose
    (QP.pair (Q.identity (rep.ty (.pair (AGM.outputTy message) (storeTy value config))))
      (data.unit (rep.ty (.pair (AGM.outputTy message) (storeTy value config)))))
    (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (extractionArgs value config))

def finishSome (value config : Ty CryptoAtom)
    (extractor : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [AGM.outputTy message, transcriptTy]) (rep.ty (cacheTy value)))
      (rep.ty (.pair scalar (cacheTy value)))) :
    Code Q unifSpec iface (StepClass.HasProd.prod bd.out (rep.ty (storeTy value config))) (rep.ty scalar) :=
  .seq (.first (rep.ty (storeTy value config)) (.atomic boundary.output))
    (.seq (.atomic (extractionArgsCode rep data cost primitive value config))
      (.seq extractor (.atomic (QP.fst (rep.ty scalar) (rep.ty (cacheTy value))))))

def cutoff (value config : Ty CryptoAtom) : Code Q unifSpec iface
    (StepClass.HasProd.prod rep.data.unit (rep.ty (storeTy value config))) (rep.ty scalar) :=
  .atomic (Q.compose (data.unit (StepClass.HasProd.prod rep.data.unit (rep.ty (storeTy value config))))
    (primitive CryptoOp.zero))

def terminal (value config : Ty CryptoAtom)
    (extractor : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [AGM.outputTy message, transcriptTy]) (rep.ty (cacheTy value)))
      (rep.ty (.pair scalar (cacheTy value)))) :
    Code Q unifSpec iface (Caller.result (bd := bd) (rep.ty (storeTy value config))) (rep.ty scalar) :=
  .seq (.first (rep.ty (storeTy value config)) (.atomic boundary.optional))
    (.seq (.atomic (QD.distribute rep.data.unit bd.out (rep.ty (storeTy value config))))
      (.branch (cutoff rep data cost primitive value config)
        (finishSome rep bd boundary data cost primitive value config extractor)))

def goodProgram (fuel : Nat) : Code Q unifSpec iface (rep.env inputTypes) (rep.ty scalar) :=
  .seq (setupGood rep bd boundary data cost primitive)
    (.seq (goodCaller rep bd ports sampler data cost primitive sampling R fuel)
      (terminal rep bd boundary data cost primitive scalar goodConfigTy
        (backendExtractGood rep data cost primitive sampling)))

def badProgram (fuel : Nat) : Code Q unifSpec iface (rep.env inputTypes) (rep.ty scalar) :=
  .seq (setupBad rep bd boundary data cost primitive sampling)
    (.seq (badCaller rep bd ports sampler data cost primitive sampling R fuel)
      (terminal rep bd boundary data cost primitive (.pair scalar scalar) badConfigTy
        (backendExtractBad rep data cost primitive sampling)))

omit QO QD OC [SampleableType F] in
theorem setupGood_denote (g X : G₁) (g₂ pk : G₂) :
    (setupGood (iface := iface) rep bd boundary data cost primitive).denote (g, X, g₂, pk, ()) =
      pure (pk, (g, X), [], ([], [])) := by
  simp only [setupGood, Code.denote, map_pure, pure_bind]
  rfl

omit QO QD OC in
theorem setupBad_denote (g X : G₁) (g₂ pk : G₂) :
    (setupBad rep bd boundary data cost primitive sampling).denote (g, X, g₂, pk, ()) =
      (fun kappa => (kappa • g₂, (kappa, g, X), [], ([], []))) <$> ($ᵗ F : ProbComp F) := by
  simp only [setupBad, Code.denote, sampling.scalar_denote, map_pure, pure_bind,
    bind_pure_comp, Functor.map_map]
  rfl

omit QO QD OC [SampleableType F] in
theorem finishSome_denote (value config : Ty CryptoAtom)
    (extractor : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [AGM.outputTy message, transcriptTy]) (rep.ty (cacheTy value)))
      (rep.ty (.pair scalar (cacheTy value))))
    (out : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (saved : (storeTy value config).Value (cryptoBase F G₁ G₂ M M)) :
    (finishSome rep bd boundary data cost primitive value config extractor).denote (out, saved) =
      Prod.fst <$> extractor.denote ((out, saved.2.2, ()), saved.2.1) := by
  simp only [finishSome, Code.denote, map_pure, pure_bind, bind_pure_comp]
  rfl

omit QP QS QO QD OC [C.HasOption] [SampleableType F] in
theorem cutoff_denote (value config : Ty CryptoAtom)
    (input : Unit × (storeTy value config).Value (cryptoBase F G₁ G₂ M M)) :
    (cutoff (iface := iface) rep data cost primitive value config).denote input = pure (0 : F) := rfl

omit QO OC [SampleableType F] in
theorem terminal_denote (value config : Ty CryptoAtom)
    (extractor : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [AGM.outputTy message, transcriptTy]) (rep.ty (cacheTy value)))
      (rep.ty (.pair scalar (cacheTy value))))
    (result : Option ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))
    (saved : (storeTy value config).Value (cryptoBase F G₁ G₂ M M)) :
    (terminal rep bd boundary data cost primitive value config extractor).denote (result, saved) =
      match result with
      | none => pure (0 : F)
      | some out => Prod.fst <$> extractor.denote ((out, saved.2.2, ()), saved.2.1) := by
  cases result with
  | none =>
      simp only [terminal, Code.denote, optionView, Sum.elim_inl, map_pure, pure_bind]
      rfl
  | some out =>
      simp only [terminal, Code.denote, optionView, Sum.elim_inr, map_pure, pure_bind]
      exact finishSome_denote rep bd boundary data cost primitive value config extractor out saved

theorem goodProgram_denote (fuel : Nat) (g X : G₁) (g₂ pk : G₂) :
    (goodProgram rep bd ports sampler boundary data cost primitive sampling R fuel).denote (g, X, g₂, pk, ()) =
      (goodCaller rep bd ports sampler data cost primitive sampling R fuel).denote
        (pk, (g, X), [], ([], [])) >>=
      fun p => (terminal rep bd boundary data cost primitive scalar goodConfigTy
        (backendExtractGood rep data cost primitive sampling)).denote p := by
  simp only [goodProgram, Code.denote]
  erw [setupGood_denote (iface := iface) rep bd boundary data cost primitive g X g₂ pk]
  simp only [pure_bind]

theorem badProgram_denote (fuel : Nat) (g X : G₁) (g₂ pk : G₂) :
    (badProgram rep bd ports sampler boundary data cost primitive sampling R fuel).denote (g, X, g₂, pk, ()) = (do
      let kappa ← ($ᵗ F : ProbComp F)
      let p ← (badCaller rep bd ports sampler data cost primitive sampling R fuel).denote
        (kappa • g₂, (kappa, g, X), [], ([], []))
      (terminal rep bd boundary data cost primitive (.pair scalar scalar) badConfigTy
        (backendExtractBad rep data cost primitive sampling)).denote p) := by
  simp only [badProgram, Code.denote]
  erw [setupBad_denote rep bd boundary data cost primitive sampling g X g₂ pk]
  simp only [bind_map_left]

end Signatures.Runtime.LazyAGM.NativeSolver
