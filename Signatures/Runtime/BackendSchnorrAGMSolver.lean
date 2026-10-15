import Signatures.Runtime.BackendSchnorrAGMSolverOutput
import Signatures.Runtime.BackendSchnorrAGMCallerOutput

/-! The complete native single-pass Schnorr AGM DLog solver. Initial basis and
state construction, actual boundary conversions, general caller execution,
cutoff handling, extraction and scalar projection are represented as code. -/

open OracleComp OracleSpec PFunctor AlgebraicGroupModel.Interaction
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

abbrev SourceInput (G : Type) := Message Unit (Schnorr.AGM.Group G)
abbrev inputTypes : List (Ty CryptoAtom) := [point₁, point₁]

def initialExpression : Expr CryptoOp inputTypes (.pair configTy storeTy) :=
  let g : Expr CryptoOp inputTypes point₁ := .var .here
  let pk : Expr CryptoOp inputTypes point₁ := .var (.there .here)
  let zero : Expr CryptoOp inputTypes scalar := .op .zero .unit
  let one : Expr CryptoOp inputTypes scalar := .op .one .unit
  .pair (.pair g pk) (.pair (.pair g pk)
    (.pair .nil (.pair (.cons (.pair one zero) (.cons (.pair zero one) .nil))
      (.pair .nil (.pair (.bool false) (.bool false))))))

def optionView {A : Type} : Option A → Unit ⊕ A
  | none => .inl ()
  | some out => .inr out

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor (SourceInput G₁) (SourceForgery F G₁ M))

/-- These are implemented local representation adapters, not solver budgets. -/
structure DataPorts where
  input : Q.Realizer (rep.ty configTy) bd.input (fun p => Schnorr.AGM.initial p.1 p.2)
  output : Q.Realizer bd.out (rep.ty forgeryTy) encodeForgery
  optional : Q.Realizer (StepClass.HasOption.option bd.out)
    (StepClass.HasSum.sum rep.data.unit bd.out) optionView

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def setup : Code Q unifSpec iface (rep.env inputTypes)
    (StepClass.HasProd.prod bd.input (rep.ty storeTy)) :=
  .seq (.atomic (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive initialExpression))
    (.first (rep.ty storeTy) (.atomic boundary.input))

def finishSome (extractor : Code Q unifSpec iface (rep.ty Extraction.inputTy) (rep.ty Read.outputTy)) :
    Code Q unifSpec iface (StepClass.HasProd.prod bd.out (rep.ty storeTy)) (rep.ty scalar) :=
  .seq (adaptOutput rep bd boundary.output)
    (.seq extractor (.atomic (QP.fst (rep.ty scalar) (rep.ty stateTy))))

def cutoff : Code Q unifSpec iface (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) (rep.ty scalar) :=
  .atomic (Q.compose (data.unit (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy))) (primitive CryptoOp.zero))

variable [QD : Q.IsDistributive]

def terminal (extractor : Code Q unifSpec iface (rep.ty Extraction.inputTy) (rep.ty Read.outputTy)) :
    Code Q unifSpec iface (Caller.result (bd := bd) (rep.ty storeTy)) (rep.ty scalar) :=
  .seq (.first (rep.ty storeTy) (.atomic boundary.optional))
    (.seq (.atomic (QD.distribute rep.data.unit bd.out (rep.ty storeTy)))
      (.branch (cutoff rep data cost primitive) (finishSome rep bd boundary extractor)))

variable [Q.HasOption] [OptionCode (Q := Q)] [DecidableEq (SourceRequest F G₁ M)]
  (ports : Ports (Q := Q) rep bd)
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def program (fuel : Nat) : Code Q unifSpec iface (rep.env inputTypes) (rep.ty scalar) :=
  .seq (setup rep bd boundary data cost primitive)
    (.seq (Handler.caller rep bd ports data cost primitive randomPorts sampler R fuel)
      (terminal rep bd boundary data cost primitive (Extraction.code rep data cost primitive sampler)))

omit QD [Q.HasOption] [OptionCode (Q := Q)] [DecidableEq (SourceRequest F G₁ M)] in
theorem setup_denote (g pk : G₁) :
    (setup (iface := iface) rep bd boundary data cost primitive).denote (g, pk, ()) =
      pure (Schnorr.AGM.initial g pk, (g, pk), encodeState ({} : State F G₁ M)) := by
  simp only [setup, Code.denote, pure_bind, map_pure]
  rfl

omit QD [Q.HasOption] [OptionCode (Q := Q)] [DecidableEq (SourceRequest F G₁ M)]
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] QS in
theorem finishSome_denote (extractor : Code Q unifSpec iface (rep.ty Extraction.inputTy) (rep.ty Read.outputTy))
    (out : SourceForgery F G₁ M) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (finishSome rep bd boundary extractor).denote (out, saved) =
      Prod.fst <$> extractor.denote (encodeForgery out, saved.2) := by
  simp only [finishSome, Code.denote, bind_pure_comp]
  rw [adaptOutput_denote, pure_bind]

omit QD [Q.HasOption] [OptionCode (Q := Q)] [DecidableEq (SourceRequest F G₁ M)] [C.HasOption] QP QS in
theorem cutoff_denote (input : Unit × ((G₁ × G₁) × EncodedState F G₁ M)) :
    (cutoff (iface := iface) rep data cost primitive).denote input = pure (0 : F) := rfl

omit [Q.HasOption] [OptionCode (Q := Q)] [DecidableEq (SourceRequest F G₁ M)] QS in
theorem terminal_denote (extractor : Code Q unifSpec iface (rep.ty Extraction.inputTy) (rep.ty Read.outputTy))
    (result : Option (SourceForgery F G₁ M)) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (terminal rep bd boundary data cost primitive extractor).denote (result, saved) =
      match result with
      | none => pure (0 : F)
      | some out => Prod.fst <$> extractor.denote (encodeForgery out, saved.2) := by
  cases result with
  | none =>
      simp only [terminal, Code.denote, optionView, Sum.elim_inl, map_pure, pure_bind]
      rfl
  | some out =>
      simp only [terminal, Code.denote, optionView, Sum.elim_inr, map_pure, pure_bind]
      exact finishSome_denote rep bd boundary extractor out saved

omit [Q.HasOption] [OptionCode (Q := Q)] [DecidableEq (SourceRequest F G₁ M)] QS in
/-- A cutoff never executes output conversion or extraction, including their
sampling effects. This is equality of complete costed runs. -/
theorem terminal_none_run
    (extractor other : Code Q unifSpec iface (rep.ty Extraction.inputTy) (rep.ty Read.outputTy))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (terminal rep bd boundary data cost primitive extractor).run control queryCost (none, saved) =
      (terminal rep bd boundary data cost primitive other).run control queryCost (none, saved) := by
  simp only [terminal, Code.run, sequenceRun, retainRun, chargeRun, pure_bind, map_pure, optionView, Sum.elim_inl]

theorem program_denote (fuel : Nat) (g pk : G₁) :
    (program rep bd boundary data cost primitive ports randomPorts sampler R fuel).denote (g, pk, ()) =
      (Handler.caller rep bd ports data cost primitive randomPorts sampler R fuel).denote
        (Schnorr.AGM.initial g pk, (g, pk), encodeState ({} : State F G₁ M)) >>=
      fun p => (terminal rep bd boundary data cost primitive (Extraction.code rep data cost primitive sampler)).denote p := by
  simp only [program, Code.denote]
  erw [setup_denote (iface := iface) rep bd boundary data cost primitive g pk]
  simp only [pure_bind]

end Signatures.Runtime.SchnorrAGM.Native.Solver
