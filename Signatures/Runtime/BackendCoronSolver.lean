import Signatures.Runtime.BackendCoronCallerBudget
import Signatures.Runtime.BackendCoronFinishBudget

/-! A complete native challenge-to-output Coron solver. Setup constructs empty
caches from the actual challenge; the caller runs with native handlers; terminal
code decodes a forgery and runs the certified extraction. Fuel exhaustion uses
an explicit zero-result branch, excluded by the caller's termination theorem.
Only data encoders/tag inspection are supplied as local code at the boundary. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver

open BackendProgram

abbrev inputTypes : List (Ty CryptoAtom) := [point₁, point₂, point₁, point₂, point₁]

def initial (qS : Nat) : Expr CryptoOp inputTypes (.pair point₂ (machineStore qS)) :=
  .pair (.var (.there (.there (.there .here))))
    (.pair (.pair (.var .here) (.pair (.var (.there (.there .here)))
      (.var (.there (.there (.there (.there .here))))))) (.pair .nil (.pair .nil .nil)))

def optionView {A : Type} : Option A → Unit ⊕ A
  | none => .inl ()
  | some value => .inr value

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))

structure DataPorts where
  key : Q.Realizer (rep.ty point₂) bd.input id
  forgery : Q.Realizer bd.out (rep.ty (.pair message point₁)) id
  optional : Q.Realizer (StepClass.HasOption.option bd.out)
    (StepClass.HasSum.sum rep.data.unit bd.out) optionView

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  [Field F] [SampleableType F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def setup (qS : Nat) : Code Q unifSpec iface (rep.env inputTypes)
    (StepClass.HasProd.prod bd.input (rep.ty (machineStore qS))) :=
  .seq (.atomic (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (initial qS)))
    (.first (rep.ty (machineStore qS)) (.atomic boundary.key))

def finishSome (qS : Nat) : Code Q unifSpec iface
    (StepClass.HasProd.prod bd.out (rep.ty (machineStore qS))) (rep.ty point₁) :=
  .seq (.first (rep.ty (machineStore qS)) (.atomic boundary.forgery))
    (.seq (backendFinish rep data samplingCode cost primitive qS)
      (.atomic (QP.fst (rep.ty point₁) (rep.ty (machineStore qS)))))

def cutoff (qS : Nat) : Code Q unifSpec iface
    (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))) (rep.ty point₁) :=
  .atomic (Q.compose (data.unit (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))))
    (primitive CryptoOp.zero₁))

def terminal (qS : Nat) : Code Q unifSpec iface
    (Caller.result (bd := bd) (rep.ty (machineStore qS))) (rep.ty point₁) :=
  .seq (.first (rep.ty (machineStore qS)) (.atomic boundary.optional))
    (.seq (.atomic (QD.distribute rep.data.unit bd.out (rep.ty (machineStore qS))))
      (.branch (cutoff rep data cost primitive qS)
        (finishSome rep bd boundary data samplingCode cost primitive qS)))

def program (qS fuel : Nat) : Code Q unifSpec iface (rep.env inputTypes) (rep.ty point₁) :=
  .seq (setup rep bd boundary data cost primitive qS)
    (.seq (NativeHandler.caller rep bd ports sampler data samplingCode cost primitive R qS fuel)
      (terminal rep bd boundary data samplingCode cost primitive qS))

omit QO QD OC [SampleableType F] in
theorem setup_denote (qS : Nat) (g : G₁) (g₂ : G₂) (X : G₁) (pk : G₂) (h : G₁) :
    (setup (iface := iface) rep bd boundary data cost primitive qS).denote (g, g₂, X, pk, h, ()) =
      pure (pk, machineState g X h (CacheState.empty : CacheState F M qS)) := by
  simp only [setup, Code.denote, map_pure, pure_bind]
  rfl

omit QO QD OC in
theorem finishSome_denote (qS : Nat) (out : M × G₁)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (finishSome rep bd boundary data samplingCode cost primitive qS).denote (out, saved) =
      Prod.fst <$> (backendFinish rep data samplingCode cost primitive qS).denote (out, saved) := by
  simp only [finishSome, Code.denote, map_pure, pure_bind, bind_pure_comp]
  rfl

omit QP QS QO QD OC [C.HasOption] [SampleableType F] in
theorem cutoff_denote (qS : Nat) (input : Unit × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (cutoff (iface := iface) rep data cost primitive qS).denote input = pure (0 : G₁) := rfl

omit QO OC in
theorem terminal_denote (qS : Nat) (result : Option (M × G₁))
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (terminal rep bd boundary data samplingCode cost primitive qS).denote (result, saved) =
      match result with
      | none => pure (0 : G₁)
      | some out => Prod.fst <$> (backendFinish rep data samplingCode cost primitive qS).denote (out, saved) := by
  cases result with
  | none =>
      simp only [terminal, Code.denote, optionView, Sum.elim_inl, map_pure, pure_bind]
      rfl
  | some out =>
      simp only [terminal, Code.denote, optionView, Sum.elim_inr, map_pure, pure_bind]
      exact finishSome_denote rep bd boundary data samplingCode cost primitive qS out saved

theorem program_denote (qS fuel : Nat) (g : G₁) (g₂ : G₂) (X : G₁) (pk : G₂) (h : G₁) :
    (program rep bd ports sampler boundary data samplingCode cost primitive R qS fuel).denote (g, g₂, X, pk, h, ()) =
      (NativeHandler.caller rep bd ports sampler data samplingCode cost primitive R qS fuel).denote
        (pk, machineState g X h (CacheState.empty : CacheState F M qS)) >>=
      fun p => (terminal rep bd boundary data samplingCode cost primitive qS).denote p := by
  simp only [program, Code.denote]
  erw [setup_denote (iface := iface) rep bd boundary data cost primitive qS g g₂ X pk h]
  simp only [pure_bind]

end Signatures.Runtime.Coron.NativeSolver
