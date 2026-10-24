import Proofs.Runtime.BackendSchnorrROMSolver
import Proofs.Runtime.BackendSchnorrROMExtractionBudget

/-! Initial configuration encoding and runtime for the complete ROM solver.
The two challenge points and all environment/product headers are charged. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeSolver

open BackendProgram NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def InputBound (width : Nat) (input : Env (cryptoBase F G₁ G₂ K M) inputTypes) : Prop :=
  ConfigBound (Q := Q) rep width (input.1, input.2.1)

variable {header : Nat} (sizes : SizeLaws Q header)

include sizes in
theorem input_size (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (input : Env (cryptoBase F G₁ G₂ K M) inputTypes) (hi : InputBound (Q := Q) rep width input) :
    Q.size (rep.env inputTypes) input ≤ 5 * width := by
  rcases input with ⟨g, pk, u⟩
  cases u
  have hprod := @sizes.prod_le
  have hg := hi.1
  have hpk := hi.2
  simp only [LanguageRepresentation.env, LanguageRepresentation.ty, inputTypes] at *
  grind only

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {iface : Interface (C := C) unifSpec}
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes laws dataLaws primitiveBound mono

theorem initialExpression_cost (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (input : Env (cryptoBase F G₁ G₂ K M) inputTypes) (hi : InputBound (Q := Q) rep width input) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive initialExpression) input ≤
      64 * overhead (256 * width) := by
  have h := Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    initialExpression input
  apply h.trans
  rcases input with ⟨g, pk, u⟩
  cases u
  have hprod := @sizes.prod_le
  have hg := hi.1
  have hpk := hi.2
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [initialExpression, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity, Expr.denote, Var.get,
    LanguageRepresentation.env, LanguageRepresentation.ty, inputTypes, id, Function.comp_def] at *
  grind only

include routing in
theorem setup_bound (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width) :
    Bounds control queryCost (.atomic (iface := iface)
      (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive initialExpression))
      (InputBound (Q := Q) rep width) (ConfigBound (Q := Q) rep width)
      (65 * overhead (256 * width)) := by
  apply Bounds.atomic
  intro input hi
  have hin := input_size rep sizes width hh hu input hi
  have hout := config_size rep sizes width hh (input.1, input.2.1) hi
  have hc := initialExpression_cost rep sizes data cost primitive laws dataLaws primitiveBound mono width hh hu input hi
  have hr := (routing.localCall _ _).trans (mono (show
    Q.size (rep.env inputTypes) input + Q.size (rep.ty configTy) (input.1, input.2.1) ≤ 256 * width by omega))
  refine ⟨hi, ?_⟩
  change Q.cost _ input + control.localCall (Q.size (rep.env inputTypes) input)
    (Q.size (rep.ty configTy) (input.1, input.2.1)) ≤ _
  omega

end Signatures.Runtime.Schnorr.ListROM.NativeSolver
