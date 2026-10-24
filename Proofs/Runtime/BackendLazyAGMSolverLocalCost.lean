import Proofs.Runtime.BackendLazyAGMSolver

/-! Local setup and extraction-adapter costs for the native AGM solvers. All
projections, empty-list construction, argument copies, and the bad branch's
public-key multiplication are charged using the fixed backend contracts. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram NativeHandler ReplySyntax

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))

omit [C.HasSum] [C.HasOption] in
theorem initial_reserved (value config : Ty CryptoAtom) (width cap fuel : Nat) (hcap : fuel ≤ cap)
    (cfg : config.Value (cryptoBase F G₁ G₂ M M)) :
    ReservedState (Q := Q) rep (value := value) (config := config) width cap fuel (cfg, [], ([], [])) := by
  simp [ReservedState, State.Messages, hcap]

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes lists laws dataLaws primitiveBound mono

theorem initialGood_cost (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (input : Env (cryptoBase F G₁ G₂ M M) inputTypes) (hi : Q.size (rep.env inputTypes) input ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive initialGood) input ≤
      64 * overhead (128 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound initialGood input).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := @lists.nil_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [initialGood, v0, v1, v3, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.nilBound, inputTypes, LanguageRepresentation.ty,
    LanguageRepresentation.env, Expr.denote, Var.get] at *
  grind only

theorem initialBad_cost (width scaleTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hg : ∀ g : G₂, Q.size (rep.ty point₂) g ≤ width)
    (hscale : ∀ f : F, ∀ g : G₂, (primitiveBound CryptoOp.scale₂).time (f, g) ≤ scaleTime)
    (input : Env (cryptoBase F G₁ G₂ M M) (scalar :: inputTypes))
    (hi : Q.size (rep.env (scalar :: inputTypes)) input ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive initialBad) input ≤
      scaleTime + 96 * overhead (128 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound initialBad input).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := @lists.nil_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [initialBad, v0, v1, v2, v3, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.nilBound, inputTypes, LanguageRepresentation.ty,
    LanguageRepresentation.env, Expr.denote, Var.get, arithmetic] at *
  grind only

omit lists in
theorem extractionArgsExpr_cost (value config : Ty CryptoAtom) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (input : Env (cryptoBase F G₁ G₂ M M) [.pair (AGM.outputTy message) (storeTy value config)])
    (hi : Q.size (rep.env [.pair (AGM.outputTy message) (storeTy value config)]) input ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (extractionArgs value config)) input ≤ 128 * overhead (128 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound (extractionArgs value config) input).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [extractionArgs, v0, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env,
    Expr.denote, Var.get, storeTy] at *
  grind only

omit lists in
theorem extractionArgsCode_cost (value config : Ty CryptoAtom) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (input : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M) ×
      (storeTy value config).Value (cryptoBase F G₁ G₂ M M))
    (hi : Q.size (rep.ty (.pair (AGM.outputTy message) (storeTy value config))) input ≤ width) :
    Q.cost (extractionArgsCode rep data cost primitive value config) input ≤
      136 * overhead (512 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hinput : Q.size (rep.env [.pair (AGM.outputTy message) (storeTy value config)]) (input, ()) ≤ 3 * width := by
    have hp := sizes.prod_le (rep.ty (.pair (AGM.outputTy message) (storeTy value config))) rep.data.unit (input, ())
    dsimp only [LanguageRepresentation.env] at *
    omega
  have hc := extractionArgsExpr_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
    value config (3 * width) (by omega) (by omega) (input, ()) hinput
  have hiCode := laws.identity (rep.ty (.pair (AGM.outputTy message) (storeTy value config))) input
  have huCode := dataLaws.unit (rep.ty (.pair (AGM.outputTy message) (storeTy value config))) input
  have hpCode := laws.pair (Q.identity (rep.ty (.pair (AGM.outputTy message) (storeTy value config))))
    (data.unit (rep.ty (.pair (AGM.outputTy message) (storeTy value config)))) input
  have hcomp := laws.compose
    (QP.pair (Q.identity (rep.ty (.pair (AGM.outputTy message) (storeTy value config))))
      (data.unit (rep.ty (.pair (AGM.outputTy message) (storeTy value config)))))
    (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (extractionArgs value config)) input
  have hfee : ∀ n ≤ 512 * width, overhead n ≤ overhead (512 * width) := fun _ hn => mono hn
  dsimp only [extractionArgsCode, extractionArgs, v0, LanguageRepresentation.ty, LanguageRepresentation.env,
    Expr.denote, Var.get, storeTy, id, Function.comp_def] at *
  grind only

end Signatures.Runtime.LazyAGM.NativeSolver
