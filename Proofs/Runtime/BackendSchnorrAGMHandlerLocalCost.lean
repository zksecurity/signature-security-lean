import Proofs.Runtime.BackendSchnorrAGMHandlerSize

/-! Costs of the actual compiled common-store adapters. These programs only
project, pair and construct the empty reply list. Their bounds use structural
backend contracts and charge the complete retained input. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.HandlerComponents

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)

include sizes laws dataLaws mono

theorem randomInput_cost
    (input : (argsStoreTy randomArgsTy).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (argsStoreTy randomArgsTy)) input ≤ width) :
    Q.cost (localCode rep data cost primitive (randomInputExpression)) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (savedTy Random.inputTy))
      ((randomInputExpression).denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [randomInputExpression, Expr.denote, Var.get, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (randomInputExpression))
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound (randomInputExpression) (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [randomInputExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact (Read.framed_cost rep data cost primitive sizes laws dataLaws mono (randomInputExpression) input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

theorem hashInput_cost
    (input : (argsStoreTy groupArgsTy).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (argsStoreTy groupArgsTy)) input ≤ width) :
    Q.cost (localCode rep data cost primitive (hashInputExpression)) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (savedTy HashDispatch.inputTy))
      ((hashInputExpression).denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [hashInputExpression, Expr.denote, Var.get, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (hashInputExpression))
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound (hashInputExpression) (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [hashInputExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact (Read.framed_cost rep data cost primitive sizes laws dataLaws mono (hashInputExpression) input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

theorem signingInput_cost
    (input : (argsStoreTy groupArgsTy).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (argsStoreTy groupArgsTy)) input ≤ width) :
    Q.cost (localCode rep data cost primitive (signingInputExpression)) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (savedTy SigningDispatch.inputTy))
      ((signingInputExpression).denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [signingInputExpression, Expr.denote, Var.get, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (signingInputExpression))
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound (signingInputExpression) (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [signingInputExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact (Read.framed_cost rep data cost primitive sizes laws dataLaws mono (signingInputExpression) input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

theorem groupOutput_cost (value : Ty CryptoAtom)
    (input : (savedTy (.pair (groupReplyTy value) stateTy)).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (savedTy (.pair (groupReplyTy value) stateTy))) input ≤ width) :
    Q.cost (localCode rep data cost primitive (groupOutputExpression value)) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (resultTy (groupReplyTy value)))
      ((groupOutputExpression value).denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [groupOutputExpression, Expr.denote, Var.get, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (groupOutputExpression value))
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound (groupOutputExpression value) (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [groupOutputExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact (Read.framed_cost rep data cost primitive sizes laws dataLaws mono (groupOutputExpression value) input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

theorem hashOutput_cost (lists : ListSizeLaws Q rep.data header)
    (input : (savedTy Read.outputTy).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (savedTy Read.outputTy)) input ≤ width) :
    Q.cost (localCode rep data cost primitive (hashOutputExpression)) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := lists.nil_le (rep.ty point₁)
  have hout : Q.size (rep.ty (resultTy scalarGroupReplyTy))
      ((hashOutputExpression).denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [hashOutputExpression, Expr.denote, Var.get, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (hashOutputExpression))
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound (hashOutputExpression) (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [hashOutputExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact (Read.framed_cost rep data cost primitive sizes laws dataLaws mono (hashOutputExpression) input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

end Signatures.Runtime.SchnorrAGM.Native.HandlerComponents
