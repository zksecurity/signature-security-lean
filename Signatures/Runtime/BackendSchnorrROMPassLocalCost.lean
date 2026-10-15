import Signatures.Runtime.BackendSchnorrROMPass
import Signatures.Runtime.BackendSchnorrRawUniformLocalCost

/-! Derived runtime and encoding bounds for every local pass adapter. Empty
and singleton list construction is charged; no optional projection or default
message is delegated to a free semantic operation. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram RawTape NativeComponents

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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)

include sizes lists laws dataLaws mono

theorem initialExpression_cost
    (input : (inputTy).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (inputTy)) input ≤ width) :
    Q.size (rep.ty (withStore point₁)) (initialExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive initialExpression) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := @lists.nil_le
  have hcons := @lists.cons_le
  have hout : Q.size (rep.ty (withStore point₁))
      (initialExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [initialExpression, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive initialExpression)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound initialExpression (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [initialExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, DataCostLaws.consBound,
      primitiveBound, LocalBound.measured, Expr.denote, Var.get, arithmetic, id, Function.comp_def,
      LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono initialExpression input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem verifyInput_cost
    (input : (withStore forgery).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (withStore forgery)) input ≤ width) :
    Q.size (rep.ty (.pair (withStore hashKey) forgery)) (verifyInput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive verifyInput) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := @lists.nil_le
  have hcons := @lists.cons_le
  have hout : Q.size (rep.ty (.pair (withStore hashKey) forgery))
      (verifyInput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [verifyInput, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive verifyInput)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound verifyInput (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [verifyInput, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, DataCostLaws.consBound,
      primitiveBound, LocalBound.measured, Expr.denote, Var.get, arithmetic, id, Function.comp_def,
      LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono verifyInput input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem verifyOutput_cost
    (input : (Ty.pair (withStore scalar) forgery).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (.pair (withStore scalar) forgery)) input ≤ width) :
    Q.size (rep.ty (NativeFork.passOutput cachePassOutput)) (verifyOutput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive verifyOutput) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := @lists.nil_le
  have hcons := @lists.cons_le
  have hout : Q.size (rep.ty (NativeFork.passOutput cachePassOutput))
      (verifyOutput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [verifyOutput, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive verifyOutput)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound verifyOutput (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [verifyOutput, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, DataCostLaws.consBound,
      primitiveBound, LocalBound.measured, Expr.denote, Var.get, arithmetic, id, Function.comp_def,
      LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono verifyOutput input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem singletonExpression_cost
    (input : (NativeFork.passOutput cachePassOutput).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (NativeFork.passOutput cachePassOutput)) input ≤ width) :
    Q.size (rep.ty (resultTy)) (singletonExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive singletonExpression) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := @lists.nil_le
  have hcons := @lists.cons_le
  have hout : Q.size (rep.ty (resultTy))
      (singletonExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [singletonExpression, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive singletonExpression)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound singletonExpression (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [singletonExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, DataCostLaws.consBound,
      primitiveBound, LocalBound.measured, Expr.denote, Var.get, arithmetic, id, Function.comp_def,
      LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono singletonExpression input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem cutoffExpression_cost
    (input : (withStore .unit).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (withStore .unit)) input ≤ width) :
    Q.size (rep.ty (resultTy)) (cutoffExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive cutoffExpression) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := @lists.nil_le
  have hcons := @lists.cons_le
  have hout : Q.size (rep.ty (resultTy))
      (cutoffExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [cutoffExpression, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive cutoffExpression)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound cutoffExpression (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [cutoffExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, DataCostLaws.consBound,
      primitiveBound, LocalBound.measured, Expr.denote, Var.get, arithmetic, id, Function.comp_def,
      LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono cutoffExpression input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

end Signatures.Runtime.Schnorr.ListROM.NativePass
