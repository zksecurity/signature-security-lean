import Signatures.Runtime.BackendSchnorrROMHandlerComponents
import Signatures.Runtime.BackendSchnorrRawUniformLocalCost

/-! Encoding and runtime bounds for the actual shared-store adapters.
Every projection, pairing and retained input is charged. Only hash/final
preparation executes a scalar primitive, constructing the cache default zero. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeComponents

open BackendProgram RawTape

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
    (input : (withStore .nat).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (withStore .nat)) input ≤ width) :
    Q.size (rep.ty (.pair (taped .nat) cacheStore)) (randomInput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive randomInput) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (.pair (taped .nat) cacheStore))
      (randomInput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [randomInput, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive randomInput)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound randomInput (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [randomInput, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, primitiveBound, LocalBound.measured, Expr.denote, Var.get,
      arithmetic, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono randomInput input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem randomOutput_cost
    (input : (Ty.pair (taped .nat) cacheStore).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (.pair (taped .nat) cacheStore)) input ≤ width) :
    Q.size (rep.ty (withStore .nat)) (randomOutput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive randomOutput) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (withStore .nat))
      (randomOutput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [randomOutput, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive randomOutput)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound randomOutput (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [randomOutput, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, primitiveBound, LocalBound.measured, Expr.denote, Var.get,
      arithmetic, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono randomOutput input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem hashInput_cost
    (input : (withStore hashKey).Value (cryptoBase F G₁ G₂ K M)) (width zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hzero : Q.cost (primitive .zero) () ≤ zeroTime)
    (hi : Q.size (rep.ty (withStore hashKey)) input ≤ width) :
    Q.size (rep.ty (.pair (taped managedArgsTy) configTy)) (hashInput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive hashInput) input ≤ zeroTime + 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (.pair (taped managedArgsTy) configTy))
      (hashInput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [hashInput, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive hashInput)
      (input, ()) ≤ zeroTime + 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound hashInput (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [hashInput, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, primitiveBound, LocalBound.measured, Expr.denote, Var.get,
      arithmetic, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono hashInput input width
    (zeroTime + 1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem hashOutput_cost
    (input : (Ty.pair (taped (.pair scalar (.pair hashCache hashCache))) configTy).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (.pair (taped (.pair scalar (.pair hashCache hashCache))) configTy)) input ≤ width) :
    Q.size (rep.ty (withStore scalar)) (hashOutput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive hashOutput) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (withStore scalar))
      (hashOutput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [hashOutput, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive hashOutput)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound hashOutput (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [hashOutput, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, primitiveBound, LocalBound.measured, Expr.denote, Var.get,
      arithmetic, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono hashOutput input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem signingInput_cost
    (input : (withStore message).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (withStore message)) input ≤ width) :
    Q.size (rep.ty (.pair (taped signingArgsTy) keepCacheTy)) (signingInput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive signingInput) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (.pair (taped signingArgsTy) keepCacheTy))
      (signingInput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [signingInput, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive signingInput)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound signingInput (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [signingInput, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, primitiveBound, LocalBound.measured, Expr.denote, Var.get,
      arithmetic, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono signingInput input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem signingOutput_cost
    (input : (Ty.pair (taped (.pair signatureTy hashCache)) keepCacheTy).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (.pair (taped (.pair signatureTy hashCache)) keepCacheTy)) input ≤ width) :
    Q.size (rep.ty (withStore signatureTy)) (signingOutput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive signingOutput) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (withStore signatureTy))
      (signingOutput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [signingOutput, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive signingOutput)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound signingOutput (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [signingOutput, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, primitiveBound, LocalBound.measured, Expr.denote, Var.get,
      arithmetic, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono signingOutput input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem finalInput_cost
    (input : (withStore hashKey).Value (cryptoBase F G₁ G₂ K M)) (width zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hzero : Q.cost (primitive .zero) () ≤ zeroTime)
    (hi : Q.size (rep.ty (withStore hashKey)) input ≤ width) :
    Q.size (rep.ty (.pair (taped liveArgsTy) keepCacheTy)) (finalInput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive finalInput) input ≤ zeroTime + 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (.pair (taped liveArgsTy) keepCacheTy))
      (finalInput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [finalInput, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive finalInput)
      (input, ()) ≤ zeroTime + 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound finalInput (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [finalInput, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, primitiveBound, LocalBound.measured, Expr.denote, Var.get,
      arithmetic, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono finalInput input width
    (zeroTime + 1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

theorem finalOutput_cost
    (input : (Ty.pair (taped (.pair scalar hashCache)) keepCacheTy).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (.pair (taped (.pair scalar hashCache)) keepCacheTy)) input ≤ width) :
    Q.size (rep.ty (withStore scalar)) (finalOutput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width ∧
      Q.cost (localCode rep data cost primitive finalOutput) input ≤ 1028 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty (withStore scalar))
      (finalOutput.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ 32 * width := by
    dsimp only [finalOutput, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive finalOutput)
      (input, ()) ≤ 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound finalOutput (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [finalOutput, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, primitiveBound, LocalBound.measured, Expr.denote, Var.get,
      arithmetic, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact ⟨hout, (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono finalOutput input width
    (1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)⟩

end Signatures.Runtime.Schnorr.ListROM.NativeComponents
