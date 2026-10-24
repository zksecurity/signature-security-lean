import Proofs.Runtime.BackendSchnorrAGMEntryRead

/-! Encoding and compiled return-adapter bounds for reads exposing a full entry.
The complete returned entry, cache and histories are accounted for. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.EntryRead

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def Output (width cap historyWidth : Nat) (output : outputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  Q.size (rep.ty entryTy) output.1 ≤ 5 * width ∧ Read.StateBound (Q := Q) rep width cap historyWidth output.2

omit [C.HasSum] [C.HasOption] in
theorem return_property (width cap historyWidth : Nat)
    (input : Read.retainedOutputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Read.CoreOutput (Q := Q) rep width cap input.1 ∧ Read.History (Q := Q) rep historyWidth input.2) :
    Output (Q := Q) rep width cap historyWidth (returnValue input) :=
  ⟨hi.1.1.1, hi.1.1.2.1, hi.1.1.2.2, hi.2⟩

variable {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists in
theorem output_size (width cap historyWidth : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (output : outputTy.Value (cryptoBase F G₁ G₂ K M)) (ho : Output (Q := Q) rep width (cap + 1) historyWidth output) :
    Q.size (rep.ty outputTy) output ≤ Read.frameWidth width cap historyWidth := by
  obtain ⟨hf, he, hn, hm⟩ := ho
  have hc := CacheCompiler.list_size rep sizes lists output.2.1 (5 * width) (cap + 1) (by omega) he hn
  have hm := Read.history_size rep sizes width historyWidth hh hb output.2.2 hm
  have hprod := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty, Read.frameWidth] at *
  grind only

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes laws dataLaws primitiveBound mono

theorem finish_cost (input : Read.retainedOutputTy.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty Read.retainedOutputTy) input ≤ width) :
    Q.cost (finish rep data cost primitive) input ≤ 260 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty outputTy) (returnValue input) ≤ 32 * width := by
    dsimp only [returnValue, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive returnExpression)
      (input, ()) ≤ 256 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound returnExpression (input, ())).trans ?_
    have hfee : ∀ k ≤ 256 * width, overhead k ≤ overhead (256 * width) := fun _ h => mono h
    dsimp only [returnExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      Expr.denote, Var.get, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  unfold finish
  have h := Read.framed_cost rep data cost primitive sizes laws dataLaws mono returnExpression input width
    (256 * overhead (256 * width)) hh hu hi hout he
  exact h.trans (by omega)

end Signatures.Runtime.SchnorrAGM.Native.EntryRead
