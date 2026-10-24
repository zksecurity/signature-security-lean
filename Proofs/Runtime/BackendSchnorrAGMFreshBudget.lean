import Proofs.Runtime.BackendSchnorrAGMFresh

/-! Derived native time and size bounds for fresh-entry construction and sampling.
Only scalar sampling and the field/structural primitives need cost contracts. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native

open BackendProgram

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
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes

omit [Q.HasCategory] QP QS [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [DecidableEq K] [DecidableEq M] in
theorem readStore_size (saved : ReadStore F) (width : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (ha : Q.size (rep.ty affineTy) saved.1 ≤ width) :
    Q.size (rep.ty readStoreTy) saved ≤ 3 * width := by
  have h := sizes.prod_le (rep.ty affineTy) rep.data.bool saved
  exact h.trans (by have ht := hb saved.2; omega)

omit [Q.HasCategory] QP QS [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem freshValue_size (input : F × ReadStore F) (width : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : Q.size (rep.ty scalar) input.1 ≤ width)
    (ha : Q.size (rep.ty affineTy) input.2.1 ≤ width) :
    Q.size (rep.ty entryTy) (freshValue input).1 ≤ 5 * width ∧
      Q.size (rep.ty readStoreTy) (freshValue input).2 ≤ 3 * width ∧
      Q.size (rep.ty (.pair entryTy readStoreTy)) (freshValue input) ≤ 9 * width := by
  have hprod := @sizes.prod_le
  have hb' := hb true
  have hs := readStore_size rep sizes (freshValue input).2 width hh hb ha
  have he : Q.size (rep.ty entryTy) (freshValue input).1 ≤ 5 * width := by
    dsimp only [freshValue, LanguageRepresentation.ty] at *
    grind only
  refine ⟨he, hs, ?_⟩
  have hp := sizes.prod_le (rep.ty entryTy) (rep.ty readStoreTy) (freshValue input)
  exact hp.trans (by omega)

include laws dataLaws mono

theorem freshExpression_cost (input : F × ReadStore F) (width fieldTime equalityTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ha : Q.size (rep.ty affineTy) input.2.1 ≤ width)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive freshExpression)
      (input, ()) ≤ 2 * fieldTime + equalityTime + 256 * overhead (128 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound freshExpression (input, ())).trans ?_
  have hprod := @sizes.prod_le
  have hsum := @sizes.sum_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hleft := sizes.sum_le (rep.env [.pair scalar readStoreTy]) (rep.env [.pair scalar readStoreTy])
    (.inl (input, ()))
  have hright := sizes.sum_le (rep.env [.pair scalar readStoreTy]) (rep.env [.pair scalar readStoreTy])
    (.inr (input, ()))
  dsimp only [Sum.elim] at hleft hright
  have hfield := hadd input.2.1.2 input.1
  have hequality := heq (input.2.1.2 + input.1) 0
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ h => mono h
  cases h : input.2.2 <;>
    dsimp only [freshExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.castFunction, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.boolBound,
      DataCostLaws.selectBound, Expr.denote, Var.get, arithmetic,
      id, Function.comp_def, Sum.elim] <;>
    simp only [h, Bool.false_eq_true, ite_true, ite_false] <;>
    dsimp only [arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env] at * <;>
    clear hadd heq <;> grind only

theorem freshCode_cost (input : F × ReadStore F) (width fieldTime equalityTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ha : Q.size (rep.ty affineTy) input.2.1 ≤ width)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime) :
    Q.cost (freshCode rep data cost primitive) input ≤
      2 * fieldTime + equalityTime + 260 * overhead (128 * width) := by
  rw [freshCode, QuantitativeStepClass.Realizer.cost_castFunction]
  have he := freshExpression_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
    input width fieldTime equalityTime hh hu hb hf ha hz hadd heq
  have hframe := (LocalBound.pair laws (LocalBound.identity laws (rep.ty (.pair scalar readStoreTy)))
    (dataLaws.unitBound (rep.ty (.pair scalar readStoreTy)))).cost_le input
  have hc := laws.compose (freshFrame rep data)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive freshExpression) input
  have hout := (freshValue_size rep sizes input width hh hb (hf _) ha).2.2
  have hstore := readStore_size rep sizes input.2 width hh hb ha
  have hin : Q.size (rep.ty (.pair scalar readStoreTy)) input ≤ 5 * width := by
    have hp := sizes.prod_le (rep.ty scalar) (rep.ty readStoreTy) input
    have hscalar := hf input.1
    exact hp.trans (by omega)
  have henv : Q.size (rep.env [.pair scalar readStoreTy]) (input, ()) ≤ 7 * width := by
    have hp := sizes.prod_le (rep.ty (.pair scalar readStoreTy)) rep.data.unit (input, ())
    dsimp only at hp
    exact hp.trans (by omega)
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ h => mono h
  rw [freshExpression_value] at hc
  dsimp only [LocalBound.pair, LocalBound.identity, DataCostLaws.unitBound, id] at hframe
  have hframeTime : Q.cost (freshFrame rep data) input ≤ 3 * overhead (128 * width) :=
    hframe.trans (by
      have h₁ := hfee _ (show Q.size (rep.ty (.pair scalar readStoreTy)) input ≤ 128 * width by omega)
      have h₂ := hfee _ (show Q.size (rep.ty (.pair scalar readStoreTy)) input +
        Q.size rep.data.unit () ≤ 128 * width by omega)
      have h₃ := hfee _ (show Q.size (rep.ty (.pair scalar readStoreTy)) input +
        Q.size (rep.env [.pair scalar readStoreTy]) (input, ()) ≤ 128 * width by omega)
      dsimp only [LanguageRepresentation.env] at h₃
      omega)
  have hj := hfee _ (show Q.size (rep.ty (.pair scalar readStoreTy)) input +
      Q.size (rep.env [.pair scalar readStoreTy]) (input, ()) +
      Q.size (rep.ty (.pair entryTy readStoreTy)) (freshValue input) ≤ 128 * width by omega)
  exact hc.trans (by omega)

variable {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include routing

/-- Charge sampling, retaining the explanation, constructing the entry and flag,
and both native control transitions. -/
theorem freshSample_bound (width fieldTime equalityTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime)
    (hd : Bounds control queryCost sampler (fun _ => True)
      (fun c => Q.size (rep.ty scalar) c ≤ width) sampleTime) :
    Bounds control queryCost (freshSample rep data cost primitive sampler)
      (fun p => Q.size (rep.ty affineTy) p.2.1 ≤ width)
      (fun p => Q.size (rep.ty entryTy) p.1 ≤ 5 * width ∧
        Q.size (rep.ty affineTy) p.2.1 ≤ width)
      (sampleTime + 2 * fieldTime + equalityTime + 263 * overhead (128 * width)) := by
  let keep := fun saved : ReadStore F => Q.size (rep.ty affineTy) saved.1 ≤ width
  let fee := overhead (128 * width)
  have hdraw := Bounds.first control queryCost (rep.ty readStoreTy) sampler
    (fun _ => True) (fun c => Q.size (rep.ty scalar) c ≤ width) keep sampleTime fee hd (by
      intro saved hs c hc
      have hstore := readStore_size rep sizes saved width hh hb hs
      exact (routing.retain _ _).trans (mono (by omega)))
  have hconstruct : Bounds control queryCost (Code.atomic (iface := iface) (freshCode rep data cost primitive))
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ keep p.2)
      (fun p => Q.size (rep.ty entryTy) p.1 ≤ 5 * width ∧ keep p.2)
      (2 * fieldTime + equalityTime + 261 * fee) := by
    apply Bounds.atomic
    intro input hi
    have hsize := freshValue_size rep sizes input width hh hb hi.1 hi.2
    have hcost := freshCode_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
      input width fieldTime equalityTime hh hu hb hf hi.2 hz hadd heq
    have hstore := readStore_size rep sizes input.2 width hh hb hi.2
    have hinput := sizes.prod_le (rep.ty scalar) (rep.ty readStoreTy) input
    have hcall := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty (.pair scalar readStoreTy)) input +
        Q.size (rep.ty (.pair entryTy readStoreTy)) (freshValue input) ≤ 128 * width by
          dsimp only [LanguageRepresentation.ty] at *; omega))
    exact ⟨⟨hsize.1, hi.2⟩, by dsimp only [fee] at *; omega⟩
  have hall := Bounds.seq control queryCost _ _ _ _ _ (sampleTime + fee)
    (2 * fieldTime + equalityTime + 261 * fee) fee hdraw hconstruct (by
      intro input hi output ho
      have hsi := readStore_size rep sizes input.2 width hh hb hi.2
      have hso := readStore_size rep sizes output.2 width hh hb ho.2
      have hpi := sizes.prod_le rep.data.unit (rep.ty readStoreTy) input
      have hpo := sizes.prod_le (rep.ty scalar) (rep.ty readStoreTy) output
      have hu' : Q.size rep.data.unit input.1 ≤ width := by cases input.1; exact hu
      exact (routing.sequence _ _).trans (mono (by
        dsimp only [LanguageRepresentation.ty] at *; omega)))
  intro input hi z hzrun
  obtain ⟨hout, ht⟩ := hall input ⟨True.intro, hi⟩ z hzrun
  exact ⟨hout, by dsimp only [fee] at ht; omega⟩

end Signatures.Runtime.SchnorrAGM.Native
