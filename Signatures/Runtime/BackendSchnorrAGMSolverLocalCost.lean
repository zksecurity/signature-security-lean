import Signatures.Runtime.BackendSchnorrAGMSolver

/-! Primitive-derived local costs for solver initialization and cutoff. The
initial two affine basis cells are built and charged; their capacity reservation
is established rather than supplied as an invariant of the finished solver. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type} [Field F]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

omit [C.HasSum] [C.HasOption] in
theorem initial_reserved (width cap basisCap signedCap fuel : Nat)
    (hc : fuel ≤ cap) (hn : fuel + 2 ≤ basisCap) (hs : fuel ≤ signedCap)
    (g pk : G₁) (hg : Q.size (rep.ty point₁) g ≤ width) (hp : Q.size (rep.ty point₁) pk ≤ width) :
    Handler.ReservedState (Q := Q) rep width cap basisCap signedCap fuel
      ((g, pk), encodeState ({} : State F G₁ M)) := by
  refine ⟨⟨⟨hg, hp⟩, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [encodeState, CacheCompiler.Entries]
    · simp [encodeState]
    · simpa [encodeState, encodeMetadata, Schnorr.AGM.initialRepresentations] using
        (show 2 ≤ basisCap by omega)
    · simp [encodeState, encodeMetadata]
    · simp [encodeState, encodeMetadata]
  · simpa [encodeState] using hc
  · simpa [encodeState, encodeMetadata, Schnorr.AGM.initialRepresentations, Nat.add_comm] using hn
  · simpa [encodeState, encodeMetadata] using hs

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes lists laws dataLaws primitiveBound mono

theorem initial_cost (width fieldTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : Q.size rep.data.bool false ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width) (ho : Q.size (rep.ty scalar) (1 : F) ≤ width)
    (hzero : (primitiveBound .zero).time () ≤ fieldTime) (hone : (primitiveBound .one).time () ≤ fieldTime)
    (input : Env (cryptoBase F G₁ G₂ K M) inputTypes) (hi : Q.size (rep.env inputTypes) input ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive initialExpression) input ≤
      4 * fieldTime + 1024 * overhead (1024 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound initialExpression input).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := @lists.nil_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 1024 * width, overhead n ≤ overhead (1024 * width) := fun _ hn => mono hn
  dsimp only [initialExpression, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.nilBound, DataCostLaws.consBound, DataCostLaws.boolBound,
    inputTypes, LanguageRepresentation.ty, LanguageRepresentation.env, Expr.denote, Var.get, arithmetic] at *
  grind only

omit [C.HasOption] sizes lists in
theorem cutoff_cost (input : Unit × ((G₁ × G₁) × EncodedState F G₁ M)) (width fieldTime : Nat)
    (hu : Q.size rep.data.unit () ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input ≤ width)
    (hzero : (primitiveBound .zero).time () ≤ fieldTime) :
    Q.cost (Q.compose (data.unit (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy))) (primitive CryptoOp.zero)) input ≤
      fieldTime + 2 * overhead (32 * width) := by
  have ht := (LocalBound.compose laws (dataLaws.unitBound (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)))
    (primitiveBound .zero)).cost_le input
  refine ht.trans ?_
  change overhead (Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input + Q.size rep.data.unit ()) +
    (primitiveBound .zero).time () + overhead
      (Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input + Q.size rep.data.unit () +
        Q.size (rep.ty scalar) (0 : F)) ≤ _
  have hunit := mono (show Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input +
    Q.size rep.data.unit () ≤ 32 * width by omega)
  have hcompose := mono (show Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input +
    Q.size rep.data.unit () + Q.size (rep.ty scalar) (0 : F) ≤ 32 * width by omega)
  omega

variable {iface : BackendProgram.Interface (C := C) unifSpec}
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include routing

omit [C.HasOption] sizes lists in
theorem cutoff_bound (width fieldTime : Nat)
    (hu : Q.size rep.data.unit () ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hzero : (primitiveBound .zero).time () ≤ fieldTime) :
    Bounds control queryCost (cutoff (iface := iface) rep data cost primitive)
      (fun input => Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input ≤ width)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (fieldTime + 3 * overhead (32 * width)) := by
  apply Bounds.atomic
  intro input hi
  have ht := cutoff_cost rep data cost primitive laws dataLaws primitiveBound mono input width fieldTime hu hz hi hzero
  have hc := (routing.localCall _ _).trans (mono (show
    Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input + Q.size (rep.ty scalar) (0 : F) ≤
      32 * width by omega))
  refine ⟨hz, ?_⟩
  change Q.cost (Q.compose (data.unit (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy))) (primitive CryptoOp.zero)) input +
    control.localCall (Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input) (Q.size (rep.ty scalar) (0 : F)) ≤ _
  omega

omit lists dataLaws primitiveBound [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem projection_bound (width : Nat) :
    Bounds control queryCost (.atomic (iface := iface) (QP.fst (rep.ty scalar) (rep.ty stateTy)))
      (fun input => Q.size (rep.ty Read.outputTy) input ≤ width)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (2 * overhead (32 * width)) := by
  apply Bounds.atomic
  intro input hi
  have ho := (sizes.fst_le (rep.ty scalar) (rep.ty stateTy) input).trans hi
  have ht := laws.fst (rep.ty scalar) (rep.ty stateTy) input
  have hc := routing.localCall (Q.size (rep.ty Read.outputTy) input) (Q.size (rep.ty scalar) input.1)
  have hm := mono (show Q.size (rep.ty Read.outputTy) input + Q.size (rep.ty scalar) input.1 ≤ 32 * width by omega)
  refine ⟨ho, ?_⟩
  change Q.cost (QP.fst (rep.ty scalar) (rep.ty stateTy)) input +
    control.localCall (Q.size (rep.ty Read.outputTy) input) (Q.size (rep.ty scalar) input.1) ≤ _
  change Q.cost (QP.fst (rep.ty scalar) (rep.ty stateTy)) input ≤
    overhead (Q.size (rep.ty Read.outputTy) input + Q.size (rep.ty scalar) input.1) at ht
  omega

end Signatures.Runtime.SchnorrAGM.Native.Solver
