import Signatures.Runtime.BackendCoronReplyBudget

/-! Explicit primitive and encoding contracts shared by the complete native
Coron reply and extraction budgets. None of these contracts prices a cache,
oracle handler, replay, or complete solver as a primitive operation. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Coron

open BackendProgram

def nativeReplyTime (overhead : Nat → Nat)
    (width cap comparisonTime scalarTime coinTime opTime : Nat) : Nat :=
  2 * (cap * (comparisonTime + 257 * overhead (32 * ReplyCompiler.replyFrameWidth width cap))) +
    scalarTime + coinTime + 7 * opTime + 700 * overhead (32 * ReplyCompiler.replyFrameWidth width cap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))

structure NativeValueCaps (qS width : Nat) : Prop where
  unit : Q.size rep.data.unit () ≤ width
  bool : ∀ b, Q.size rep.data.bool b ≤ width
  scalar : ∀ x : F, Q.size (rep.ty Runtime.scalar) x ≤ width
  coin : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ width
  point : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width
  nat : ∀ n ≤ qS, Q.size rep.data.nat n ≤ width

variable [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))

structure NativeInstructionCaps (qS messageWidth comparisonTime opTime : Nat) : Prop where
  message : ∀ x y : M, Q.size (rep.ty Runtime.message) x ≤ messageWidth →
    Q.size (rep.ty Runtime.message) y ≤ messageWidth →
    (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime
  fieldZero : (primitiveBound CryptoOp.zero).time () ≤ opTime
  coinZero : (primitiveBound (CryptoOp.finZero qS)).time () ≤ opTime
  convert : ∀ n : Fin (qS + 1), (primitiveBound (CryptoOp.finVal qS)).time n ≤ opTime
  natEq : ∀ n ≤ qS, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ opTime
  pointZero : (primitiveBound CryptoOp.zero₁).time () ≤ opTime
  scale : ∀ rho : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ opTime
  add : ∀ g h : G₁, (primitiveBound CryptoOp.add₁).time (g, h) ≤ opTime
  sub : ∀ g h : G₁, (primitiveBound CryptoOp.sub₁).time (g, h) ≤ opTime

variable [SampleableType F] {iface : Interface (C := C) unifSpec}
  (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

structure NativeSamplingCaps (qS scalarTime coinTime : Nat) : Prop where
  scalar : ∀ z ∈ support (samplingCode.scalar.run control queryCost ()), z.steps ≤ scalarTime
  coin : ∀ z ∈ support ((samplingCode.uniform qS).run control queryCost ()), z.steps ≤ coinTime

end Signatures.Runtime.Coron
