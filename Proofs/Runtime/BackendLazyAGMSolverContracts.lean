import Proofs.Runtime.BackendLazyAGMSolverState

/-! Inspectable primitive contracts for complete native AGM solver bounds.
The common operation allowance can be the maximum of separately proved prices;
it prices individual implemented operations, never a completed reduction. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))

structure ValueCaps (width queryCap : Nat) : Prop where
  unit : Q.size rep.data.unit () ≤ width
  bool : ∀ b, Q.size rep.data.bool b ≤ width
  nat : ∀ n ≤ queryCap + 1, Q.size rep.data.nat n ≤ width
  scalar : ∀ f : F, Q.size (rep.ty scalar) f ≤ width
  point₁ : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width
  point₂ : ∀ g : G₂, Q.size (rep.ty point₂) g ≤ width

variable [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))

structure OperationCaps (queryCap messageWidth opTime comparisonTime : Nat) : Prop where
  natEq : ∀ n ≤ queryCap, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ opTime
  natSub : ∀ n ≤ queryCap, (primitiveBound CryptoOp.natSub).time (n, 1) ≤ opTime
  natAdd : ∀ n ≤ queryCap, (primitiveBound CryptoOp.natAdd).time (n, 1) ≤ opTime
  messageEq : ∀ x y : M, Q.size (rep.ty message) x ≤ messageWidth → Q.size (rep.ty message) y ≤ messageWidth →
    (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime
  zero : (primitiveBound CryptoOp.zero).time () ≤ opTime
  groupZero : (primitiveBound CryptoOp.zero₁).time () ≤ opTime
  add : ∀ x y : F, (primitiveBound CryptoOp.add).time (x, y) ≤ opTime
  mul : ∀ x y : F, (primitiveBound CryptoOp.mul).time (x, y) ≤ opTime
  sub : ∀ x y : F, (primitiveBound CryptoOp.sub).time (x, y) ≤ opTime
  neg : ∀ x : F, (primitiveBound CryptoOp.neg).time x ≤ opTime
  div : ∀ x y : F, (primitiveBound CryptoOp.div).time (x, y) ≤ opTime
  scale₁ : ∀ x : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (x, g) ≤ opTime
  scale₂ : ∀ x : F, ∀ g : G₂, (primitiveBound CryptoOp.scale₂).time (x, g) ≤ opTime
  groupAdd : ∀ g h : G₁, (primitiveBound CryptoOp.add₁).time (g, h) ≤ opTime

end Signatures.Runtime.LazyAGM.NativeSolver
