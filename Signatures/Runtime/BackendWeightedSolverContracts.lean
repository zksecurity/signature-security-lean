import Signatures.Runtime.BackendWeightedSolverPorts
import Signatures.Runtime.BackendWeightedExtractionEntry
import Signatures.Runtime.BackendWeightedExtractionWidth

/-! Individual encoding and operation contracts for native weighted solvers.
Counter bounds cover transcript expansion and target evaluation; key comparisons
are restricted by encoded width. No finished component runtime is supplied. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.NativeSolver

open BackendProgram Reply NativeHandler

def rowCap (index : Index) (cap : Nat) : Nat :=
  cap + cap * (index.bound + 1) + (index.bound + 1)

def terminalFrameWidth (index : Index) (width outputWidth routeWidth cap : Nat) : Nat :=
  routeWidth + handlerStoreWidth index width cap + extractionEntryWidth width cap outputWidth +
    Extract.extractionWidth index (extractionEntryWidth width cap outputWidth) cap cap outputWidth
      (cap * (index.bound + 1)) + width

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M)) (index : Index)

structure ValueCaps (width cap : Nat) : Prop where
  unit : Q.size rep.data.unit () ≤ width
  bool : ∀ b, Q.size rep.data.bool b ≤ width
  nat : ∀ n ≤ rowCap index cap + index.bound + 1, Q.size rep.data.nat n ≤ width
  scalar : ∀ f : F, Q.size (rep.ty scalar) f ≤ width
  point₁ : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width
  point₂ : ∀ g : G₂, Q.size (rep.ty point₂) g ≤ width
  index : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width

variable [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))

structure OperationCaps (cap keyWidth opTime comparisonTime : Nat) : Prop where
  natEq : ∀ j k, j ≤ rowCap index cap + index.bound → k ≤ rowCap index cap + index.bound →
    (primitiveBound .natEq).time (j, k) ≤ opTime
  natSub : ∀ n ≤ rowCap index cap, (primitiveBound .natSub).time (n, 1) ≤ opTime
  natAdd : ∀ n ≤ rowCap index cap, (primitiveBound .natAdd).time (n, 1) ≤ opTime
  keyEq : ∀ x y : K, Q.size (rep.ty key) x ≤ keyWidth → Q.size (rep.ty key) y ≤ keyWidth →
    (primitiveBound .keyEq).time (x, y) ≤ comparisonTime
  finVal : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ opTime
  finOfNat : ∀ n ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time n ≤ opTime
  finZero : (primitiveBound (.finZero index.bound)).time () ≤ opTime
  zero : (primitiveBound .zero).time () ≤ opTime
  one : (primitiveBound .one).time () ≤ opTime
  add : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ opTime
  mul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ opTime
  sub : ∀ x y : F, (primitiveBound .sub).time (x, y) ≤ opTime
  neg : ∀ x : F, (primitiveBound .neg).time x ≤ opTime
  div : ∀ x y : F, (primitiveBound .div).time (x, y) ≤ opTime
  scale₁ : ∀ x : F, ∀ g : G₁, (primitiveBound .scale₁).time (x, g) ≤ opTime
  scale₂ : ∀ x : F, ∀ g : G₂, (primitiveBound .scale₂).time (x, g) ≤ opTime
  groupAdd : ∀ g h : G₁, (primitiveBound .add₁).time (g, h) ≤ opTime

/-- Preserved quantitative store bounds together with the semantic invariant
established by the preceding native interaction. -/
def ExtractionReady (value config : Ty CryptoAtom) (width cap : Nat)
    (saved : (storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  ReservedState (Q := Q) rep index width cap 0 saved ∧
    Model.LazyAGM.WeightedReduction.TranscriptCached (index.sourceTerms cost)
      (chronological saved.2.2) saved.2.1

end Signatures.Runtime.WeightedAGM.NativeSolver
