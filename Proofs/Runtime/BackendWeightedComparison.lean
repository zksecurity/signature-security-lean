import Proofs.Runtime.BackendWeightedKeyEquality
import Proofs.Runtime.BackendComparison

/-! Compiled comparison routines for both weighted-cache index encodings.
`Index` selects the encoding when the reduction code is constructed; it is not
an extra runtime tag. Every comparison bound below is derived from the original
topic/slot, bounded-index and natural-comparison instructions. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM

open BackendProgram

inductive Index where
  | oops (degree : Nat)
  | proximity (dimension : Nat)
  | sync (weighted : Bool)

def Index.bound : Index → Nat
  | .oops d | .proximity d => d
  | .sync _ => 0

@[reducible] def Index.ty : Index → Ty CryptoAtom
  | .oops d => Weights.oopsKey d
  | .proximity ell => Weights.proximityKey ell
  | .sync _ => key

def Index.expression : (index : Index) → Expr CryptoOp [index.ty, index.ty] .bool
  | .oops d => AGM.KeyEquality.oops d
  | .proximity ell => AGM.KeyEquality.proximity ell
  | .sync _ => AGM.KeyEquality.bls

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

instance Index.valueDecidableEq (index : Index) :
    DecidableEq (index.ty.Value (cryptoBase F G₁ G₂ K M)) := by
  cases index <;> dsimp [Index.ty, Weights.oopsKey, Weights.proximityKey] <;> infer_instance

theorem Index.expression_value (cost : PrimitiveCosts) (index : Index)
    (x y : index.ty.Value (cryptoBase F G₁ G₂ K M)) :
    index.expression.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y) := by
  cases index with
  | oops d => exact AGM.KeyEquality.oops_value cost d x y
  | proximity ell => exact AGM.KeyEquality.proximity_value cost ell x y
  | sync _ => exact AGM.KeyEquality.bls_value cost x y

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def Index.code (index : Index) :
    Q.Realizer (rep.ty (.pair index.ty index.ty)) rep.data.bool (fun p => decide (p.1 = p.2)) :=
  Comparison.code rep data (arithmetic F G₁ G₂ K M cost) primitive index.expression
    (index.expression_value cost)

theorem Index.description (index : Index) (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    sizes.localSize (index.code rep data cost primitive) ≤
      primitiveSize .keyEq + 2 * primitiveSize (.finVal index.bound) +
        primitiveSize .natEq + 70 * allowance := by
  have ha := Comparison.description rep data (arithmetic F G₁ G₂ K M cost) primitive
    index.expression (index.expression_value cost) sizes allowance laws dataLaws
  have he : sizes.localSize (Expression.compile rep data (arithmetic F G₁ G₂ K M cost)
      primitive index.expression) ≤
        primitiveSize .keyEq + 2 * primitiveSize (.finVal index.bound) + primitiveSize .natEq +
          64 * allowance := by
    cases index with
    | oops d =>
      exact AGM.KeyEquality.oops_code_size rep data cost primitive d
        sizes allowance laws dataLaws primitiveSize hp
    | proximity ell =>
      exact AGM.KeyEquality.proximity_code_size rep data cost primitive ell
        sizes allowance laws dataLaws primitiveSize hp
    | sync _ =>
      exact AGM.KeyEquality.bls_code_size rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
  exact ha.trans (by omega)

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes laws dataLaws mono

theorem Index.native_cost (index : Index) (x y : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (width topicTime indexTime natTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ j ≤ index.bound, Q.size rep.data.nat j ≤ width)
    (hx : Q.size (rep.ty index.ty) x ≤ width) (hy : Q.size (rep.ty index.ty) y ≤ width)
    (ht : ∀ a b : K, Q.size (rep.ty key) a ≤ width → Q.size (rep.ty key) b ≤ width →
      (primitiveBound .keyEq).time (a, b) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (he : ∀ j k : Nat, j ≤ index.bound → k ≤ index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natTime) :
    Q.cost (index.code rep data cost primitive) (x, y) ≤
      topicTime + 2 * indexTime + natTime + 134 * overhead (128 * width) := by
  have hc : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      index.expression) (x, y, ()) ≤
        topicTime + 2 * indexTime + natTime + 128 * overhead (128 * width) := by
    cases index with
    | oops d =>
      exact AGM.KeyEquality.oops_cost rep data cost primitive laws dataLaws
        primitiveBound sizes mono d x y width topicTime indexTime natTime hh hu hb hn hx hy ht hi he
    | proximity ell =>
      exact AGM.KeyEquality.proximity_cost rep data cost primitive laws dataLaws
        primitiveBound sizes mono ell x y width topicTime indexTime natTime hh hu hb hn hx hy ht hi he
    | sync _ =>
      exact AGM.KeyEquality.bls_cost rep data cost primitive laws dataLaws
        primitiveBound sizes mono x y width topicTime indexTime natTime hh hu hb hx hy ht
  have ha := Comparison.cost rep data (arithmetic F G₁ G₂ K M cost) primitive sizes laws dataLaws mono
    index.expression (index.expression_value cost) x y width
    (topicTime + 2 * indexTime + natTime + 128 * overhead (128 * width)) hh hu hb hx hy hc
  have hm : overhead (16 * width) ≤ overhead (128 * width) := mono (by omega)
  exact ha.trans (by omega)

end Signatures.Runtime.WeightedAGM
