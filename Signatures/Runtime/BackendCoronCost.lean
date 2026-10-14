import Signatures.Runtime.BackendCoronSize
import Signatures.Runtime.BackendLookupCost

/-! Native costs for the actual lookup expressions used by Coron's lazy scalar
and coin caches and by final extraction. Costs come from compiled backend code,
not from the old arithmetic interpreter's step count. `BackendCoronCacheCost`
adds complete cache-control and sampling bounds. `BackendCoronArithmeticCost`,
`BackendCoronReplyBudget`, and `BackendCoronFinishBudget` extend these to group
arithmetic and complete reply/extraction routines. Full solver assembly remains open.
-/

open PFunctor

namespace Signatures.Runtime.Coron

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

include localLaws dataLaws sizes lists mono

theorem scalarLookup_cost (qS : Nat) (m : M) (state : CacheState F M qS)
    (width comparisonTime cap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : state.Messages (fun m => Q.size (rep.ty message) m ≤ width))
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width) (hn : state.size ≤ cap)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (lookup (val := scalar) CryptoOp.messageEq)) (m, 0, state.scalars, ()) ≤
      cap * (comparisonTime + 257 * overhead (128 * ((4 * cap + 1) * width))) +
        32 * overhead (128 * ((4 * cap + 1) * width)) := by
  apply LookupCompiler.lookup_cost_bound (val := scalar) rep data (arithmetic F G₁ G₂ M M cost) primitive
    localLaws dataLaws primitiveBound sizes mono lists CryptoOp.messageEq
    m 0 state.scalars width comparisonTime cap hh hu hb hm (hf 0)
    (fun p hp => ⟨hs.1 p hp, hf p.2⟩) ((Nat.le_max_left _ _).trans hn)
  intro p hp
  exact he p.1 m (hs.1 p hp) hm

theorem coinLookup_cost (qS : Nat) (m : M) (state : CacheState F M qS)
    (width comparisonTime cap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : state.Messages (fun m => Q.size (rep.ty message) m ≤ width))
    (hf : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ width) (hn : state.size ≤ cap)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (lookup (val := boundedNat qS) CryptoOp.messageEq)) (m, 0, state.coins, ()) ≤
      cap * (comparisonTime + 257 * overhead (128 * ((4 * cap + 1) * width))) +
        32 * overhead (128 * ((4 * cap + 1) * width)) := by
  apply LookupCompiler.lookup_cost_bound (val := boundedNat qS) rep data (arithmetic F G₁ G₂ M M cost) primitive
    localLaws dataLaws primitiveBound sizes mono lists CryptoOp.messageEq
    m 0 state.coins width comparisonTime cap hh hu hb hm (hf 0)
    (fun p hp => ⟨hs.2.1 p hp, hf p.2⟩)
    (((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans hn)
  intro p hp
  exact he p.1 m (hs.2.1 p hp) hm

end Signatures.Runtime.Coron
