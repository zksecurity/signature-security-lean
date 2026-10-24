import Proofs.Runtime.BackendLookupExprCost
import Proofs.Runtime.BackendCacheCost
import Proofs.Runtime.SchnorrCache

/-! Actual Schnorr structured-key comparisons inside a retained lookup context.
The message and point primitives, projections, branches and full retained
encoding contribute to the native comparison cost. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeCache

open BackendProgram

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes laws dataLaws mono

theorem hashEq_time {Γ : List (Ty CryptoAtom)} (x y : M × G₁) (tail : Env (cryptoBase F G₁ G₂ K M) Γ) (width messageTime pointTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hx : Q.size (rep.ty hashKey) x ≤ width) (hy : Q.size (rep.ty hashKey) y ≤ width)
    (htail : Q.size (rep.env Γ) tail ≤ width)
    (hm : (primitiveBound .messageEq).time (x.1, y.1) ≤ messageTime)
    (hg : (primitiveBound .point₁Eq).time (x.2, y.2) ≤ pointTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (hashEq.weakenTail Γ)).time (x, y, tail) ≤
      messageTime + pointTime + 128 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hsum := @sizes.sum_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hleft := sizes.sum_le (rep.env (hashKey :: hashKey :: Γ)) (rep.env (hashKey :: hashKey :: Γ))
    (.inl (x, y, tail))
  have hright := sizes.sum_le (rep.env (hashKey :: hashKey :: Γ)) (rep.env (hashKey :: hashKey :: Γ))
    (.inr (x, y, tail))
  dsimp only [Sum.elim] at hleft hright
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ h => mono h
  by_cases h : x.1 = y.1 <;>
    dsimp only [hashEq, Expr.weakenTail, Var.weakenTail, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.castFunction, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.boolBound,
      DataCostLaws.selectBound, Expr.denote, Var.get, arithmetic,
      id, Function.comp_def, Sum.elim] <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;>
    dsimp only [arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env, List.append] at * <;>
    simp only [List.cons_append, List.nil_append] at * <;>
    dsimp only [LanguageRepresentation.env] at * <;>
    grind only

def scanFrameWidth (width cap : Nat) : Nat := (16 * cap + 32) * width

def scanComparisonTime (overhead : Nat → Nat) (width cap messageTime pointTime : Nat) : Nat :=
  messageTime + pointTime + 128 * overhead (128 * scanFrameWidth width cap)

def scanTime (overhead : Nat → Nat) (width cap messageTime pointTime : Nat) : Nat :=
  cap * (scanComparisonTime overhead width cap messageTime pointTime +
    513 * overhead (128 * ((4 * cap + 1) * width))) +
      32 * overhead (128 * ((4 * cap + 1) * width))

variable (lists : ListSizeLaws Q rep.data header)

include lists

theorem scan_comparison_time (width cap messageTime pointTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ width → Q.size (rep.ty point₁) y ≤ width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (k : M × G₁) (d : F) (xs : List ((M × G₁) × F))
    (hi : CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep width cap (k, d, xs, ()))
    (p : (M × G₁) × F) (hp : p ∈ xs) (acc : Bool × F)
    (ha : Q.size (rep.ty scalar) acc.2 ≤ (4 * cap + 1) * width) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (hashEq.weakenTail [.pair hashKey scalar, .pair .bool scalar, hashKey, scalar, hashCache])).time
        (p.1, k, p, acc, k, d, xs, ()) ≤ scanComparisonTime overhead width cap messageTime pointTime := by
  let W := scanFrameWidth width cap
  have hw : width ≤ W := by dsimp [W, scanFrameWidth]; nlinarith
  have hk := hi.1
  obtain ⟨hpkey, hpval⟩ := hi.2.2.1 p hp
  have hmessage := hm p.1.1 k.1 ((sizes.fst_le _ _ p.1).trans hpkey) ((sizes.fst_le _ _ k).trans hk)
  have hpoint := hg p.1.2 k.2 ((sizes.snd_le _ _ p.1).trans hpkey) ((sizes.snd_le _ _ k).trans hk)
  have htail : Q.size (rep.env [.pair hashKey scalar, .pair .bool scalar, hashKey, scalar, hashCache])
      (p, acc, k, d, xs, ()) ≤ W := by
    have hlist := CacheCompiler.list_size (key := hashKey) (val := scalar) rep sizes lists xs width cap hh hi.2.2.1 hi.2.2.2
    have hd := hi.2.1
    have hbool := hb acc.1
    have hprod := @sizes.prod_le
    dsimp only [W, scanFrameWidth, LanguageRepresentation.ty, LanguageRepresentation.env, List.append] at *
    grind only
  exact hashEq_time (Γ := [.pair hashKey scalar, .pair .bool scalar, hashKey, scalar, hashCache]) rep data cost primitive sizes laws dataLaws primitiveBound mono p.1 k
    (p, acc, k, d, xs, ()) W messageTime pointTime (hh.trans hw) (hu.trans hw)
    (fun b => (hb b).trans hw) (hpkey.trans hw) (hk.trans hw) htail hmessage hpoint

/-- The scan's entire compiled cost follows from the two comparison primitives
and the list length. Retained contexts are included in every comparison charge. -/
theorem lookup_expression_time (width cap messageTime pointTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ width → Q.size (rep.ty point₁) y ≤ width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (k : M × G₁) (d : F) (xs : List ((M × G₁) × F))
    (hi : CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep width cap (k, d, xs, ())) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (lookupExpr (val := scalar) hashEq)).time (k, d, xs, ()) ≤ scanTime overhead width cap messageTime pointTime := by
  have hw : width ≤ (4 * cap + 1) * width := by nlinarith
  apply LookupExprCompiler.lookup_time_bound_of_caps (val := scalar) rep data (arithmetic F G₁ G₂ K M cost)
    primitive laws dataLaws primitiveBound sizes mono hashEq k d xs ((4 * cap + 1) * width)
    (scanComparisonTime overhead width cap messageTime pointTime) cap (hh.trans hw) (hu.trans hw)
    (fun b => (hb b).trans hw) (hi.1.trans hw) (hi.2.1.trans hw)
    (fun p hp => ⟨(hi.2.2.1 p hp).1.trans hw, (hi.2.2.1 p hp).2.trans hw⟩) hi.2.2.2
  · intro ys hn hy
    exact CacheCompiler.list_size (key := hashKey) (val := scalar) rep sizes lists ys width cap hh
      (fun p hp => hi.2.2.1 p (hy p hp)) hn
  · exact scan_comparison_time rep data cost primitive sizes laws dataLaws primitiveBound mono lists
      width cap messageTime pointTime hh hu hb hm hg k d xs hi

theorem lookup_cost (width cap messageTime pointTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ width → Q.size (rep.ty point₁) y ≤ width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (k : M × G₁) (d : F) (xs : List ((M × G₁) × F))
    (hi : CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep width cap (k, d, xs, ())) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (lookupExpr (val := scalar) hashEq))
      (k, d, xs, ()) ≤ scanTime overhead width cap messageTime pointTime :=
  (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    (lookupExpr (val := scalar) hashEq) (k, d, xs, ())).trans
      (lookup_expression_time rep data cost primitive sizes laws dataLaws primitiveBound mono lists
        width cap messageTime pointTime hh hu hb hm hg k d xs hi)

end Signatures.Runtime.Schnorr.ListROM.NativeCache
