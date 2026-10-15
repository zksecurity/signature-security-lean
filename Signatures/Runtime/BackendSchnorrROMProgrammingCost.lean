import Signatures.Runtime.BackendSchnorrROMComparison
import Signatures.Runtime.BackendCacheExprBudget
import Signatures.Runtime.BackendCacheProgramming
import Signatures.Runtime.PolynomialResources

/-! The exact first-entry-preserving cache update used by ordinary Schnorr ROM
signing. Its inlined lookup, retained result, branch and possible insertion are
all charged from primitive backend laws. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeCache

open BackendProgram

def programmingTime (overhead : Nat → Nat) (width cap messageTime pointTime : Nat) : Nat :=
  scanTime overhead width cap messageTime pointTime +
    128 * overhead (128 * CacheProgramming.frameWidth width cap)

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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes lists laws dataLaws mono

omit sizes lists laws dataLaws mono in
theorem programming_value (k : M × G₁) (v : F) (xs : List ((M × G₁) × F)) :
    (cacheProgram (val := scalar) hashEq).denote (arithmetic F G₁ G₂ K M cost) (k, v, xs, ()) =
      CacheProgramming.value k v xs := by
  rw [← Expr.run_value, cacheProgram_value _ _ (hashEq_value cost), lookupValue_cacheMap]
  unfold CacheProgramming.value
  cases cacheMap xs k <;> rfl

omit sizes lists laws dataLaws mono [C.HasSum] [C.HasOption] [Q.HasCategory] QP QS in
theorem programming_property (width cap : Nat) (k : M × G₁) (v : F) (xs : List ((M × G₁) × F))
    (hi : CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep width cap (k, v, xs, ())) :
    CacheCompiler.Entries (Q := Q) (key := hashKey) (val := scalar) rep width
        ((cacheProgram (val := scalar) hashEq).denote (arithmetic F G₁ G₂ K M cost) (k, v, xs, ())) ∧
      ((cacheProgram (val := scalar) hashEq).denote (arithmetic F G₁ G₂ K M cost) (k, v, xs, ())).length ≤ cap + 1 := by
  rw [programming_value cost]
  exact CacheProgramming.property (key := hashKey) (val := scalar) rep width cap k v xs hi

theorem programming_expression_time (width cap messageTime pointTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ width → Q.size (rep.ty point₁) y ≤ width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (k : M × G₁) (v : F) (xs : List ((M × G₁) × F))
    (hi : CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep width cap (k, v, xs, ())) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (cacheProgram (val := scalar) hashEq)).time (k, v, xs, ()) ≤
      programmingTime overhead width cap messageTime pointTime := by
  let W := CacheProgramming.frameWidth width cap
  have hw : width ≤ W := by dsimp [W, CacheProgramming.frameWidth]; nlinarith
  have hin := CacheCompiler.input_size (key := hashKey) (val := scalar) rep sizes lists width cap hh hu (k, v, xs, ()) hi
  have hv := CacheCompiler.lookupExpr_value_size (val := scalar) rep (arithmetic F G₁ G₂ K M cost) hashEq
    (hashEq_value cost) width cap (k, v, xs, ()) hi
  have hp := sizes.prod_le rep.data.bool (rep.ty scalar)
    ((lookupExpr (val := scalar) hashEq).denote (arithmetic F G₁ G₂ K M cost) (k, v, xs, ()))
  have hb' := hb ((lookupExpr (val := scalar) hashEq).denote (arithmetic F G₁ G₂ K M cost) (k, v, xs, ())).1
  have hscan := lookup_expression_time rep data cost primitive sizes laws dataLaws primitiveBound mono lists
    width cap messageTime pointTime hh hu hb hm hg k v xs hi
  exact CacheProgramming.withLookup_time_bound rep data (arithmetic F G₁ G₂ K M cost) primitive sizes lists
    laws dataLaws primitiveBound mono (lookupExpr (val := scalar) hashEq) (k, v, xs, ()) W _ (hh.trans hw)
    (hin.trans (by dsimp [W, CacheProgramming.frameWidth]; nlinarith))
    (by change Q.size (StepClass.HasProd.prod rep.data.bool (rep.ty scalar)) _ ≤ _
        dsimp only [W, CacheProgramming.frameWidth]
        nlinarith) hscan

theorem programming_cost (width cap messageTime pointTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ width → Q.size (rep.ty point₁) y ≤ width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (k : M × G₁) (v : F) (xs : List ((M × G₁) × F))
    (hi : CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep width cap (k, v, xs, ())) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (cacheProgram (val := scalar) hashEq))
      (k, v, xs, ()) ≤ programmingTime overhead width cap messageTime pointTime :=
  (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    (cacheProgram (val := scalar) hashEq) (k, v, xs, ())).trans
      (programming_expression_time rep data cost primitive sizes lists laws dataLaws primitiveBound mono
        width cap messageTime pointTime hh hu hb hm hg k v xs hi)

omit sizes lists laws dataLaws mono in
theorem programmingTime_polynomial (overhead : Nat → Nat → Nat)
    (width cap messageTime pointTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) (hMessage : PolynomiallyBounded messageTime)
    (hPoint : PolynomiallyBounded pointTime) :
    PolynomiallyBounded (fun n => programmingTime (overhead n) (width n) (cap n)
      (messageTime n) (pointTime n)) := by
  unfold programmingTime scanTime scanComparisonTime scanFrameWidth CacheProgramming.frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.ListROM.NativeCache
