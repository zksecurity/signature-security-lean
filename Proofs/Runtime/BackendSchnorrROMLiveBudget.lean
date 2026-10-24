import Proofs.Runtime.BackendSchnorrROMCache
import Proofs.Runtime.BackendSchnorrROMComparison
import Proofs.Runtime.BackendCacheExprBudget
import Proofs.Runtime.PolynomialResources

/-! Complete native live-cache runtime with a stateful draw. The scan and key
comparison are derived from the actual compiled expressions. Sampling may
advance the replay-store invariant; hits make no sampling call. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeCache

open BackendProgram

def liveTime (overhead : Nat → Nat) (width cap messageTime pointTime drawTime : Nat) : Nat :=
  cap * (scanComparisonTime overhead width cap messageTime pointTime +
    513 * overhead (32 * CacheCompiler.frameWidth width cap)) + drawTime +
      132 * overhead (32 * CacheCompiler.frameWidth width cap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M S : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (store : C.Str S)
  (draw : Code Q unifSpec iface (StepClass.HasProd.prod rep.data.unit store)
    (StepClass.HasProd.prod (rep.ty scalar) store))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat) (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem live_bound (inv nextInv : S → Prop) (advance : ∀ saved, inv saved → nextInv saved)
    (width cap messageTime pointTime drawTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (hsNext : ∀ saved, nextInv saved → Q.size store saved ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ width → Q.size (rep.ty point₁) y ≤ width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (hd : Bounds control queryCost draw (fun p => inv p.2)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ nextInv p.2) drawTime) :
    Bounds control queryCost (live rep data cost primitive store draw)
      (fun p => CacheCompiler.Input (Q := Q) rep width cap p.1 ∧ inv p.2)
      (fun p => CacheCompiler.Output (Q := Q) rep width (cap + 1) p.1 ∧ nextInv p.2)
      (liveTime overhead width cap messageTime pointTime drawTime) := by
  exact CacheCompiler.cacheGetExpr_bound rep data (arithmetic F G₁ G₂ K M cost) primitive sizes lists
    laws dataLaws primitiveBound mono control queryCost routing store (effect rep store draw)
    hashEq .sample (hashEq_value cost) inv nextInv advance width cap
    (scanComparisonTime overhead width cap messageTime pointTime) drawTime hh hu hb hs hsNext
    (scan_comparison_time rep data cost primitive sizes laws dataLaws primitiveBound mono lists
      width cap messageTime pointTime hh hu hb hm hg) hd

omit sizes lists laws dataLaws mono routing in
theorem liveTime_polynomial (overhead : Nat → Nat → Nat)
    (width cap messageTime pointTime drawTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) (hMessage : PolynomiallyBounded messageTime)
    (hPoint : PolynomiallyBounded pointTime) (hDraw : PolynomiallyBounded drawTime) :
    PolynomiallyBounded (fun n => liveTime (overhead n) (width n) (cap n)
      (messageTime n) (pointTime n) (drawTime n)) := by
  unfold liveTime scanComparisonTime scanFrameWidth CacheCompiler.frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.ListROM.NativeCache
