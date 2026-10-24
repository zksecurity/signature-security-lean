import Proofs.Runtime.BackendCacheProgramming
import Proofs.Runtime.BackendSchnorrAGMComparison
import Proofs.Runtime.BackendStructuredCache

/-! Native programming of Schnorr signing challenges. The input includes the
supplied encoded entry; this routine never samples. Existing entries, including
their original affine explanations and shadowed duplicates, remain unchanged. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Programming

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def code : Code Q unifSpec iface (rep.env [cacheKeyTy, entryTy, cacheTy]) (rep.ty cacheTy) :=
  .atomic (Expression.compile rep data
    (StructuredCache.operations rep (comparison rep data cost primitive))
    (StructuredCache.implementation rep (comparison rep data cost primitive))
    (CacheProgramming.expression .equal))

theorem denote (k : M × G₁) (v : EncodedEntry F) (xs : List ((M × G₁) × EncodedEntry F)) :
    (code rep data cost primitive (iface := iface)).denote (k, v, xs, ()) =
      pure (CacheProgramming.value k v xs) := by
  simp only [code, Code.denote]
  rw [CacheProgramming.denote _ _ (fun _ _ => rfl)]

/-- This is exactly the cache component of the source signing update. History
append, response arithmetic and sampling are separate parts of the signing handler. -/
theorem source (s : State F G₁ M) (g pk : G₁) (m : M) (c z : F) :
    (code rep data cost primitive (iface := iface)).denote
      ((m, z • g - c • pk), (c, false, 0, 0), (encodeState s).1, ()) =
      pure (encodeState (signedState s g pk m c z)).1 := by
  rw [denote]
  simp only [CacheProgramming.value, encodeState, cacheMap_encode, signedState]
  cases cacheMap s.cache (m, z • g - c • pk) <;>
    simp [encodeEntry]

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    (code rep data cost primitive (iface := iface)).descriptionSize sizes ≤
      primitiveSize .messageEq + primitiveSize .point₁Eq + 264 * allowance + 1 := by
  have h := CacheProgramming.description rep data
    (StructuredCache.operations rep (comparison rep data cost primitive))
    (StructuredCache.implementation rep (comparison rep data cost primitive))
    (val := entryTy) .equal sizes allowance laws dataLaws
  have hc := comparison_description rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
  dsimp only [StructuredCache.implementation] at h
  have htotal := h.trans (Nat.add_le_add_right hc (200 * allowance))
  dsimp only [code, Code.descriptionSize]
  exact (Nat.add_le_add_right htotal 1).trans (by omega)

def programmingTime (overhead : Nat → Nat) (width cap messageTime pointTime : Nat) : Nat :=
  CacheProgramming.programmingTime overhead width cap
    (messageTime + pointTime + 134 * overhead (128 * width)) +
      overhead (128 * CacheProgramming.frameWidth width cap)

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem bound (width cap messageTime pointTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ width → Q.size (rep.ty message) b ≤ width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ width → Q.size (rep.ty point₁) b ≤ width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime) :
    Bounds control queryCost (code rep data cost primitive (iface := iface))
      (CacheCompiler.Input (Q := Q) rep width cap)
      (fun xs => CacheCompiler.Entries (Q := Q) rep width xs ∧ xs.length ≤ cap + 1)
      (programmingTime overhead width cap messageTime pointTime) := by
  apply Bounds.atomic
  rintro ⟨k, v, xs, u⟩ hi
  cases u
  have hout := CacheProgramming.property rep width cap k v xs hi
  have ht := CacheProgramming.cost rep data
    (StructuredCache.operations rep (comparison rep data cost primitive))
    (StructuredCache.implementation rep (comparison rep data cost primitive))
    sizes lists laws dataLaws
    (fun call => LocalBound.measured (StructuredCache.implementation rep (comparison rep data cost primitive) call))
    mono .equal (fun _ _ => rfl) width cap
    (messageTime + pointTime + 134 * overhead (128 * width)) hh hu hb k v xs hi
    (by
      intro p hp
      exact comparison_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
        p.1 k width messageTime pointTime hh hu hb (hi.2.2.1 p hp).1 hi.1 hm hg)
  have hin := CacheCompiler.input_size rep sizes lists width cap hh hu (k, v, xs, ()) hi
  have hsize := CacheCompiler.list_size rep sizes lists (CacheProgramming.value k v xs)
    width (cap + 1) hh hout.1 hout.2
  rw [CacheProgramming.denote _ _ (fun _ _ => rfl)]
  refine ⟨hout, ?_⟩
  have hc := (routing.localCall
    (Q.size (rep.env [cacheKeyTy, entryTy, cacheTy]) (k, v, xs, ()))
    (Q.size (rep.ty cacheTy) (CacheProgramming.value k v xs))).trans (mono (show
      Q.size (rep.env [cacheKeyTy, entryTy, cacheTy]) (k, v, xs, ()) +
        Q.size (rep.ty cacheTy) (CacheProgramming.value k v xs) ≤
          128 * CacheProgramming.frameWidth width cap by
      dsimp only [CacheProgramming.frameWidth]
      nlinarith))
  dsimp only [programmingTime]
  exact Nat.add_le_add ht hc

end Signatures.Runtime.SchnorrAGM.Native.Programming
