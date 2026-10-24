import Proofs.Runtime.BackendSampledCache
import Proofs.Runtime.BackendComparison

/-! A lazy cache calling an implemented local comparator. `Call.equal` is an
internal compiler label, implemented by the supplied realizer in the same
backend; its measured cost and complete stored description are charged. In the
weighted schemes that realizer is compiled from the structured-key expressions.
This reuses the cache compiler without assuming a whole-cache primitive. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.StructuredCache

universe v w

inductive Call {Atom : Type} (key : Ty Atom) : Ty Atom → Ty Atom → Type
  | equal : Call key (.pair key key) .bool

theorem lookup_encoded {K L V : Type} [DecidableEq K] [DecidableEq L]
    (encode : K → L) (hi : Function.Injective encode) (k : K) (xs : List (K × V)) :
    (xs.map (Prod.map encode id)).lookup (encode k) = xs.lookup k := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨q, v⟩
    by_cases h : k = q
    · subst q
      simp
    · have he : (encode k == encode q) = false := beq_eq_false_iff_ne.mpr (fun he => h (hi he))
      have hk : (k == q) = false := beq_eq_false_iff_ne.mpr h
      simp [List.lookup_cons, he, hk, ih]

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {Atom I S : Type} {base : Atom → Type}
  {spec : OracleSpec I} {iface : Interface (C := C) spec}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  {key val : Ty Atom} [DecidableEq (key.Value base)]
  (comparison : Q.Realizer (rep.ty (.pair key key)) rep.data.bool (fun p => decide (p.1 = p.2)))
  (store : C.Str S) (sampler : Code Q spec iface rep.data.unit (rep.ty val))

def operations : Primitives base (Call key) where
  execute | .equal => fun p => decide (p.1 = p.2)
  cost | .equal => Q.cost comparison

def implementation {a b : Ty Atom} (call : Call key a b) :
    Q.Realizer (rep.ty a) (rep.ty b) ((operations rep comparison).execute call) :=
  match call with | .equal => comparison

@[irreducible] def code :
    Code Q spec iface (StepClass.HasProd.prod (rep.env [key, val, .list (.pair key val)]) store)
      (StepClass.HasProd.prod (rep.ty (.pair val (.list (.pair key val)))) store) :=
  SampledCache.code rep data (operations rep comparison) (implementation rep comparison)
    store sampler .equal

theorem denote (k : key.Value base) (default : val.Value base)
    (xs : List (key.Value base × val.Value base)) (saved : S) :
    (code rep data comparison store sampler).denote ((k, default, xs, ()), saved) =
      match xs.lookup k with
      | some v => pure ((v, xs), saved)
      | none => (fun v => ((v, (k, v) :: xs), saved)) <$> sampler.denote () := by
  rw [code]
  exact SampledCache.denote rep data (operations rep comparison) (implementation rep comparison)
    store sampler .equal (fun _ _ => rfl) k default xs saved

/-- Exact joint answer/cache correspondence with the probability-level lazy
oracle, including the cache's first-hit behavior and every sampled miss. -/
theorem uniform [SampleableType (val.Value base)] {iface : Interface (C := C) unifSpec}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty val))
    (hs : sampler.denote () = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (k : key.Value base) (default : val.Value base)
    (xs : List (key.Value base × val.Value base)) (saved : S) :
    (code rep data comparison store sampler).denote ((k, default, xs, ()), saved) =
      (fun p => (p, saved)) <$>
        (QueryImpl.ListCache.handler (uniformSampleImpl (spec := key.Value base →ₒ val.Value base)) k).run xs := by
  rw [code]
  exact SampledCache.uniform rep data (operations rep comparison) (implementation rep comparison)
    store Call.equal sampler hs (fun _ _ => rfl) k default xs saved

/-- Injective representations preserve source cache hits and misses, including
shadowed entries. The map is a proof relation between states, not work performed
by cache access and not an enumeration of the source key universe. -/
theorem uniform_encoded [SampleableType (val.Value base)] {iface : Interface (C := C) unifSpec}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty val))
    (hs : sampler.denote () = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    {K : Type} [DecidableEq K] (encode : K → key.Value base) (hi : Function.Injective encode)
    (k : K) (default : val.Value base) (xs : List (K × val.Value base)) (saved : S) :
    (code rep data comparison store sampler).denote
        ((encode k, default, xs.map (Prod.map encode id), ()), saved) =
      (fun p => ((p.1, p.2.map (Prod.map encode id)), saved)) <$>
        (QueryImpl.ListCache.handler (uniformSampleImpl (spec := K →ₒ val.Value base)) k).run xs := by
  rw [denote, lookup_encoded encode hi]
  cases hx : xs.lookup k <;>
    simp [QueryImpl.ListCache.handler, StateT.run, hx, hs, Functor.map_map, uniformSampleImpl]

/-- A hit does not execute the sampler: replacing it leaves the entire costed
run unchanged, including the saved ambient state. -/
theorem hit_run (other : Code Q spec iface rep.data.unit (rep.ty val))
    (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
    (k : key.Value base) (default : val.Value base)
    (xs : List (key.Value base × val.Value base)) (saved : S)
    (value : val.Value base) (hit : xs.lookup k = some value) :
    (code rep data comparison store sampler).run control queryCost ((k, default, xs, ()), saved) =
      (code rep data comparison store other).run control queryCost ((k, default, xs, ()), saved) := by
  rw [code, code]
  exact SampledCache.hit_run rep data (operations rep comparison) (implementation rep comparison)
    store sampler Call.equal (fun _ _ => rfl) other control queryCost k default xs saved value hit

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (code rep data comparison store sampler).descriptionSize sizes ≤
      sampler.descriptionSize sizes + sizes.localSize comparison + 250 * allowance + 30 := by
  rw [code]
  exact SampledCache.description rep data (operations rep comparison) (implementation rep comparison)
    store sampler Call.equal sizes allowance laws dataLaws

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : I) → spec.Range i → Nat) (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem bound (width cap comparisonTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (he : ∀ x y, Q.size (rep.ty key) x ≤ width → Q.size (rep.ty key) y ≤ width →
      Q.cost comparison (x, y) ≤ comparisonTime)
    (hd : Bounds control queryCost sampler (fun _ => True)
      (fun v => Q.size (rep.ty val) v ≤ width) sampleTime)
    (env : Env base [key, val, .list (.pair key val)])
    (hi : CacheCompiler.Input (Q := Q) rep width cap env) (saved : S) (hs : Q.size store saved ≤ width)
    (z : Run ((val.Value base × List (key.Value base × val.Value base)) × S))
    (hz : z ∈ support ((code rep data comparison store sampler).run control queryCost (env, saved))) :
    CacheCompiler.Output (Q := Q) rep width (cap + 1) z.value.1 ∧ z.value.2 = saved ∧
      z.steps ≤ cap * (comparisonTime + 257 * overhead (32 * CacheCompiler.frameWidth width cap)) +
        sampleTime + 133 * overhead (32 * CacheCompiler.frameWidth width cap) := by
  rw [code] at hz
  exact SampledCache.bound rep data (operations rep comparison) (implementation rep comparison)
    store sampler sizes lists laws dataLaws
    (fun call => LocalBound.measured (implementation rep comparison call))
    mono control queryCost routing Call.equal (fun _ _ => rfl)
    width cap comparisonTime sampleTime hh hu hb he hd env hi saved hs z hz

end Signatures.Runtime.BackendProgram.StructuredCache
