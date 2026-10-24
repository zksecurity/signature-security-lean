import Proofs.Runtime.BackendCacheCost
import Proofs.Runtime.BackendLanguageCorrectness
import Proofs.Runtime.BackendLanguageSize
import VCVio.OracleComp.QueryTracking.ListCache
import VCVio.OracleComp.Constructions.SampleableType.Basic

/-! A compiled association-list cache parameterized by actual sampling code.
This permits derived samplers, including independent scalar pairs, without
adding a whole-cache primitive. The returned list and ambient store are kept
in the semantic statement; cache hits preserve the complete costed execution
when the sampler is replaced.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.SampledCache

universe v w

inductive Draw {Atom : Type} (value : Ty Atom) : Ty Atom → Ty Atom → Type
  | sample : Draw value .unit value

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {Atom I S : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  {spec : OracleSpec I} {iface : Interface (C := C) spec}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  (store : C.Str S) {key val : Ty Atom}
  (sampler : Code Q spec iface rep.data.unit (rep.ty val))

def effect {a b : Ty Atom} (draw : Draw val a b) :
    Code Q spec iface (StepClass.HasProd.prod (rep.ty a) store)
      (StepClass.HasProd.prod (rep.ty b) store) :=
  match draw with | .sample => .first store sampler

@[irreducible] def code (eq : Op (.pair key key) .bool) :
    Code Q spec iface (StepClass.HasProd.prod (rep.env [key, val, .list (.pair key val)]) store)
      (StepClass.HasProd.prod (rep.ty (.pair val (.list (.pair key val)))) store) :=
  Language.compile rep data P primitive store (effect rep store sampler) (cacheGet eq .sample)

omit [Q.HasCategory] QP QS in
theorem lookupValue_lookup [DecidableEq (key.Value base)]
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    lookupValue k default xs =
      match xs.lookup k with | none => (false, default) | some v => (true, v) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨q, v⟩
    by_cases h : q = k
    · subst q; simp [lookupValue]
    · have hb : (k == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      simp [lookupValue, List.lookup_cons, h, hb, ih]

theorem denote (eq : Op (.pair key key) .bool) [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (saved : S) :
    (code rep data P primitive store sampler eq).denote ((k, default, xs, ()), saved) =
      match xs.lookup k with
      | some v => pure ((v, xs), saved)
      | none => (fun v => ((v, (k, v) :: xs), saved)) <$> sampler.denote () := by
  let H : SemanticsM base (Draw val) (StateT S (OracleComp spec)) :=
    fun draw input => match draw with
    | .sample => fun saved => (fun v => (v, saved)) <$> sampler.denote input
  have he : ∀ {a b} (draw : Draw val a b) input saved,
      (effect rep store sampler draw).denote (input, saved) = (H draw input).run saved := by
    intro a b draw input saved
    cases draw
    rfl
  rw [code, Language.compile_denote rep data P primitive store _ H he]
  have hl : (lookup eq).denote P (k, default, xs, ()) = lookupValue k default xs := by
    rw [← Expr.run_value]
    exact lookup_correct P eq heq k default xs
  rw [lookupValue_lookup] at hl
  cases hx : xs.lookup k <;>
    simp [cacheGet, Program.denote, hl, hx, Expr.denote, Var.get, H,
      StateT.run_pure, bind_pure_comp]
  change (fun p => ((p.1, (k, p.1) :: xs), p.2)) <$>
    ((fun v => (v, saved)) <$> sampler.denote ()) = _
  simp only [Functor.map_map]

/-- Exact correspondence to the list-cache handler used by the lazy probability
program. The result includes the updated list, not just the sampled answer. -/
theorem uniform (eq : Op (.pair key key) .bool) [DecidableEq (key.Value base)]
    [SampleableType (val.Value base)] {iface : Interface (C := C) unifSpec}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty val))
    (hs : sampler.denote () = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (saved : S) :
    (code rep data P primitive store sampler eq).denote ((k, default, xs, ()), saved) =
      (fun p => (p, saved)) <$>
        (QueryImpl.ListCache.handler (uniformSampleImpl (spec := key.Value base →ₒ val.Value base)) k).run xs := by
  rw [denote rep data P primitive store sampler eq heq]
  cases hx : xs.lookup k <;>
    simp [QueryImpl.ListCache.handler, StateT.run, hx, hs, Functor.map_map,
      uniformSampleImpl]

theorem hit_run (eq : Op (.pair key key) .bool) [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (other : Code Q spec iface rep.data.unit (rep.ty val))
    (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (saved : S) (value : val.Value base) (h : xs.lookup k = some value) :
    (code rep data P primitive store sampler eq).run control queryCost ((k, default, xs, ()), saved) =
      (code rep data P primitive store other eq).run control queryCost ((k, default, xs, ()), saved) := by
  have hl : (lookup eq).denote P (k, default, xs, ()) = (true, value) := by
    rw [← Expr.run_value, lookup_correct P eq heq, lookupValue_lookup, h]
  simp only [code, cacheGet, Language.compile, Language.withContext, Code.run,
    sequenceRun, retainRun, chargeRun, pure_bind, map_pure, hl, Expr.denote, Var.get, ite_true]

section Bound

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty Atom} → (instr : Op a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : I) → spec.Range i → Nat) (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem bound (eq : Op (.pair key key) .bool) [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (width cap comparisonTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (he : ∀ x y, Q.size (rep.ty key) x ≤ width → Q.size (rep.ty key) y ≤ width →
      (primitiveBound eq).time (x, y) ≤ comparisonTime)
    (hd : Bounds control queryCost sampler (fun _ => True)
      (fun v => Q.size (rep.ty val) v ≤ width) sampleTime)
    (env : Env base [key, val, .list (.pair key val)])
    (hi : CacheCompiler.Input (Q := Q) rep width cap env) (saved : S) (hs : Q.size store saved ≤ width)
    (z : Run ((val.Value base × List (key.Value base × val.Value base)) × S))
    (hz : z ∈ support ((code rep data P primitive store sampler eq).run control queryCost (env, saved))) :
    CacheCompiler.Output (Q := Q) rep width (cap + 1) z.value.1 ∧ z.value.2 = saved ∧
      z.steps ≤ cap * (comparisonTime + 257 * overhead (32 * CacheCompiler.frameWidth width cap)) +
        sampleTime + 133 * overhead (32 * CacheCompiler.frameWidth width cap) := by
  rw [code] at hz
  exact CacheCompiler.cacheGet_sampling_bound rep data P primitive sizes lists laws dataLaws
    primitiveBound mono control queryCost routing store (effect rep store sampler)
    eq .sample heq sampler rfl width cap comparisonTime sampleTime hh hu hb he hd env hi saved hs z hz

end Bound

theorem description (eq : Op (.pair key key) .bool)
    (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (code rep data P primitive store sampler eq).descriptionSize sizes ≤
      sampler.descriptionSize sizes + sizes.localSize (primitive eq) + 250 * allowance + 30 := by
  rw [code]
  have h := Language.compile_descriptionSize sizes allowance laws rep data P primitive dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl) store
    (effect rep store sampler) (fun _ => sampler.descriptionSize sizes + 1)
    (fun instr => by cases instr; rfl)
    (cacheGet eq Draw.sample)
  refine h.trans ?_
  simp only [cacheGet, lookup, lookupBody, Language.descriptionBound,
    Expression.descriptionBound, Expression.variableDescription]
  omega

end Signatures.Runtime.BackendProgram.SampledCache
