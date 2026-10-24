import Proofs.Runtime.BackendBudget
import Proofs.Runtime.GeneralCaller

/-! A typed semantic view of an already implemented native dispatcher. Its
costed handler uses exactly the dispatcher's actual run and step count. Matching
indices prove that decoding's fallback is unreachable and allow exact generic
caller composition. This is a mathematical factorization, not additional
unpriced executable decoding or an assumed handler runtime. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.IndexedHandler

variable {I J S : Type} {source : OracleSpec I} {target : OracleSpec J} [DecidableEq I]

def decode (fallback : (i : I) → source.Range i) (i : I) (reply : (Σ j, source.Range j)) : source.Range i :=
  if h : reply.1 = i then h ▸ reply.2 else fallback i

theorem decode_mk (fallback : (i : I) → source.Range i) (i : I) (reply : source.Range i) :
    decode fallback i ⟨i, reply⟩ = reply := by simp [decode]

theorem repack_decode (fallback : (i : I) → source.Range i) (i : I)
    (reply : (Σ j, source.Range j)) (hi : reply.1 = i) : (⟨i, decode fallback i reply⟩ : (Σ j, source.Range j)) = reply := by
  obtain ⟨j, r⟩ := reply
  dsimp only at hi
  subst j
  simp [decode]

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {iface : Interface (C := C) target}
  {request : C.Str I} {response : C.Str (Σ j, source.Range j)} {store : C.Str S}
  (control : ControlCosts) (queryCost : (j : J) → target.Range j → Nat)
  (code : Code Q target iface (StepClass.HasProd.prod request store) (StepClass.HasProd.prod response store))
  (fallback : (i : I) → source.Range i)

def handler : GeneralCaller.Handler (spec := source) (StateT S (OracleComp target)) :=
  fun i saved => (fun z => (⟨decode fallback i z.value.1, z.steps⟩, z.value.2)) <$>
    code.run control queryCost (i, saved)

def Matches : Prop :=
  ∀ i saved z, z ∈ support (code.run control queryCost (i, saved)) → z.value.1.1 = i

theorem handler_run (hmatches : Matches control queryCost code) (i : I) (saved : S) :
    code.run control queryCost (i, saved) =
      (fun p => (⟨(⟨i, p.1.value⟩, p.2), p.1.steps⟩ : Run ((Σ j, source.Range j) × S))) <$>
        ((handler control queryCost code fallback i).run saved) := by
  simp only [handler, StateT.run, Functor.map_map]
  symm
  rw [← bind_pure_comp]
  calc
    _ = code.run control queryCost (i, saved) >>= pure := by
      apply bind_congr_of_forall_mem_support
      intro z hz
      have he := repack_decode fallback i z.value.1 (hmatches i saved z hz)
      cases z with
      | mk value steps =>
        cases value with
        | mk reply saved' =>
          simp only [he]
    _ = _ := by simp

omit [DecidableEq I] in
theorem matches_of_denote (H : QueryImpl source (StateT S (OracleComp target)))
    (he : ∀ i saved, code.denote (i, saved) = (fun p => (⟨i, p.1⟩, p.2)) <$> (H i).run saved) :
    Matches control queryCost code := by
  intro i saved z hz
  have hv := Code.value_mem_denote control queryCost code (i, saved) z hz
  rw [he] at hv
  simp only [support_map, Set.mem_image] at hv
  obtain ⟨p, _, hp⟩ := hv
  rw [← hp]

theorem handler_erase (H : QueryImpl source (StateT S (OracleComp target)))
    (he : ∀ i saved, code.denote (i, saved) = (fun p => (⟨i, p.1⟩, p.2)) <$> (H i).run saved)
    (i : I) (saved : S) :
    (fun p => (p.1.value, p.2)) <$> ((handler control queryCost code fallback i).run saved) = (H i).run saved := by
  change (fun p : Run (source.Range i) × S => (p.1.value, p.2)) <$>
    ((fun z : Run ((Σ j, source.Range j) × S) => (⟨decode fallback i z.value.1, z.steps⟩, z.value.2)) <$>
      code.run control queryCost (i, saved)) = _
  simp only [Functor.map_map]
  calc
    _ = (fun p => (decode fallback i p.1, p.2)) <$> code.denote (i, saved) := by
      rw [← Code.run_erase control queryCost]
      simp only [Functor.map_map]
    _ = _ := by
      rw [he]
      simp [Functor.map_map, decode]

end Signatures.Runtime.BackendProgram.IndexedHandler
