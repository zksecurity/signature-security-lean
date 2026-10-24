import Proofs.Runtime.BackendMachine
import Proofs.Runtime.BackendLanguageBudget

/-! Native costs for the store and entry/exit adapters of compiled wrapper
machines. State transitions have separate pre/post invariants, so growing caches
can be written back without assuming that the old capacity remains unchanged. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.MachineCompiler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [SampleableType F]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (samplingCode : SamplingImplementation Q iface rep)
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes laws mono routing

theorem read_bound (store : Ty CryptoAtom) (inv : store.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hs : ∀ saved, inv saved → Q.size (rep.ty store) saved ≤ width) :
    Bounds control queryCost (effects rep data samplingCode store .read) (fun p => inv p.2)
      (fun p => p.1 = p.2 ∧ inv p.2) (4 * overhead (32 * width)) := by
  apply Bounds.atomic
  intro input hi
  obtain ⟨u, saved⟩ := input
  cases u
  have hw := hs saved hi
  have hf := laws.snd rep.data.unit (rep.ty store) ((), saved)
  have hp := laws.pair (QP.snd rep.data.unit (rep.ty store)) (QP.snd rep.data.unit (rep.ty store)) ((), saved)
  have hprod := @sizes.prod_le
  have hcall := routing.localCall
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  exact ⟨⟨rfl, hi⟩, by dsimp only [LanguageRepresentation.ty] at *; grind only⟩

include dataLaws in
theorem write_bound (store : Ty CryptoAtom)
    (before after : store.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hs : ∀ saved, before saved → Q.size (rep.ty store) saved ≤ width)
    (hn : ∀ saved, after saved → Q.size (rep.ty store) saved ≤ width) :
    Bounds control queryCost (effects rep data samplingCode store .write)
      (fun p => after p.1 ∧ before p.2) (fun p => p.1 = () ∧ after p.2)
      (4 * overhead (32 * width)) := by
  apply Bounds.atomic
  intro input hi
  have hw := hs input.2 hi.2
  have hn' := hn input.1 hi.1
  have hf := laws.fst (rep.ty store) (rep.ty store) input
  have hu' := dataLaws.unit (StepClass.HasProd.prod (rep.ty store) (rep.ty store)) input
  have hp := laws.pair (data.unit (StepClass.HasProd.prod (rep.ty store) (rep.ty store)))
    (QP.fst (rep.ty store) (rep.ty store)) input
  have hprod := @sizes.prod_le
  have hcall := routing.localCall
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  exact ⟨⟨rfl, hi.1⟩, by dsimp only [LanguageRepresentation.ty] at *; grind only⟩

variable [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq K] [DecidableEq M] (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

include dataLaws

theorem unary_bound (store : Ty CryptoAtom) {a b : Ty CryptoAtom}
    (source : Program CryptoOp (Machine.Effect store) [a] b)
    (pre : a.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (inv : store.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (post : b.Value (cryptoBase F G₁ G₂ K M) × store.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (width bodyTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : ∀ input, pre input → Q.size (rep.ty a) input ≤ width)
    (hs : ∀ saved, inv saved → Q.size (rep.ty store) saved ≤ width)
    (hb : Bounds control queryCost (program rep data samplingCode cost primitive store source)
      (fun p => pre p.1.1 ∧ inv p.2) post bodyTime) :
    Bounds control queryCost (unary rep data samplingCode cost primitive store source)
      (fun p => pre p.1 ∧ inv p.2) post (bodyTime + 7 * overhead (32 * width)) := by
  intro input hp z hz
  simp only [unary, Code.run, sequenceRun, pure_bind, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  obtain ⟨hout, ht⟩ := hb ((input.1, ()), input.2) hp r hr
  have hi' := hi input.1 hp.1
  have hs' := hs input.2 hp.2
  let inputRep := StepClass.HasProd.prod (rep.ty a) (rep.ty store)
  have hfst := laws.fst (rep.ty a) (rep.ty store) input
  have hsnd := laws.snd (rep.ty a) (rep.ty store) input
  have hunit := dataLaws.unit inputRep input
  have hpair := laws.pair (QP.fst (rep.ty a) (rep.ty store)) (data.unit inputRep) input
  have houter := laws.pair (QP.pair (QP.fst (rep.ty a) (rep.ty store)) (data.unit inputRep))
    (QP.snd (rep.ty a) (rep.ty store)) input
  have hprod := @sizes.prod_le
  have hcall := routing.localCall
  have hseq := routing.sequence
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  refine ⟨hout, ?_⟩
  dsimp only [inputRep, LanguageRepresentation.env] at *
  grind only

omit sizes laws dataLaws mono routing [C.HasOption] in
/-- Reuse a unary routine's certificate when its source body is called inline.
Removing the deterministic entry adapter can only remove nonnegative work.
This preserves the full postcondition and does not equate distinct runtimes. -/
theorem program_bound_of_unary (store : Ty CryptoAtom) {a b : Ty CryptoAtom}
    (source : Program CryptoOp (Machine.Effect store) [a] b)
    (pre : a.Value (cryptoBase F G₁ G₂ K M) × store.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (post : b.Value (cryptoBase F G₁ G₂ K M) × store.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (budget : Nat)
    (hb : Bounds control queryCost (unary rep data samplingCode cost primitive store source) pre post budget) :
    Bounds control queryCost (program rep data samplingCode cost primitive store source)
      (fun p => pre (p.1.1, p.2)) post budget := by
  intro input hp z hz
  obtain ⟨⟨value, u⟩, saved⟩ := input
  cases u
  have h := hb (value, saved) hp
  simp only [unary, Code.run, sequenceRun, pure_bind, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at h
  have hout := h _ ⟨z, hz, rfl⟩
  exact ⟨hout.1, by dsimp at hout; omega⟩

end Signatures.Runtime.BackendProgram.MachineCompiler
