import Signatures.Runtime.HeapMachine

/-! Initialization and execution of a closed machine on the shared bit heap.
Input registers are represented on entry; storage is constructed by compiled
code, not supplied by a host initializer. Sampling failure remains observable. -/

namespace Signatures.Runtime.HeapMachine

open HeapBits SharedHeap OracleComp WeierstrassCurve

structure Code where
  storage : Ty CryptoAtom
  init : HeapExpression.Code
  body : HeapProgram.Code (Instruction storage)

def compile (w r : Nat) {p₁ p₂ : Nat} (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂))
    (k : Nat) {Γ a} (code : Machine.Code Γ a) : Code :=
  ⟨code.store, HeapExpression.compile w r W₁ W₂ code.init,
    compileBody w r W₁ W₂ k code.body⟩

def Code.run (code : Code) (frame : List Bool) (store : Store) :
    OracleComp BitRejection.bitSpec (Run HeapExpression.Result × Bool) := do
  let initial := code.init.run frame store
  match initial.value with
  | none => pure (⟨none, initial.steps+1⟩, false)
  | some (root, next) =>
    let out ← (code.body.run Instruction.run frame next).run (root, false)
    pure (⟨out.1.value, initial.steps+out.1.steps+2⟩, out.2.2)

def budget (w r k nodes : Nat) {Γ a} (code : Machine.Code Γ a) : Nat :=
  max 1 (max (HeapExpression.budget w nodes code.init)
    (HeapProgram.budget w nodes (fee w r k nodes) code.body))

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]
  [SampleableType (ZMod r)]

/-- Reference-only values and source costs, driven by the same fair-bit tree. -/
noncomputable def codeSemantics (k : Nat) (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Machine.Code Γ a) (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) :
    OracleComp BitRejection.bitSpec (Run (a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) × Bool) := do
  let initial := code.init.run (arithmetic (ZMod r) H₁ H₂ K M cost) env
  let out ← (code.body.run (arithmetic (ZMod r) H₁ H₂ K M cost)
    (semantics H₁ H₂ (w := w) k sampling code.store) env).run (initial.value, false)
  pure (⟨out.1.value, initial.steps+out.1.steps+2⟩, out.2.2)

/-- Forgetting the marked sampler failure preserves support and source costs.
This is not a claim of equality of the two probability distributions. -/
theorem codeSemantics_support (k : Nat) (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Machine.Code Γ a) (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ)
    (out) (hout : out ∈ support (codeSemantics H₁ H₂ (w := w) k cost sampling code env)) :
    out.1 ∈ support (code.run cost sampling env) := by
  simp only [codeSemantics, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨body, hb, rfl⟩ := hout
  have h := code.body.run_support_refines (arithmetic (ZMod r) H₁ H₂ K M cost) Prod.fst
    (semantics H₁ H₂ (w := w) k sampling code.store) (Machine.effects sampling code.store)
    (semantics_support H₁ H₂ (w := w) k sampling code.store) env _ body hb
  simp only [Machine.Code.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  exact ⟨(body.1, body.2.1), h, rfl⟩

/-- The whole closed code, including initialization, refines the marked bit
semantics and meets a bit-step budget derived from the original ideal machine.
Only the input frame is assumed encoded; no initialized storage is assumed. -/
theorem compile_costed
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) (k : Nat) (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n))
    {Γ a} (code : Machine.Code Γ a) (heap : List Node) (roots : List Address)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (store : Store)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : EnvRep w (atomRep H₁ H₂ encodeK encodeM) heap roots env)
    (bits B : Nat) (hebits : NaturalRange.EnvBound bits env) (hwidth : bits+B ≤ w)
    (hb : ∀ out ∈ support (code.run cost sampling env), out.steps ≤ B) :
    QueryTreeRel (fun actual source =>
      HeapExpression.ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM)
        heap source.1.steps source.1.value actual.1 ∧
      actual.2 = source.2 ∧
      actual.1.steps ≤ source.1.steps * budget w r k (heap.length+B) code ∧
      actual.1.steps ≤ B * budget w r k (heap.length+B) code)
      ((compile w r W₁ W₂ k code).run (frameBits roots) store)
      (codeSemantics H₁ H₂ (w := w) k cost sampling code env) := by
  let P := arithmetic (ZMod r) H₁ H₂ K M cost
  let initial := code.init.run P env
  let H : HandlerM (cryptoBase (ZMod r) H₁ H₂ K M) (Machine.Effect code.store)
      (StateT (code.store.Value (cryptoBase (ZMod r) H₁ H₂ K M) × Bool)
        (OracleComp BitRejection.bitSpec)) := semantics H₁ H₂ (w := w) k sampling code.store
  let factor := budget w r k (heap.length+B) code
  have hbody : ∀ out ∈ support ((code.body.run P H env).run (initial.value, false)),
      initial.steps+out.1.steps+2 ≤ B := by
    intro out hout
    apply hb ⟨out.1.value, initial.steps+out.1.steps+2⟩
    exact codeSemantics_support H₁ H₂ k cost sampling code env _
      (by simp only [codeSemantics, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
          exact ⟨out, hout, rfl⟩)
  obtain ⟨someOut, hsome⟩ := support_nonempty ((code.body.run P H env).run (initial.value, false))
  have hiB : initial.steps ≤ B := by have := hbody someOut hsome; omega
  have ht := NaturalRange.expr_trace_bound cost code.init bits w env hebits (by
    change bits+initial.steps ≤ w; omega)
  have hinit := HeapExpression.compile_spec H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
    cost code.init heap roots env store hs hw he ht
  have hicost := HeapExpression.compile_steps H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
    cost code.init heap roots env store hs hw he ht (heap.length+B) factor
    (by change heap.length+initial.steps ≤ heap.length+B; omega)
    ((le_max_left _ _).trans (le_max_right _ _))
  obtain ⟨extra, root, next, hv, hs', hw', hx, hlen⟩ := hinit
  have hstate := NaturalRange.expr_bound cost code.init bits env hebits
  have htBody := NaturalRange.program_trace_bound cost H
    (fun d s => NaturalRange.ValueBound d s.1)
    (fun h _ hs => NaturalRange.value_mono h _ hs)
    (semantics_bound H₁ H₂ (w := w) k sampling hsampling code.store)
    code.body (bits+initial.steps) w env
    (NaturalRange.env_mono (by omega) env hebits) (initial.value, false) hstate
    (fun out hout => by have := hbody out hout; omega)
  have hrun := HeapProgram.compile_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost
    (heap.length+B) factor (fee w r k (heap.length+B)) H (handler w r k)
    (StateRel H₁ H₂ encodeK encodeM code.store)
    (fun _ more _ _ h => stateRel_append H₁ H₂ encodeK encodeM h more)
    (fun cmd current addr st impl x state hs hw hx hi _ hn =>
      (handler_costed H₁ H₂ encodeK encodeM k (heap.length+B) sampling cmd
        current addr st impl x state hs hw hx hi hn).mono
        (fun actual source h => ⟨h.1, h.2.trans (Nat.le_add_left _ _)⟩))
    code.body (heap ++ extra) roots env next (root, false) (initial.value, false)
    hs' hw' (he.append extra) ⟨hx, rfl⟩ htBody
    (fun out hout => by
      have := hbody out hout
      change extra.length ≤ initial.steps at hlen
      simp only [List.length_append]
      omega)
    ((le_max_right _ _).trans (le_max_right _ _))
  change QueryTreeRel _ _ ((code.body.run P H env).run (initial.value, false)) at hrun
  have hfinal := hrun.with_support.map
    (fun out => (⟨out.1.value,
      ((HeapExpression.compile w r W₁ W₂ code.init).run (frameBits roots) store).steps+out.1.steps+2⟩,
      out.2.2))
    (fun out => (⟨out.1.value, initial.steps+out.1.steps+2⟩, out.2.2))
    (S := fun (actual : Run HeapExpression.Result × Bool)
      (source : Run (a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) × Bool) =>
      HeapExpression.ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM)
        heap source.1.steps source.1.value actual.1 ∧
      actual.2 = source.2 ∧ actual.1.steps ≤ source.1.steps*factor ∧ actual.1.steps ≤ B*factor)
    (by
      intro actual source h
      obtain ⟨more, addr, last, ho, hstore, hwell, hvalue, hstate, halloc⟩ := h.2.2.1
      have hcost := h.2.2.2
      have hbudget := hbody source h.2.1
      have hf : 1 ≤ factor := le_max_left _ _
      have hc : ((HeapExpression.compile w r W₁ W₂ code.init).run (frameBits roots) store).steps +
          actual.1.steps+2 ≤ (initial.steps+source.1.steps+2)*factor := by
        change _ ≤ initial.steps*factor at hicost
        simp only [Nat.add_mul]
        omega
      refine ⟨?_, hstate.2, hc, hc.trans (Nat.mul_le_mul_right factor hbudget)⟩
      refine ⟨extra ++ more, addr, last, ho, ?_, ?_, ?_, ?_⟩
      · simpa only [List.append_assoc] using hstore
      · simpa only [List.append_assoc] using hwell
      · simpa only [List.append_assoc] using hvalue
      · change extra.length ≤ initial.steps at hlen
        simp only [List.length_append]
        omega)
  simp only [Code.run, compile, hv, compileBody, HeapProgram.Code.run_mapQueries,
    codeSemantics, bind_pure_comp]
  convert hfinal using 1
  rfl

end Signatures.Runtime.HeapMachine
