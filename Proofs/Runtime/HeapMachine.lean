import Proofs.Runtime.PaddedSampling
import Proofs.Runtime.HeapProgramCost
import Proofs.Runtime.Machine
import Proofs.Runtime.SupportRefinement

/-! Concrete heap implementations of every closed-machine effect. Sampling
instructions contain precompiled bit code. State is a shared-heap root plus a
sticky failure flag. The reference semantics below uses the same bit queries;
comparison with ideal randomness is a separate distributional obligation. -/

namespace Signatures.Runtime.HeapMachine

open HeapBits SharedHeap OracleComp WeierstrassCurve
open PrimeFieldCircuit (exponent)

abbrev State := Address × Bool

inductive Instruction (storage : Ty CryptoAtom) : Ty CryptoAtom → Ty CryptoAtom → Type
  | scalar (code : PaddedSampling.Code) : Instruction storage .unit scalar
  | uniform (n : Nat) (code : PaddedSampling.Code) : Instruction storage .unit (boundedNat n)
  | read : Instruction storage .unit storage
  | write : Instruction storage storage .unit

def compileEffect (w r k : Nat) {storage a b : Ty CryptoAtom} :
    Machine.Effect storage a b → Instruction storage a b
  | .scalar => .scalar (PaddedSampling.compile r w k)
  | .uniform n => .uniform n (PaddedSampling.compile (n+1) w k)
  | .read => .read
  | .write => .write

private def sample (code : PaddedSampling.Code) (store : Store) :
    StateT State (OracleComp BitRejection.bitSpec) (Run HeapExpression.Result) := fun state => do
  let out ← PaddedSampling.run code
  let node := alloc store (.word out.value.1)
  pure (⟨some node.value, out.steps+node.steps+3⟩, (state.1, state.2 || out.value.2))

def Instruction.run {storage : Ty CryptoAtom} :
    HeapProgram.HandlerM (Instruction storage) (StateT State (OracleComp BitRejection.bitSpec))
  | _, _, .scalar code, _, store => sample code store
  | _, _, .uniform _ code, _, store => sample code store
  | _, _, .read, _, store => fun state =>
    let root := copy state.1
    pure (⟨some (root.value, store), root.steps+1⟩, state)
  | _, _, .write, arg, store => fun state =>
    let root := copy arg
    let unit := alloc store (.word [])
    pure (⟨some unit.value, root.steps+unit.steps+2⟩, (root.value, state.2))

def handler (w r k : Nat) {storage : Ty CryptoAtom} :
    HeapProgram.HandlerM (Machine.Effect storage) (StateT State (OracleComp BitRejection.bitSpec)) :=
  fun cmd => Instruction.run (compileEffect w r k cmd)

def fee (w r k nodes : Nat) {storage a b : Ty CryptoAtom} : Machine.Effect storage a b → Nat
  | .scalar => PaddedSampling.budget r w k + HeapExpression.allocBudget (3*w+1) nodes + 3
  | .uniform n => PaddedSampling.budget (n+1) w k + HeapExpression.allocBudget (3*w+1) nodes + 3
  | .read => 2*nodes+2
  | .write => 2*nodes+HeapExpression.allocBudget (3*w+1) nodes+4

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)

/-- Decoding is confined to reference semantics, not the executable handler. -/
noncomputable def semantics (k : Nat) (sampling : Machine.SamplingCosts) (storage : Ty CryptoAtom) :
    HandlerM (cryptoBase (ZMod r) H₁ H₂ K M) (Machine.Effect storage)
      (StateT (storage.Value (cryptoBase (ZMod r) H₁ H₂ K M) × Bool)
        (OracleComp BitRejection.bitSpec)) := fun cmd arg state => match cmd with
  | .scalar => do
    let out ← PaddedSampling.run (PaddedSampling.compile r w k)
    pure (⟨(exponent out.value.1 : ZMod r), sampling.scalar⟩, (state.1, state.2 || out.value.2))
  | .uniform n => do
    let out ← PaddedSampling.run (PaddedSampling.compile (n+1) w k)
    pure (⟨Fin.ofNat (n+1) (exponent out.value.1), sampling.uniform n⟩, (state.1, state.2 || out.value.2))
  | .read => pure (⟨state.1, 1⟩, state)
  | .write => pure (⟨(), 1⟩, (arg, state.2))

def StateRel (storage : Ty CryptoAtom) (heap : List Node) (impl : State)
    (source : storage.Value (cryptoBase (ZMod r) H₁ H₂ K M) × Bool) : Prop :=
  Represents w (atomRep H₁ H₂ encodeK encodeM) heap storage impl.1 source.1 ∧ impl.2 = source.2

omit [Fact r.Prime] in
theorem stateRel_append {storage : Ty CryptoAtom} {heap : List Node} {impl : State}
    {source : storage.Value (cryptoBase (ZMod r) H₁ H₂ K M) × Bool}
    (h : StateRel H₁ H₂ encodeK encodeM storage heap impl source) (extra : List Node) :
    StateRel H₁ H₂ encodeK encodeM storage (heap ++ extra) impl source := ⟨h.1.append extra, h.2⟩

/-- All four effects have concrete costs and typed heap refinements, including
every sampler-failure path. This theorem does not identify fair-bit sampling
with the original ideal `Machine.effects`. -/
theorem handler_costed (k nodes : Nat) (sampling : Machine.SamplingCosts)
    {storage a b : Ty CryptoAtom} (cmd : Machine.Effect storage a b)
    (heap : List Node) (root : Address) (store : Store) (impl : State)
    (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (state : storage.Value (cryptoBase (ZMod r) H₁ H₂ K M) × Bool)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (hx : Represents w (atomRep H₁ H₂ encodeK encodeM) heap a root x)
    (hi : StateRel H₁ H₂ encodeK encodeM storage heap impl state) (hn : heap.length ≤ nodes) :
    QueryTreeRel (fun actual source =>
      HeapProgram.Post w (3*w+1) (atomRep H₁ H₂ encodeK encodeM)
        (StateRel H₁ H₂ encodeK encodeM storage) heap (source.1.steps+1) actual source ∧
      actual.1.steps ≤ fee w r k nodes cmd)
      ((handler w r k cmd root store).run impl)
      ((semantics H₁ H₂ (w := w) k sampling storage cmd x).run state) := by
  have hnode (bits : List Bool) (hb : bits.length = w) : NodeBound (3*w+1) heap.length (.word bits) := by
    change bits.length ≤ 3*w+1
    omega
  cases cmd with
  | read =>
    apply QueryTreeRel.pure
    constructor
    · refine ⟨[], impl.1, store, by simp [copy_value],
        ?_, ?_, ?_, ?_, by simp⟩
      · simpa using hs
      · simpa using hw
      · simpa using hi.1
      · simpa using hi
    · have hr := hi.1.address_lt
      simp only [copy_steps, fee]
      omega
  | write =>
    apply QueryTreeRel.pure
    constructor
    · refine ⟨[.word []], _, _, rfl, alloc_represents store heap hs _, ?_, ?_, ?_, by simp⟩
      · apply wellFormed_append heap _ hw
        change 0 ≤ 3*w+1
        omega
      · exact .unit (alloc_lookup store heap hs _)
      · exact ⟨by simpa only [copy_value] using hx.append [.word []], hi.2⟩
    · have hr := hx.address_lt
      have ha := HeapExpression.alloc_le_budget hw hn store hs (.word []) (by
        change 0 ≤ 3*w+1
        omega)
      simp only [copy_steps, fee]
      omega
  | scalar =>
    simp only [handler, compileEffect, Instruction.run]
    apply (QueryTreeRel.refl (PaddedSampling.run (PaddedSampling.compile r w k))).bind_support
    intro out hout reference _ heq
    subst reference
    have h := PaddedSampling.run_support r w k (Fact.out : r.Prime).pos out hout
    have hv : (exponent out.value.1 : ZMod r).val = exponent out.value.1 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt h.2.1]
    have ha := HeapExpression.alloc_le_budget hw hn store hs (.word out.value.1) (hnode _ h.2.2.1)
    apply QueryTreeRel.pure
    constructor
    · refine ⟨[.word out.value.1], _, _, rfl, alloc_represents store heap hs _, ?_, ?_, ?_, by simp⟩
      · apply wellFormed_append heap _ hw
        exact hnode _ h.2.2.1
      · apply Represents.atom (alloc_lookup store heap hs _)
        exact ⟨by change out.value.1 = natBits w (exponent out.value.1 : ZMod r).val; rw [hv]; exact h.1,
          trivial⟩
      · exact ⟨hi.1.append _, congrArg (· || out.value.2) hi.2⟩
    · change out.steps+(alloc store (.word out.value.1)).steps+3 ≤
        PaddedSampling.budget r w k+HeapExpression.allocBudget (3*w+1) nodes+3
      omega
  | uniform n =>
    simp only [handler, compileEffect, Instruction.run]
    apply (QueryTreeRel.refl (PaddedSampling.run (PaddedSampling.compile (n+1) w k))).bind_support
    intro out hout reference _ heq
    subst reference
    have h := PaddedSampling.run_support (n+1) w k (by omega) out hout
    have hv : (Fin.ofNat (n+1) (exponent out.value.1)).val = exponent out.value.1 :=
      Nat.mod_eq_of_lt h.2.1
    have hr : exponent out.value.1 < 2^w := by
      simpa only [h.2.2.1] using BitRejection.exponent_lt out.value.1
    have ha := HeapExpression.alloc_le_budget hw hn store hs (.word out.value.1) (hnode _ h.2.2.1)
    apply QueryTreeRel.pure
    constructor
    · refine ⟨[.word out.value.1], _, _, rfl, alloc_represents store heap hs _, ?_, ?_, ?_, by simp⟩
      · apply wellFormed_append heap _ hw
        exact hnode _ h.2.2.1
      · apply Represents.atom (alloc_lookup store heap hs _)
        constructor
        · change out.value.1 = natBits w (Fin.ofNat (n+1) (exponent out.value.1)).val
          rw [hv]
          exact h.1
        · change (Fin.ofNat (n+1) (exponent out.value.1)).val < 2^w
          rwa [hv]
      · exact ⟨hi.1.append _, congrArg (· || out.value.2) hi.2⟩
    · change out.steps+(alloc store (.word out.value.1)).steps+3 ≤
        PaddedSampling.budget (n+1) w k+HeapExpression.allocBudget (3*w+1) nodes+3
      omega

theorem semantics_bound (k : Nat) (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n)) (storage : Ty CryptoAtom)
    {a b : Ty CryptoAtom} (cmd : Machine.Effect storage a b) (bits : Nat)
    (arg : a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) (ha : NaturalRange.ValueBound bits arg)
    (state : storage.Value (cryptoBase (ZMod r) H₁ H₂ K M) × Bool)
    (hs : NaturalRange.ValueBound bits state.1)
    (out : Run (b.Value (cryptoBase (ZMod r) H₁ H₂ K M)) ×
      (storage.Value (cryptoBase (ZMod r) H₁ H₂ K M) × Bool))
    (hout : out ∈ support ((semantics H₁ H₂ (w := w) k sampling storage cmd arg).run state)) :
    NaturalRange.ValueBound (bits+out.1.steps) out.1.value ∧
      NaturalRange.ValueBound (bits+out.1.steps) out.2.1 := by
  cases cmd with
  | scalar =>
    simp only [semantics, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨_, _, rfl⟩ := hout
    exact ⟨trivial, NaturalRange.value_mono (by dsimp; omega) _ hs⟩
  | uniform n =>
    simp only [semantics, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨sample, _, rfl⟩ := hout
    refine ⟨?_, NaturalRange.value_mono (by dsimp; omega) _ hs⟩
    have hr := (Fin.ofNat (n+1) (exponent sample.value.1)).isLt
    exact (Nat.le_of_lt_succ hr).trans_lt ((hsampling n).trans_le
      (Nat.pow_le_pow_right (by decide) (by dsimp; omega)))
  | read =>
    simp only [semantics, StateT.run, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact ⟨NaturalRange.value_mono (by dsimp; omega) _ hs, NaturalRange.value_mono (by dsimp; omega) _ hs⟩
  | write =>
    simp only [semantics, StateT.run, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact ⟨trivial, NaturalRange.value_mono (by dsimp; omega) _ ha⟩

/-- Compile all effects once; no sampler compiler runs inside an online loop. -/
def compileBody (w r : Nat) (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂)) (k : Nat)
    {storage : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom}
    (code : Program CryptoOp (Machine.Effect storage) Γ a) : HeapProgram.Code (Instruction storage) :=
  (HeapProgram.compile w r W₁ W₂ code).mapQueries (compileEffect w r k)

variable [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]
  [SampleableType (ZMod r)]

omit [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂] in
/-- Every marked fair-bit path is an allowed ideal-machine path, with identical
source costs. This is support inclusion only, including on bad paths. -/
theorem semantics_support (k : Nat) (sampling : Machine.SamplingCosts) (storage : Ty CryptoAtom)
    {a b : Ty CryptoAtom} (cmd : Machine.Effect storage a b)
    (arg : a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) :
    StateSupportRefines Prod.fst (semantics H₁ H₂ (w := w) k sampling storage cmd arg)
      (Machine.effects (F := ZMod r) (G₁ := H₁) (G₂ := H₂) (K := K) (M := M) sampling storage cmd arg) := by
  intro state out hout
  cases cmd with
  | scalar =>
    simp only [semantics, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨sample, _, rfl⟩ := hout
    simp only [Machine.effects, StateT.run, support_map, Set.mem_image]
    exact ⟨(exponent sample.value.1 : ZMod r), mem_support_uniformSample (ZMod r), rfl⟩
  | uniform n =>
    simp only [semantics, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨sample, _, rfl⟩ := hout
    simp only [Machine.effects, StateT.run, support_map, Set.mem_image]
    exact ⟨Fin.ofNat (n+1) (exponent sample.value.1), mem_support_query _ _, rfl⟩
  | read =>
    simp only [semantics, StateT.run, support_pure, Set.mem_singleton_iff] at hout
    subst out
    simp [Machine.effects, StateT.run]
  | write =>
    simp only [semantics, StateT.run, support_pure, Set.mem_singleton_iff] at hout
    subst out
    simp [Machine.effects, StateT.run]

/-- The generic compiler's handler obligations are discharged for the closed
effect set. The budget comes from the original ideal-randomness machine and
is transported by support inclusion, not assumed for the new implementation. -/
theorem compileBody_costed
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) (k : Nat) (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n))
    {storage a : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (code : Program CryptoOp (Machine.Effect storage) Γ a)
    (heap : List Node) (roots : List Address) (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ)
    (store : Store) (impl : State) (state : storage.Value (cryptoBase (ZMod r) H₁ H₂ K M) × Bool)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : EnvRep w (atomRep H₁ H₂ encodeK encodeM) heap roots env)
    (hi : StateRel H₁ H₂ encodeK encodeM storage heap impl state)
    (bits B : Nat) (hebits : NaturalRange.EnvBound bits env)
    (hstate : NaturalRange.ValueBound bits state.1) (hwidth : bits+B ≤ w)
    (hb : ∀ out ∈ support ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost)
      (Machine.effects sampling storage) env).run state.1), out.1.steps ≤ B) :
    QueryTreeRel (fun actual source =>
      HeapProgram.CostPost w (3*w+1) (atomRep H₁ H₂ encodeK encodeM)
        (StateRel H₁ H₂ encodeK encodeM storage) heap
        (HeapProgram.budget w (heap.length+B) (fee w r k (heap.length+B)) code) actual source ∧
      actual.1.steps ≤ B*HeapProgram.budget w (heap.length+B) (fee w r k (heap.length+B)) code)
      (((compileBody w r W₁ W₂ k code).run Instruction.run (frameBits roots) store).run impl)
      ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost)
        (semantics H₁ H₂ (w := w) k sampling storage) env).run state) := by
  rw [compileBody, HeapProgram.Code.run_mapQueries]
  have hsupport := code.run_support_refines (arithmetic (ZMod r) H₁ H₂ K M cost) Prod.fst
    (semantics H₁ H₂ (w := w) k sampling storage) (Machine.effects sampling storage)
    (semantics_support H₁ H₂ (w := w) k sampling storage) env
  apply HeapProgram.compile_costed_of_budget H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost
    (fee w r k (heap.length+B)) (semantics H₁ H₂ (w := w) k sampling storage) (handler w r k)
    (StateRel H₁ H₂ encodeK encodeM storage)
    (fun _ extra _ _ h => stateRel_append H₁ H₂ encodeK encodeM h extra)
    (fun d s => NaturalRange.ValueBound d s.1)
    (fun h _ hs => NaturalRange.value_mono h _ hs)
    (semantics_bound H₁ H₂ (w := w) k sampling hsampling storage)
    code heap roots env store impl state hs hw he hi bits B hebits hstate hwidth
    (fun out hout => hb (out.1, out.2.1) (hsupport state out hout))
  intro a b cmd current root store impl x state hs hw hx hi _ hn
  apply (handler_costed H₁ H₂ encodeK encodeM k (heap.length+B) sampling cmd
    current root store impl x state hs hw hx hi hn).mono
  intro actual source h
  exact ⟨h.1, h.2.trans (Nat.le_add_left _ _)⟩

end Signatures.Runtime.HeapMachine
