import Proofs.Runtime.HeapProgramCorrectness

/-! Bit-step composition for the compiled program controller. Heap limits are
derived along matched source paths using allocation refinement, including each
adaptive loop iteration. Handler bit costs remain explicit obligations. -/

namespace Signatures.Runtime.HeapProgram

open HeapBits SharedHeap HeapExpression OracleComp
open PrimeFieldCircuit (exponent)

def budget {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type} (w nodes : Nat)
    (fee : {a b : Ty CryptoAtom} → Cmd a b → Nat)
    {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom} : Program CryptoOp Cmd Γ a → Nat
  | .ret e => max (HeapExpression.budget w nodes e) 1
  | .query cmd e => max (HeapExpression.budget w nodes e) (fee cmd + 1)
  | .bind first body => max (max (budget w nodes fee first) (budget w nodes fee body))
      (frameBudget Γ.length nodes + 2)
  | .branch cond yes no => max (max (HeapExpression.budget w nodes cond)
      (max (budget w nodes fee yes) (budget w nodes fee no))) (readBudget (3*w+1) nodes + 4)
  | .loop count init body => max (max (HeapExpression.budget w nodes count)
      (max (HeapExpression.budget w nodes init) (budget w nodes fee body)))
      (readBudget (3*w+1) nodes + 2*w + 2*nodes + frameBudget Γ.length nodes + 10)
  | .call body args => max (max (HeapArguments.budget w nodes args) (budget w nodes fee body)) 2

variable {base : CryptoAtom → Type} {S T I : Type} {spec : OracleSpec I}
  {w cap : Nat} {leaf : (a : CryptoAtom) → List Bool → base a → Prop}

def CostPost (w cap : Nat) (leaf : (a : CryptoAtom) → List Bool → base a → Prop)
    (StateRel : List Node → T → S → Prop) (heap : List Node) (factor : Nat)
    {a : Ty CryptoAtom} (actual : Run HeapExpression.Result × T) (source : Run (a.Value base) × S) : Prop :=
  Post w cap leaf StateRel heap source.1.steps actual source ∧ actual.1.steps ≤ source.1.steps*factor

/-- A body's cost may vary with oracle replies. Its append bound, together with
the residual source budget, justifies the heap limit for the next iteration. -/
theorem loop_costed [∀ q, Nonempty (spec.Range q)] {a : Ty CryptoAtom}
    (StateRel : List Node → T → S → Prop)
    (step : Address → Store → StateT T (OracleComp spec) (Run HeapExpression.Result))
    (source : a.Value base → StateT S (OracleComp spec) (Run (a.Value base)))
    (check : a.Value base → S → Prop) (nodes factor overhead : Nat)
    (hstep : ∀ heap root store impl x state, store.Represents heap → WellFormed cap heap →
      Represents w leaf heap a root x → StateRel heap impl state → check x state →
      (∀ out ∈ support ((source x).run state), heap.length+out.1.steps ≤ nodes) →
      QueryTreeRel (fun actual source => Post w cap leaf StateRel heap source.1.steps actual source ∧
        actual.1.steps ≤ source.1.steps*factor + overhead)
        ((step root store).run impl) ((source x).run state))
    (heap : List Node) (root : Address) (store : Store) (impl : T) (x : a.Value base) (state : S)
    (hs : store.Represents heap) (hw : WellFormed cap heap) (hx : Represents w leaf heap a root x)
    (hi : StateRel heap impl state) (bits : List Bool)
    (ht : NaturalRange.RepeatTrace check source (exponent bits) x state)
    (hfactor : 2*bits.length+2*nodes+overhead+3 ≤ factor)
    (hb : ∀ out ∈ support ((repeatRun source (exponent bits) x).run state), heap.length+out.1.steps ≤ nodes) :
    QueryTreeRel (CostPost w cap leaf StateRel heap factor)
      ((HeapLoop.run step bits root store).run impl) ((repeatRun source (exponent bits) x).run state) := by
  generalize hn : exponent bits = n at ht hb ⊢
  induction n generalizing bits heap root store impl x state with
  | zero =>
    rw [HeapLoop.run]
    dsimp only
    split
    · simp only [repeatRun, StateT.run_pure]
      apply QueryTreeRel.pure
      constructor
      · refine ⟨[], root, store, by simp only [copy_value], ?_, ?_, ?_, ?_, by simp⟩
        · simpa using hs
        · simpa using hw
        · simpa using hx
        · simpa using hi
      · have hsize := hb (⟨x, 1⟩, state) (by simp [repeatRun])
        have ha := hx.address_lt
        simp only [HeapLoop.tick_steps, copy_steps, Nat.one_mul]
        dsimp only at hsize
        omega
    · rename_i rest htick
      have h := (HeapLoop.tick_some htick).2
      omega
  | succ n ih =>
    have htotal r (hr : r ∈ support ((source x).run state)) out
        (hout : out ∈ support ((repeatRun source n r.1.value).run r.2)) :
        heap.length+(r.1.steps+out.1.steps+2) ≤ nodes := by
      apply hb (⟨out.1.value, r.1.steps+out.1.steps+2⟩, out.2)
      simp only [repeatRun, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff]
      exact ⟨r, hr, out, hout, rfl⟩
    have hbodyBudget r (hr : r ∈ support ((source x).run state)) : heap.length+r.1.steps ≤ nodes := by
      obtain ⟨last, hlast⟩ := support_nonempty ((repeatRun source n r.1.value).run r.2)
      have h := htotal r hr last hlast
      omega
    rw [HeapLoop.run]
    dsimp only
    split
    · rename_i htick
      have h := HeapLoop.tick_none htick
      omega
    · rename_i rest htick
      have hrest := HeapLoop.tick_some htick
      have hn' : exponent rest = n := by omega
      simp only [repeatRun, StateT.run_bind, StateT.run_pure]
      apply (hstep heap root store impl x state hs hw hx hi ht.1 hbodyBudget).bind_support
      intro actual _ reference hreference hrel
      rcases actual with ⟨body, nextImpl⟩
      rcases reference with ⟨ref, nextState⟩
      obtain ⟨hpost, hcost⟩ := hrel
      obtain ⟨extra, acc, next, hv, hs₁, hw₁, hx₁, hi₁, hlen⟩ := hpost
      dsimp only at hv hs₁ hw₁ hx₁ hi₁ hlen hcost
      simp only [hv, StateT.run_bind, StateT.run_pure]
      have htail := ih (heap ++ extra) acc next nextImpl ref.value nextState
        hs₁ hw₁ hx₁ hi₁ rest (by rw [hrest.1]; exact hfactor) hn'
        (ht.2 (ref, nextState) hreference) (by
          intro out hout
          have h := htotal (ref, nextState) hreference out hout
          simp only [List.length_append]; dsimp only at h; omega)
      apply htail.bind
      intro actual reference hrel
      rcases actual with ⟨out, finalImpl⟩
      rcases reference with ⟨refOut, finalState⟩
      obtain ⟨hpost, htailCost⟩ := hrel
      apply QueryTreeRel.pure
      constructor
      · exact hpost.rebase.mono (by dsimp; omega)
      · simp only [HeapLoop.tick_steps]
        dsimp only at htailCost
        nlinarith

open WeierstrassCurve

variable {r p₁ p₂ : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]
  {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}

/-- The executable controller's full bit-step bound, paired with its semantic
and allocation refinement. The node limit follows from the source budget on
every reply path; handler costs must be proved for their actual implementations. -/
theorem compile_costed [∀ q, Nonempty (spec.Range q)]
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) (nodes factor : Nat) (fee : {a b : Ty CryptoAtom} → Cmd a b → Nat)
    (H : Signatures.Runtime.HandlerM (cryptoBase (ZMod r) H₁ H₂ K M) Cmd (StateT S (OracleComp spec)))
    (handler : HandlerM Cmd (StateT T (OracleComp spec))) (StateRel : List Node → T → S → Prop)
    (happend : ∀ heap extra impl state, StateRel heap impl state → StateRel (heap ++ extra) impl state)
    (hhandler : ∀ {a b} (cmd : Cmd a b) heap root store impl x state,
      store.Represents heap → WellFormed (3*w+1) heap →
      Represents w (atomRep H₁ H₂ encodeK encodeM) heap a root x → StateRel heap impl state →
      (∀ out ∈ support ((H cmd x).run state), NaturalRange.ValueBound w out.1.value) → heap.length ≤ nodes →
      QueryTreeRel (fun actual source => Post w (3*w+1) (atomRep H₁ H₂ encodeK encodeM)
        StateRel heap (source.1.steps+1) actual source ∧ actual.1.steps ≤ source.1.steps*factor + fee cmd)
        ((handler cmd root store).run impl) ((H cmd x).run state))
    {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom} (code : Program CryptoOp Cmd Γ a)
    (heap : List Node) (roots : List Address)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (store : Store) (impl : T) (state : S)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : EnvRep w (atomRep H₁ H₂ encodeK encodeM) heap roots env) (hi : StateRel heap impl state)
    (ht : NaturalRange.ProgramTrace cost w H code env state)
    (hb : ∀ out ∈ support ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost) H env).run state),
      heap.length+out.1.steps ≤ nodes) (hf : budget w nodes fee code ≤ factor) :
    QueryTreeRel (CostPost w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) StateRel heap factor)
      (((compile w r W₁ W₂ code).run handler (frameBits roots) store).run impl)
      ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost) H env).run state) := by
  let P := arithmetic (ZMod r) H₁ H₂ K M cost
  let L := atomRep (r := r) H₁ H₂ encodeK encodeM
  have expr {Δ t} (e : Expr CryptoOp Δ t) heap roots env store hs hw he ht :
      HeapExpression.ResultSpec w (3*w+1) L heap (e.run P env).steps (e.run P env).value
        ((HeapExpression.compile w r W₁ W₂ e).run (frameBits roots) store) :=
    HeapExpression.compile_spec H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
      cost e heap roots env store hs hw he ht
  have exprCost {Δ t} (e : Expr CryptoOp Δ t) heap roots env store hs hw he ht
      (hb : heap.length+(e.run P env).steps ≤ nodes) (hf : HeapExpression.budget w nodes e ≤ factor) :
      ((HeapExpression.compile w r W₁ W₂ e).run (frameBits roots) store).steps ≤ (e.run P env).steps*factor :=
    HeapExpression.compile_steps H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
      cost e heap roots env store hs hw he ht nodes factor hb hf
  change QueryTreeRel (CostPost w (3*w+1) L StateRel heap factor) _ ((code.run P H env).run state)
  change ∀ out ∈ support ((code.run P H env).run state), heap.length+out.1.steps ≤ nodes at hb
  induction code generalizing heap roots store impl state with
  | ret e =>
    simp only [budget, max_le_iff] at hf
    have hc := hb (⟨(e.run P env).value, (e.run P env).steps+1⟩, state) (by simp [Program.run])
    dsimp only at hc
    have hcost := exprCost e heap roots env store hs hw he ht (by omega) hf.1
    obtain ⟨extra, root, next, hv, hs', hw', hx, hlen⟩ := expr e heap roots env store hs hw he ht
    simp only [compile, Code.run, Program.run, StateT.run_pure]
    apply QueryTreeRel.pure
    constructor
    · exact ⟨extra, root, next, hv, hs', hw', hx, happend heap extra impl state hi, by dsimp; omega⟩
    · have hf' := hf.2
      dsimp only; simp only [Nat.add_mul, Nat.one_mul]; omega
  | query cmd arg =>
    simp only [budget, max_le_iff] at hf
    have htotal out (hout : out ∈ support ((H cmd (arg.run P env).value).run state)) :
        heap.length+((arg.run P env).steps+out.1.steps+1) ≤ nodes := by
      apply hb (⟨out.1.value, (arg.run P env).steps+out.1.steps+1⟩, out.2)
      simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff]
      exact ⟨out, hout, rfl⟩
    obtain ⟨out, hout⟩ := support_nonempty ((H cmd (arg.run P env).value).run state)
    have hsize := htotal out hout
    have hcost := exprCost arg heap roots env store hs hw he ht.1 (by omega) hf.1
    obtain ⟨extra, root, next, hv, hs', hw', hx, hlen⟩ := expr arg heap roots env store hs hw he ht.1
    simp only [compile, Code.run, bindM, hv, Program.run, StateT.run_bind, StateT.run_pure, pure_bind]
    apply (hhandler cmd (heap ++ extra) root next impl _ state hs' hw' hx
      (happend heap extra impl state hi) ht.2 (by simp only [List.length_append]; omega)).bind
    intro actual source hrel
    obtain ⟨hpost, hhandlerCost⟩ := hrel
    apply QueryTreeRel.pure
    constructor
    · exact hpost.rebase.mono (by dsimp; omega)
    · have hf' := hf.2
      dsimp only; simp only [Nat.add_mul, Nat.one_mul]; omega
  | bind first body ihfirst ihbody =>
    simp only [budget, max_le_iff] at hf
    have htotal r (hr : r ∈ support ((first.run P H env).run state)) out
        (hout : out ∈ support ((body.run P H (r.1.value, env)).run r.2)) :
        heap.length+(r.1.steps+out.1.steps+1) ≤ nodes := by
      apply hb (⟨out.1.value, r.1.steps+out.1.steps+1⟩, out.2)
      simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff]
      exact ⟨r, hr, out, hout, rfl⟩
    have hfirstBudget r (hr : r ∈ support ((first.run P H env).run state)) : heap.length+r.1.steps ≤ nodes := by
      obtain ⟨out, hout⟩ := support_nonempty ((body.run P H (r.1.value, env)).run r.2)
      have h := htotal r hr out hout
      omega
    simp only [compile, Code.run, bindM, Program.run, StateT.run_bind, StateT.run_pure]
    apply (ihfirst heap roots env store impl state hs hw he hi ht.1 (hf := hf.1.1) (hb := hfirstBudget)).bind_support
    intro actual _ source hsource hrel
    rcases actual with ⟨firstOut, nextImpl⟩
    rcases source with ⟨ref, nextState⟩
    obtain ⟨hpost, hfirstCost⟩ := hrel
    obtain ⟨extra, root, next, hv, hs', hw', hx, hi', hlen⟩ := hpost
    dsimp only at hv hs' hw' hx hi' hlen hfirstCost
    have hbodyBudget out (hout : out ∈ support ((body.run P H (ref.value, env)).run nextState)) :
        (heap ++ extra).length+out.1.steps ≤ nodes := by
      have h := htotal (ref, nextState) hsource out hout
      simp only [List.length_append]; dsimp only at h; omega
    obtain ⟨out, hout⟩ := support_nonempty ((body.run P H (ref.value, env)).run nextState)
    have hsize : (heap ++ extra).length ≤ nodes := by have h := hbodyBudget out hout; omega
    have hpush := framePush_le_budget roots root
      (fun addr h => ((he.append extra).addresses addr h).trans_le hsize)
      (hx.address_lt.trans_le hsize) (le_of_eq he.length)
    simp only [hv, framePush_value, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    apply (ihbody (heap ++ extra) (root :: roots) (ref.value, env) next nextImpl nextState
      hs' hw' (.cons hx (he.append extra)) hi' (ht.2 (ref, nextState) hsource)
      (hf := hf.1.2) (hb := hbodyBudget)).bind
    intro actual source hrel
    obtain ⟨hpost, hbodyCost⟩ := hrel
    apply QueryTreeRel.pure
    constructor
    · exact hpost.rebase.mono (by dsimp; omega)
    · have hf' := hf.2
      dsimp only; simp only [Nat.add_mul, Nat.one_mul]; omega
  | branch cond yes no ihyes ihno =>
    simp only [budget, max_le_iff] at hf
    let chosen := if (cond.run P env).value then yes.run P H env else no.run P H env
    have htotal out (hout : out ∈ support (chosen.run state)) :
        heap.length+((cond.run P env).steps+out.1.steps+1) ≤ nodes := by
      apply hb (⟨out.1.value, (cond.run P env).steps+out.1.steps+1⟩, out.2)
      cases hc : (cond.run P env).value <;>
        simp only [Program.run, hc, Bool.false_eq_true, ite_false, ite_true,
          StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] <;>
        exact ⟨out, by simpa only [chosen, hc, Bool.false_eq_true, ite_false, ite_true] using hout, rfl⟩
    obtain ⟨out, hout⟩ := support_nonempty (chosen.run state)
    have hsize := htotal out hout
    have hcost := exprCost cond heap roots env store hs hw he ht.1 (by omega) hf.1.1
    obtain ⟨extra, root, next, hv, hs', hw', hx, hlen⟩ := expr cond heap roots env store hs hw he ht.1
    have hn : (heap ++ extra).length ≤ nodes := by simp only [List.length_append]; omega
    have hread := read_le_budget hw' hn next hs' root
    have hselector : (readBool next.memory root).steps ≤ readBudget (3*w+1) nodes+2 :=
      Nat.add_le_add_right hread 2
    rw [hs'.2] at hselector
    cases hx with
    | bool hlookup =>
      simp only [compile, Code.run, bindM, hv, Program.run, StateT.run_bind, StateT.run_pure,
        pure_bind, hs'.2, readBool_value _ _ _ hlookup]
      cases hc : (cond.run P env).value with
      | false =>
        simp only [Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
        have htrace : NaturalRange.ProgramTrace cost w H no env state := by
          simpa only [P, hc, Bool.false_eq_true, ite_false] using ht.2
        apply (ihno (heap ++ extra) roots env next impl state hs' hw' (he.append extra)
          (happend heap extra impl state hi) htrace (hf := hf.1.2.2) (hb := ?_)).bind
        · intro actual source hrel
          obtain ⟨hpost, hbodyCost⟩ := hrel
          apply QueryTreeRel.pure
          constructor
          · exact hpost.rebase.mono (by dsimp; omega)
          · have hf' := hf.2
            dsimp only; simp only [Nat.add_mul, Nat.one_mul]; omega
        · intro out hout
          have h := htotal out (by simpa only [chosen, hc, Bool.false_eq_true, ite_false] using hout)
          simp only [List.length_append]; omega
      | true =>
        simp only [ite_true, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
        have htrace : NaturalRange.ProgramTrace cost w H yes env state := by
          simpa only [P, hc, ite_true] using ht.2
        apply (ihyes (heap ++ extra) roots env next impl state hs' hw' (he.append extra)
          (happend heap extra impl state hi) htrace (hf := hf.1.2.1) (hb := ?_)).bind
        · intro actual source hrel
          obtain ⟨hpost, hbodyCost⟩ := hrel
          apply QueryTreeRel.pure
          constructor
          · exact hpost.rebase.mono (by dsimp; omega)
          · have hf' := hf.2
            dsimp only; simp only [Nat.add_mul, Nat.one_mul]; omega
        · intro out hout
          have h := htotal out (by simpa only [chosen, hc, ite_true] using hout)
          simp only [List.length_append]; omega
  | call body args ih =>
    simp only [budget, max_le_iff] at hf
    have htotal out (hout : out ∈ support ((body.run P H (args.run P env).value).run state)) :
        heap.length+((args.run P env).steps+out.1.steps+2) ≤ nodes := by
      apply hb (⟨out.1.value, (args.run P env).steps+out.1.steps+2⟩, out.2)
      simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff]
      exact ⟨out, hout, rfl⟩
    obtain ⟨out, hout⟩ := support_nonempty ((body.run P H (args.run P env).value).run state)
    have hn := htotal out hout
    obtain ⟨hargs, hargCost⟩ := HeapArguments.compile_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
      cost args heap roots env store hs hw he ht.1 nodes factor
      (by change heap.length+(args.run P env).steps ≤ nodes; omega) hf.1.1
    obtain ⟨extra, output, next, hv, hs', hw', he', hlen⟩ := hargs
    change extra.length ≤ (args.run P env).steps at hlen
    change _ ≤ (args.run P env).steps*factor at hargCost
    simp only [compile, Code.run, bindM, hv, Program.run, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind]
    apply (ih (heap ++ extra) output (args.run P env).value next impl state hs' hw' he'
      (happend heap extra impl state hi) ht.2 (hf := hf.1.2) (hb := ?_)).bind
    · intro actual source hrel
      obtain ⟨hpost, hbodyCost⟩ := hrel
      apply QueryTreeRel.pure
      constructor
      · exact hpost.rebase.mono (by dsimp; omega)
      · have hf' := hf.2
        dsimp only; simp only [Nat.add_mul]; omega
    · intro out hout
      have h := htotal out hout
      simp only [List.length_append]; omega
  | loop count init body ih =>
    simp only [budget, max_le_iff] at hf
    let source := fun x => body.run P H (x, env)
    have htotal out (hout : out ∈ support
        ((repeatRun source (count.run P env).value (init.run P env).value).run state)) :
        heap.length+((count.run P env).steps+(init.run P env).steps+out.1.steps+1) ≤ nodes := by
      apply hb (⟨out.1.value, (count.run P env).steps+(init.run P env).steps+out.1.steps+1⟩, out.2)
      simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff]
      exact ⟨out, hout, rfl⟩
    obtain ⟨out, hout⟩ := support_nonempty
      ((repeatRun source (count.run P env).value (init.run P env).value).run state)
    have hn := htotal out hout
    have hcountCost := exprCost count heap roots env store hs hw he ht.1 (by omega) hf.1.1
    obtain ⟨extra, countRoot, s₁, hc, hs₁, hw₁, hcount, hlen⟩ := expr count heap roots env store hs hw he ht.1
    have hinitCost := exprCost init (heap ++ extra) roots env s₁ hs₁ hw₁ (he.append extra) ht.2.1
      (by simp only [List.length_append]; omega) hf.1.2.1
    obtain ⟨more, acc, s₂, hv, hs₂, hw₂, hacc, hmore⟩ :=
      expr init (heap ++ extra) roots env s₁ hs₁ hw₁ (he.append extra) ht.2.1
    have hcount' := hcount.append more
    have hframe := (he.append extra).append more
    have histate := happend (heap ++ extra) more impl state (happend heap extra impl state hi)
    have hsize : ((heap ++ extra) ++ more).length ≤ nodes := by simp only [List.length_append]; omega
    have hread := read_le_budget hw₂ hsize s₂ hs₂ countRoot
    have hwordCost : (readWord s₂.memory countRoot).steps ≤ readBudget (3*w+1) nodes+1 :=
      Nat.add_le_add_right hread 1
    let step : Address → Store → StateT T (OracleComp spec) (Run HeapExpression.Result) := fun root store => do
      let frame := framePush root (frameBits roots)
      let out ← (compile w r W₁ W₂ body).run handler frame.value store
      pure ⟨out.value, frame.steps+out.steps+1⟩
    have hloop := loop_costed (fun heap impl state => StateRel heap impl state ∧ EnvRep w L heap roots env)
      step source (fun x state => NaturalRange.ProgramTrace cost w H body (x, env) state)
      nodes factor (frameBudget roots.length nodes+1)
      (by
        intro heap root store impl x state hs hw hx hi htrace hb
        have hbody := ih heap (root :: roots) (x, env) store impl state hs hw (.cons hx hi.2) hi.1 htrace
          (hf := hf.1.2.2) (hb := hb)
        obtain ⟨out, hout⟩ := support_nonempty ((source x).run state)
        have hsize : heap.length ≤ nodes := by have h := hb out hout; omega
        have hpush := framePush_le_budget roots root
          (fun addr h => (hi.2.addresses addr h).trans_le hsize)
          (hx.address_lt.trans_le hsize) (le_refl _)
        dsimp only [step]
        simp only [framePush_value, StateT.run_bind, StateT.run_pure]
        have mapped := hbody.map
          (S := fun actual source => Post w (3*w+1) L
            (fun heap impl state => StateRel heap impl state ∧ EnvRep w L heap roots env)
            heap source.1.steps actual source ∧ actual.1.steps ≤ source.1.steps*factor + (frameBudget roots.length nodes+1))
          (fun p => ((⟨p.1.value, (framePush root (frameBits roots)).steps+p.1.steps+1⟩ :
            Run HeapExpression.Result), p.2)) id (by
            intro actual source hrel
            constructor
            · exact hrel.1.state_mono
                (Other := fun heap impl state => StateRel heap impl state ∧ EnvRep w L heap roots env)
                (fun added hstate => ⟨hstate, hi.2.append added⟩)
            · dsimp only [id]; have hcost := hrel.2; omega)
        simpa only [map_eq_bind_pure_comp, Function.comp_def, id_eq, bind_pure, source] using mapped)
      ((heap ++ extra) ++ more) acc s₂ impl (init.run P env).value state hs₂ hw₂ hacc
      ⟨histate, hframe⟩ (natBits w (count.run P env).value)
      (by
        have hfit := represents_range H₁ H₂ encodeK encodeM hcount
        rw [HeapLoop.exponent_natBits _ _ hfit]
        exact ht.2.2)
      (by simp only [natBits, List.length_ofFn, he.length]; omega)
      (by
        intro last hlast
        have hfit := represents_range H₁ H₂ encodeK encodeM hcount
        rw [HeapLoop.exponent_natBits _ _ hfit] at hlast
        have h := htotal last hlast
        simp only [List.length_append]; omega)
    cases hcount' with
    | nat hlookup hfit =>
      have hword : (readWord s₂.memory countRoot).value = some (natBits w (count.run P env).value) := by
        simp only [readWord, hs₂.2, read_value, hlookup]
      rw [HeapLoop.exponent_natBits _ _ hfit] at hloop
      simp only [compile, Code.run, bindM, hc, hv, hword, Program.run,
        StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
      apply hloop.bind
      intro actual reference hrel
      obtain ⟨hpost, hloopCost⟩ := hrel
      apply QueryTreeRel.pure
      constructor
      · have h := (hpost.state_mono (fun _ hstate => hstate.1)).rebase.rebase
        exact h.mono (by dsimp; omega)
      · have hf' := hf.2
        dsimp only; simp only [Nat.add_mul, Nat.one_mul]; omega

/-- A total source budget supplies both the intermediate width checks and the
heap limit. The result bounds every compiled path, retaining its matched source
execution. This does not include loading the initial heap or compiling code. -/
theorem compile_costed_of_budget [∀ q, Nonempty (spec.Range q)]
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) (fee : {a b : Ty CryptoAtom} → Cmd a b → Nat)
    (H : Signatures.Runtime.HandlerM (cryptoBase (ZMod r) H₁ H₂ K M) Cmd (StateT S (OracleComp spec)))
    (handler : HandlerM Cmd (StateT T (OracleComp spec))) (StateRel : List Node → T → S → Prop)
    (happend : ∀ heap extra impl state, StateRel heap impl state → StateRel (heap ++ extra) impl state)
    (StateBound : Nat → S → Prop)
    (hmono : ∀ {d e}, d ≤ e → ∀ state, StateBound d state → StateBound e state)
    (hgrowth : ∀ {a b} (cmd : Cmd a b) (bits : Nat)
      (arg : a.Value (cryptoBase (ZMod r) H₁ H₂ K M)),
      NaturalRange.ValueBound bits arg → ∀ state, StateBound bits state →
      ∀ out ∈ support ((H cmd arg).run state),
        NaturalRange.ValueBound (bits+out.1.steps) out.1.value ∧ StateBound (bits+out.1.steps) out.2)
    {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom} (code : Program CryptoOp Cmd Γ a)
    (heap : List Node) (roots : List Address)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (store : Store) (impl : T) (state : S)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : EnvRep w (atomRep H₁ H₂ encodeK encodeM) heap roots env) (hi : StateRel heap impl state)
    (bits B : Nat) (hebits : NaturalRange.EnvBound bits env) (hstate : StateBound bits state)
    (hwidth : bits+B ≤ w)
    (hb : ∀ out ∈ support ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost) H env).run state),
      out.1.steps ≤ B)
    (hhandler : ∀ {a b} (cmd : Cmd a b) current root store impl x state,
      store.Represents current → WellFormed (3*w+1) current →
      Represents w (atomRep H₁ H₂ encodeK encodeM) current a root x → StateRel current impl state →
      (∀ out ∈ support ((H cmd x).run state), NaturalRange.ValueBound w out.1.value) →
      current.length ≤ heap.length+B →
      QueryTreeRel (fun actual source => Post w (3*w+1) (atomRep H₁ H₂ encodeK encodeM)
        StateRel current (source.1.steps+1) actual source ∧
        actual.1.steps ≤ source.1.steps*budget w (heap.length+B) fee code + fee cmd)
        ((handler cmd root store).run impl) ((H cmd x).run state)) :
    QueryTreeRel (fun actual source =>
      CostPost w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) StateRel heap
        (budget w (heap.length+B) fee code) actual source ∧
      actual.1.steps ≤ B*budget w (heap.length+B) fee code)
      (((compile w r W₁ W₂ code).run handler (frameBits roots) store).run impl)
      ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost) H env).run state) := by
  have ht := NaturalRange.program_trace_bound cost H StateBound hmono hgrowth code bits w
    env hebits state hstate (fun out hout => (Nat.add_le_add_left (hb out hout) bits).trans hwidth)
  have h := compile_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost
    (heap.length+B) (budget w (heap.length+B) fee code) fee H handler StateRel happend hhandler
    code heap roots env store impl state hs hw he hi ht
    (fun out hout => Nat.add_le_add_left (hb out hout) heap.length) (le_refl _)
  exact h.with_support.mono (fun _ source h =>
    ⟨h.2.2, h.2.2.2.trans (Nat.mul_le_mul_right _ (hb source h.2.1))⟩)

end Signatures.Runtime.HeapProgram
