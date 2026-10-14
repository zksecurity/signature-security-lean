import Signatures.Runtime.HeapProgramRefinement

/-! Whole-program structural refinement to the executable bit-tape controller.
This theorem preserves query trees and bounds allocations. Aggregate bit-step
costs and concrete closed-machine handlers are separate obligations. -/

namespace Signatures.Runtime.HeapProgram

open HeapBits SharedHeap WeierstrassCurve OracleComp

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M S T I : Type} {spec : OracleSpec I}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]
  {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}

theorem compile_refines
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts)
    (H : Signatures.Runtime.HandlerM (cryptoBase (ZMod r) H₁ H₂ K M) Cmd (StateT S (OracleComp spec)))
    (handler : HandlerM Cmd (StateT T (OracleComp spec))) (StateRel : List Node → T → S → Prop)
    (happend : ∀ heap extra impl state, StateRel heap impl state → StateRel (heap ++ extra) impl state)
    (hhandler : ∀ {a b} (cmd : Cmd a b) heap root store impl x state,
      store.Represents heap → WellFormed (3*w+1) heap →
      Represents w (atomRep H₁ H₂ encodeK encodeM) heap a root x → StateRel heap impl state →
      (∀ out ∈ support ((H cmd x).run state), NaturalRange.ValueBound w out.1.value) →
      QueryTreeRel (fun actual source => Post w (3*w+1) (atomRep H₁ H₂ encodeK encodeM)
        StateRel heap (source.1.steps+1) actual source)
        ((handler cmd root store).run impl) ((H cmd x).run state))
    {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom} (code : Program CryptoOp Cmd Γ a)
    (heap : List Node) (roots : List Address)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (store : Store) (impl : T) (state : S)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : EnvRep w (atomRep H₁ H₂ encodeK encodeM) heap roots env) (hi : StateRel heap impl state)
    (ht : NaturalRange.ProgramTrace cost w H code env state) :
    QueryTreeRel (fun actual source => Post w (3*w+1) (atomRep H₁ H₂ encodeK encodeM)
      StateRel heap source.1.steps actual source)
      (((compile w r W₁ W₂ code).run handler (frameBits roots) store).run impl)
      ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost) H env).run state) := by
  let P := arithmetic (ZMod r) H₁ H₂ K M cost
  let L := atomRep (r := r) H₁ H₂ encodeK encodeM
  have expr {Δ t} (e : Expr CryptoOp Δ t) heap roots env store hs hw he ht :
      HeapExpression.ResultSpec w (3*w+1) L heap (e.run P env).steps (e.run P env).value
        ((HeapExpression.compile w r W₁ W₂ e).run (frameBits roots) store) :=
    HeapExpression.compile_spec H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
      cost e heap roots env store hs hw he ht
  change QueryTreeRel (fun actual source => Post w (3*w+1) L StateRel heap source.1.steps actual source)
    _ ((code.run P H env).run state)
  induction code generalizing heap roots store impl state with
  | ret e =>
    obtain ⟨extra, root, next, hv, hs', hw', hx, hlen⟩ := expr e heap roots env store hs hw he ht
    simp only [compile, Code.run, Program.run, StateT.run_pure]
    apply QueryTreeRel.pure
    exact ⟨extra, root, next, hv, hs', hw', hx, happend heap extra impl state hi, by dsimp; omega⟩
  | query cmd arg =>
    obtain ⟨extra, root, next, hv, hs', hw', hx, hlen⟩ := expr arg heap roots env store hs hw he ht.1
    simp only [compile, Code.run, bindM, hv, Program.run, StateT.run_bind, StateT.run_pure, pure_bind]
    apply (hhandler cmd (heap ++ extra) root next impl _ state hs' hw' hx
      (happend heap extra impl state hi) ht.2).bind
    intro actual source hpost
    apply QueryTreeRel.pure
    exact hpost.rebase.mono (by dsimp; omega)
  | bind first body ihfirst ihbody =>
    simp only [compile, Code.run, bindM, Program.run, StateT.run_bind, StateT.run_pure]
    apply (ihfirst heap roots env store impl state hs hw he hi ht.1).bind_support
    intro actual _ source hsource hpost
    rcases actual with ⟨firstOut, nextImpl⟩
    rcases source with ⟨ref, nextState⟩
    obtain ⟨extra, root, next, hv, hs', hw', hx, hi', hlen⟩ := hpost
    dsimp only at hv hs' hw' hx hi' hlen
    simp only [hv, framePush_value, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    apply (ihbody (heap ++ extra) (root :: roots) (ref.value, env) next nextImpl nextState
      hs' hw' (.cons hx (he.append extra)) hi' (ht.2 (ref, nextState) hsource)).bind
    intro actual source hpost
    apply QueryTreeRel.pure
    exact hpost.rebase.mono (by dsimp; omega)
  | branch cond yes no ihyes ihno =>
    obtain ⟨extra, root, next, hv, hs', hw', hx, hlen⟩ := expr cond heap roots env store hs hw he ht.1
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
          (happend heap extra impl state hi) htrace).bind
        intro actual source hpost
        apply QueryTreeRel.pure
        exact hpost.rebase.mono (by dsimp; omega)
      | true =>
        simp only [ite_true, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
        have htrace : NaturalRange.ProgramTrace cost w H yes env state := by
          simpa only [P, hc, ite_true] using ht.2
        apply (ihyes (heap ++ extra) roots env next impl state hs' hw' (he.append extra)
          (happend heap extra impl state hi) htrace).bind
        intro actual source hpost
        apply QueryTreeRel.pure
        exact hpost.rebase.mono (by dsimp; omega)
  | call body args ih =>
    have hargs := (HeapArguments.compile_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
      cost args heap roots env store hs hw he ht.1 _ _ le_rfl le_rfl).1
    obtain ⟨extra, output, next, hv, hs', hw', he', hlen⟩ := hargs
    change extra.length ≤ (args.run P env).steps at hlen
    simp only [compile, Code.run, bindM, hv, Program.run, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind]
    apply (ih (heap ++ extra) output (args.run P env).value next impl state hs' hw' he'
      (happend heap extra impl state hi) ht.2).bind
    intro actual source hpost
    apply QueryTreeRel.pure
    exact hpost.rebase.mono (by dsimp; omega)
  | loop count init body ih =>
    obtain ⟨extra, countRoot, s₁, hc, hs₁, hw₁, hcount, hlen⟩ := expr count heap roots env store hs hw he ht.1
    obtain ⟨more, acc, s₂, hv, hs₂, hw₂, hacc, hmore⟩ :=
      expr init (heap ++ extra) roots env s₁ hs₁ hw₁ (he.append extra) ht.2.1
    have hcount' := hcount.append more
    have hframe := (he.append extra).append more
    have histate := happend (heap ++ extra) more impl state (happend heap extra impl state hi)
    let source := fun x => body.run P H (x, env)
    let step : Address → Store → StateT T (OracleComp spec) (Run HeapExpression.Result) := fun root store => do
      let frame := framePush root (frameBits roots)
      let out ← (compile w r W₁ W₂ body).run handler frame.value store
      pure ⟨out.value, frame.steps+out.steps+1⟩
    have hloop := loop_refines (fun heap impl state => StateRel heap impl state ∧ EnvRep w L heap roots env)
      step source (fun x state => NaturalRange.ProgramTrace cost w H body (x, env) state)
      (by
        intro heap root store impl x state hs hw hx hi htrace
        have hbody := ih heap (root :: roots) (x, env) store impl state hs hw (.cons hx hi.2) hi.1 htrace
        dsimp only [step]
        simp only [framePush_value, StateT.run_bind, StateT.run_pure]
        have mapped := hbody.map
          (S := fun actual source => Post w (3*w+1) L
            (fun heap impl state => StateRel heap impl state ∧ EnvRep w L heap roots env)
            heap source.1.steps actual source)
          (fun p => ((⟨p.1.value, (framePush root (frameBits roots)).steps+p.1.steps+1⟩ :
            Run HeapExpression.Result), p.2)) id
          (fun _ _ hpost => hpost.state_mono
            (Other := fun heap impl state => StateRel heap impl state ∧ EnvRep w L heap roots env)
            (fun added hstate => ⟨hstate, hi.2.append added⟩))
        simpa only [map_eq_bind_pure_comp, Function.comp_def, id_eq, bind_pure, source] using mapped)
      ((heap ++ extra) ++ more) acc s₂ impl (init.run P env).value state hs₂ hw₂ hacc
      ⟨histate, hframe⟩ (natBits w (count.run P env).value)
      (by
        have hfit := represents_range H₁ H₂ encodeK encodeM hcount
        rw [HeapLoop.exponent_natBits _ _ hfit]
        exact ht.2.2)
    cases hcount' with
    | nat hlookup hfit =>
      have hword : (readWord s₂.memory countRoot).value = some (natBits w (count.run P env).value) := by
        simp only [readWord, hs₂.2, read_value, hlookup]
      rw [HeapLoop.exponent_natBits _ _ hfit] at hloop
      simp only [compile, Code.run, bindM, hc, hv, hword, Program.run,
        StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
      apply hloop.bind
      intro actual source hpost
      apply QueryTreeRel.pure
      have h := (hpost.state_mono (fun _ hstate => hstate.1)).rebase.rebase
      exact h.mono (by dsimp; omega)

/-- Derive all expression and reply width checks from the source's total budget
and the concrete handler's range-growth proof. No per-expression certificate is
required from the caller. Initial input/state encodings remain explicit. -/
theorem compile_refines_of_budget [∀ q, Nonempty (spec.Range q)]
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts)
    (H : Signatures.Runtime.HandlerM (cryptoBase (ZMod r) H₁ H₂ K M) Cmd (StateT S (OracleComp spec)))
    (handler : HandlerM Cmd (StateT T (OracleComp spec))) (StateRel : List Node → T → S → Prop)
    (happend : ∀ heap extra impl state, StateRel heap impl state → StateRel (heap ++ extra) impl state)
    (hhandler : ∀ {a b} (cmd : Cmd a b) heap root store impl x state,
      store.Represents heap → WellFormed (3*w+1) heap →
      Represents w (atomRep H₁ H₂ encodeK encodeM) heap a root x → StateRel heap impl state →
      (∀ out ∈ support ((H cmd x).run state), NaturalRange.ValueBound w out.1.value) →
      QueryTreeRel (fun actual source => Post w (3*w+1) (atomRep H₁ H₂ encodeK encodeM)
        StateRel heap (source.1.steps+1) actual source)
        ((handler cmd root store).run impl) ((H cmd x).run state))
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
    (bits : Nat) (hebits : NaturalRange.EnvBound bits env) (hstate : StateBound bits state)
    (hb : ∀ out ∈ support ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost) H env).run state),
      bits+out.1.steps ≤ w) :
    QueryTreeRel (fun actual source => Post w (3*w+1) (atomRep H₁ H₂ encodeK encodeM)
      StateRel heap source.1.steps actual source)
      (((compile w r W₁ W₂ code).run handler (frameBits roots) store).run impl)
      ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost) H env).run state) :=
  compile_refines H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost H handler StateRel happend hhandler
    code heap roots env store impl state hs hw he hi
    (NaturalRange.program_trace_bound cost H StateBound hmono hgrowth code bits w env hebits state hstate hb)

end Signatures.Runtime.HeapProgram
