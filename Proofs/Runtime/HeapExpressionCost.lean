import Proofs.Runtime.HeapExpressionCorrectness
import Proofs.Runtime.HeapControllerCost

/-! End-to-end expression cost: the same compiled bit-tape interpreter whose
value is refined in `compile_spec` has a source-budget-scaled execution bound.
This does not yet compile programs, oracle handlers, or the replay controller. -/

namespace Signatures.Runtime.HeapExpression

open HeapBits SharedHeap FixedPorts WeierstrassCurve

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]

theorem compile_steps
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom}
    (e : Expr CryptoOp Γ a) (heap : List Node) (roots : List Address)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (store : Store)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : EnvRep w (atomRep H₁ H₂ encodeK encodeM) heap roots env)
    (ht : NaturalRange.ExprBound cost w e env) (nodes factor : Nat)
    (hn : heap.length + (e.run (arithmetic (ZMod r) H₁ H₂ K M cost) env).steps ≤ nodes)
    (hb : budget w nodes e ≤ factor) :
    ((compile w r W₁ W₂ e).run (frameBits roots) store).steps ≤
      (e.run (arithmetic (ZMod r) H₁ H₂ K M cost) env).steps*factor := by
  let P := arithmetic (ZMod r) H₁ H₂ K M cost
  let L := atomRep (r := r) H₁ H₂ encodeK encodeM
  have spec {Δ t} (e : Expr CryptoOp Δ t) (heap : List Node) (roots : List Address)
      (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Δ) (store : Store)
      (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
      (he : EnvRep w L heap roots env) (ht : NaturalRange.ExprBound cost w e env) :
      ResultSpec w (3*w+1) L heap (e.run P env).steps (e.run P env).value
        ((compile w r W₁ W₂ e).run (frameBits roots) store) :=
    compile_spec H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost e heap roots env store hs hw he ht
  change _ ≤ (e.run P env).steps*factor
  change heap.length + (e.run P env).steps ≤ nodes at hn
  induction e generalizing heap roots store with
  | var v =>
    have h := frameGet_steps roots (List.replicate v.depth ()) nodes
      (fun root h => (he.addresses root h).trans_le (by omega))
    simp only [compile, Code.run, map, Expr.run, List.length_replicate] at *
    simp only [budget] at hb
    nlinarith
  | unit =>
    have h := alloc_le_budget hw (show heap.length ≤ nodes by omega) store hs (.word [])
      (by simp [NodeBound])
    simpa only [compile, Code.run, lift, Expr.run, Nat.one_mul] using
      (Nat.add_le_add_right h 1).trans hb
  | bool b =>
    have h := alloc_le_budget hw (show heap.length ≤ nodes by omega) store hs (.word [b])
      (by simp [NodeBound])
    simpa only [compile, Code.run, lift, Expr.run, Nat.one_mul] using
      (Nat.add_le_add_right h 1).trans hb
  | nat n =>
    have h := alloc_le_budget hw (show heap.length ≤ nodes by omega) store hs (.word (natBits w n))
      (by simp [NodeBound, natBits]; omega)
    simp only [compile, Code.run, lift, Expr.run]
    simp only [budget] at hb
    nlinarith
  | nil =>
    have h := alloc_le_budget hw (show heap.length ≤ nodes by omega) store hs .nil trivial
    simpa only [compile, Code.run, lift, Expr.run, Nat.one_mul] using
      (Nat.add_le_add_right h 1).trans hb
  | pair left right ihl ihr =>
    simp only [budget, max_le_iff] at hb
    simp only [Expr.run] at hn ⊢
    have h : ((compile w r W₁ W₂ (.pair left right)).run (frameBits roots) store).steps ≤
        (left.run P env).steps*factor + ((right.run P env).steps*factor +
          allocBudget (3*w+1) nodes + 2) + 1 := by
      apply bind_steps_spec (spec left heap roots env store hs hw he ht.1)
        (ihl heap roots env store hs hw he ht.1 hb.1.1 (by omega))
      intro extra l s₁ _ hs₁ hw₁ hl hlen
      have he₁ := he.append extra
      have hn₁ : (heap ++ extra).length + (right.run P env).steps ≤ nodes := by
        simp only [List.length_append]; omega
      apply (bind_steps_spec (nextCost := allocBudget (3*w+1) nodes + 1)
        (spec right _ roots env s₁ hs₁ hw₁ he₁ ht.2)
        (ihr _ roots env s₁ hs₁ hw₁ he₁ ht.2 hb.1.2 hn₁) ?_).trans (by omega)
      intro more rr s₂ _ hs₂ hw₂ hrr hmore
      have hl' := hl.append more
      have ha := alloc_le_budget hw₂ (show ((heap ++ extra) ++ more).length ≤ nodes by
        simp only [List.length_append]; omega) s₂ hs₂ (.pair l rr) ⟨hl'.address_lt, hrr.address_lt⟩
      exact Nat.add_le_add_right ha 1
    change _ ≤ ((left.run P env).steps + (right.run P env).steps + 1)*factor
    nlinarith [hb.2]
  | cons head tail ihh iht =>
    simp only [budget, max_le_iff] at hb
    simp only [Expr.run] at hn ⊢
    have h : ((compile w r W₁ W₂ (.cons head tail)).run (frameBits roots) store).steps ≤
        (head.run P env).steps*factor + ((tail.run P env).steps*factor +
          allocBudget (3*w+1) nodes + 2) + 1 := by
      apply bind_steps_spec (spec head heap roots env store hs hw he ht.1)
        (ihh heap roots env store hs hw he ht.1 hb.1.1 (by omega))
      intro extra x s₁ _ hs₁ hw₁ hx hlen
      have he₁ := he.append extra
      have hn₁ : (heap ++ extra).length + (tail.run P env).steps ≤ nodes := by
        simp only [List.length_append]; omega
      apply (bind_steps_spec (nextCost := allocBudget (3*w+1) nodes + 1)
        (spec tail _ roots env s₁ hs₁ hw₁ he₁ ht.2)
        (iht _ roots env s₁ hs₁ hw₁ he₁ ht.2 hb.1.2 hn₁) ?_).trans (by omega)
      intro more xs s₂ _ hs₂ hw₂ hxs hmore
      have hx' := hx.append more
      have ha := alloc_le_budget hw₂ (show ((heap ++ extra) ++ more).length ≤ nodes by
        simp only [List.length_append]; omega) s₂ hs₂ (.cons x xs) ⟨hx'.address_lt, hxs.address_lt⟩
      exact Nat.add_le_add_right ha 1
    change _ ≤ ((head.run P env).steps + (tail.run P env).steps + 1)*factor
    nlinarith [hb.2]
  | fst arg ih | snd arg ih =>
    simp only [budget, max_le_iff] at hb
    simp only [Expr.run] at hn ⊢
    apply (bind_steps_spec (nextCost := readBudget (3*w+1) nodes + 3)
      (spec arg heap roots env store hs hw he ht)
      (ih heap roots env store hs hw he ht hb.1 (by omega)) ?_).trans (by nlinarith [hb.2])
    intro extra root next _ hn' hwell hv hlen
    have hread := read_le_budget (nodes := nodes) hwell (by simp only [List.length_append]; omega)
      next hn' root
    simpa only [map, project, Nat.add_assoc] using Nat.add_le_add_right hread 3
  | letE arg body iharg ihbody =>
    simp only [budget, max_le_iff] at hb
    simp only [Expr.run] at hn ⊢
    apply (bind_steps_spec (nextCost := (body.run P ((arg.run P env).value, env)).steps*factor +
      frameBudget roots.length nodes + 1) (spec arg heap roots env store hs hw he ht.1)
      (iharg heap roots env store hs hw he ht.1 hb.1.1 (by omega)) ?_).trans
        (by rw [he.length]; nlinarith [hb.2])
    intro extra root next _ hn' hwell hv hlen
    have he' := he.append extra
    have hsize : (heap ++ extra).length ≤ nodes := by simp only [List.length_append]; omega
    have hpush := framePush_le_budget roots root
      (fun addr h => (he'.addresses addr h).trans_le hsize) (hv.address_lt.trans_le hsize)
      (le_refl _)
    have hbody := ihbody _ (root :: roots) ((arg.run P env).value, env) next hn' hwell
      (.cons hv he') ht.2 hb.1.2 (by simp only [List.length_append]; omega)
    simp only [framePush_value]
    nlinarith
  | branch cond yes no ihcond ihyes ihno =>
    simp only [budget, max_le_iff] at hb
    simp only [Expr.run] at hn ⊢
    apply (bind_steps_spec (nextCost := (if (cond.run P env).value then yes.run P env else no.run P env).steps*factor +
      readBudget (3*w+1) nodes + 3) (spec cond heap roots env store hs hw he ht.1)
      (ihcond heap roots env store hs hw he ht.1 hb.1.1 (by omega)) ?_).trans (by nlinarith [hb.2])
    intro extra root next _ hn' hwell hv hlen
    have hsize : (heap ++ extra).length ≤ nodes := by simp only [List.length_append]; omega
    have hread := read_le_budget hwell hsize next hn' root
    cases hv with
    | bool h =>
      simp only [bind, hn'.2, readBool_value _ _ _ h]
      rw [hn'.2] at hread
      cases hc : (cond.run P env).value with
      | false =>
        have ht' : NaturalRange.ExprBound cost w no env := by
          simpa only [P, hc, Bool.false_eq_true, ite_false] using ht.2
        have hbody := ihno _ roots env next hn' hwell (he.append extra) ht' hb.1.2.2
          (by simp only [hc, Bool.false_eq_true, ite_false] at hn
              simp only [List.length_append]; omega)
        simp only [hc, Bool.false_eq_true, ite_false, readBool] at *
        omega
      | true =>
        have ht' : NaturalRange.ExprBound cost w yes env := by
          simpa only [P, hc, ite_true] using ht.2
        have hbody := ihyes _ roots env next hn' hwell (he.append extra) ht' hb.1.2.1
          (by simp only [hc, ite_true] at hn
              simp only [List.length_append]; omega)
        simp only [hc, ite_true, readBool] at *
        omega
  | op op arg ih =>
    simp only [budget, max_le_iff] at hb
    simp only [Expr.run] at hn ⊢
    apply (bind_steps_spec (nextCost := primitiveBudget w nodes op)
      (spec arg heap roots env store hs hw he ht.1)
      (ih heap roots env store hs hw he ht.1 hb.1 (by omega)) ?_).trans (by nlinarith [hb.2])
    intro extra root next _ hn' hwell hv hlen
    exact primitive_le_budget H₁ H₂ encodeK encodeM hr h₁ h₂ hwell
      (by simp only [List.length_append]; omega) op next hn' root _ hv
  | fold input init body ihinput ihinit ihbody =>
    simp only [budget, max_le_iff] at hb
    let source := fun x acc => body.run P (x, acc, env)
    let total := (foldRun source (input.run P env).value (init.run P env).value).steps
    change heap.length + ((input.run P env).steps + (init.run P env).steps + total + 1) ≤ nodes at hn
    have h : ((compile w r W₁ W₂ (.fold input init body)).run (frameBits roots) store).steps ≤
        (input.run P env).steps*factor + ((init.run P env).steps*factor +
          (total*factor + 2*nodes + 2) + 1) + 1 := by
      apply bind_steps_spec (spec input heap roots env store hs hw he ht.1)
        (ihinput heap roots env store hs hw he ht.1 hb.1.1 (by omega))
      intro extra listRoot s₁ _ hs₁ hw₁ hlist hlen
      apply bind_steps_spec (spec init _ roots env s₁ hs₁ hw₁ (he.append extra) ht.2.1)
        (ihinit _ roots env s₁ hs₁ hw₁ (he.append extra) ht.2.1 hb.1.2.1
          (by simp only [List.length_append]; omega))
      intro more acc s₂ _ hs₂ hw₂ hacc hmore
      have hlist' := hlist.append more
      have hframe := (he.append extra).append more
      have hfuel : (input.run P env).value.length < s₂.count.length := by
        rw [hs₂.1]
        exact (hlist'.list_length hw₂).trans_lt hlist'.address_lt
      have hsize : ((heap ++ extra) ++ more).length + total ≤ nodes := by
        simp only [List.length_append]; omega
      have hfold := foldLoop_steps (fun heap => EnvRep w L heap roots env)
        (fun _ added h => h.append added) source
        (fun x acc => NaturalRange.ExprBound cost w body (x, acc, env))
        (fun head acc store =>
          let accFrame := framePush acc (frameBits roots)
          let headFrame := framePush head accFrame.value
          let out := (compile w r W₁ W₂ body).run headFrame.value store
          ⟨out.value, accFrame.steps + headFrame.steps + out.steps + 2⟩)
        nodes factor (2*frameBudget (roots.length+1) nodes + 2)
        (by rw [he.length]; omega)
        (by
          intro heap head acc store x y hi hs hw hx hy hc hn
          have he' := EnvRep.cons hx (EnvRep.cons hy hi)
          have hspec := spec body heap (head :: acc :: roots) (x, y, env) store hs hw he' hc
          have hbody := ihbody heap (head :: acc :: roots) (x, y, env) store hs hw he' hc hb.1.2.2 hn
          have hsize : heap.length ≤ nodes := by omega
          have hr := fun addr h => (hi.addresses addr h).trans_le hsize
          have hp₁ := framePush_le_budget roots acc hr (hy.address_lt.trans_le hsize)
            (Nat.le_succ roots.length)
          have hp₂ := framePush_le_budget (acc :: roots) head
            (by intro addr h; rcases List.mem_cons.mp h with rfl | h
                · exact hy.address_lt.trans_le hsize
                · exact hr addr h)
            (hx.address_lt.trans_le hsize) (le_refl _)
          constructor
          · exact hspec.of_value_eq (by simp only [framePush_value])
          · simp only [framePush_value, List.length_cons, Nat.succ_eq_add_one] at hp₁ hp₂ ⊢
            dsimp only [source]
            omega)
        ((heap ++ extra) ++ more) listRoot acc s₂ s₂.count
        (input.run P env).value (init.run P env).value hframe hs₂ hw₂ hlist' hacc hfuel ht.2.2 hsize
      simp only [copy_value, copy_steps]
      change _ ≤ total*factor at hfold
      dsimp only at hfold
      rw [hs₂.1]
      omega
    change _ ≤ ((input.run P env).steps + (init.run P env).steps + total + 1)*factor
    nlinarith [hb.2]

/-- Semantic refinement, allocation growth, and actual bit-controller cost from
one source budget. The initial heap/codec premises describe already encoded
inputs; their construction cost is not included in this expression theorem. -/
theorem compile_costed_of_budget
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom}
    (e : Expr CryptoOp Γ a) (heap : List Node) (roots : List Address)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (store : Store)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : EnvRep w (atomRep H₁ H₂ encodeK encodeM) heap roots env)
    (bits : Nat) (hebits : NaturalRange.EnvBound bits env)
    (hb : bits + (e.run (arithmetic (ZMod r) H₁ H₂ K M cost) env).steps ≤ w) :
    let source := e.run (arithmetic (ZMod r) H₁ H₂ K M cost) env
    let actual := (compile w r W₁ W₂ e).run (frameBits roots) store
    ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) heap source.steps source.value actual ∧
      actual.steps ≤ source.steps * budget w (heap.length + source.steps) e := by
  constructor
  · exact compile_spec_of_budget H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
      cost e heap roots env store hs hw he bits hebits hb
  · exact compile_steps H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
      cost e heap roots env store hs hw he
      (NaturalRange.expr_trace_bound cost e bits w env hebits hb) _ _ le_rfl le_rfl

end Signatures.Runtime.HeapExpression
