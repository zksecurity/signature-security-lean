import Signatures.Runtime.HeapExpressionRefinement

/-! Source-expression refinement to the shared bit-tape controller. The range
premise concerns all executed intermediates, as proved from local budgets in
NaturalRange. This theorem also bounds the number of newly allocated nodes. -/

namespace Signatures.Runtime.HeapExpression

open HeapBits SharedHeap FixedPorts WeierstrassCurve

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]

theorem compile_spec
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom}
    (e : Expr CryptoOp Γ a) (heap : List Node) (roots : List Address)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (store : Store)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : EnvRep w (atomRep H₁ H₂ encodeK encodeM) heap roots env)
    (ht : NaturalRange.ExprBound cost w e env) :
    ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) heap
      (e.run (arithmetic (ZMod r) H₁ H₂ K M cost) env).steps
      (e.run (arithmetic (ZMod r) H₁ H₂ K M cost) env).value
      ((compile w r W₁ W₂ e).run (frameBits roots) store) := by
  let P := arithmetic (ZMod r) H₁ H₂ K M cost
  let L := atomRep (r := r) H₁ H₂ encodeK encodeM
  change ResultSpec w (3*w+1) L heap (e.run P env).steps (e.run P env).value _
  induction e generalizing heap roots store with
  | var v =>
    obtain ⟨root, hv, hx⟩ := frameGet_represents he v
    apply (root_spec store hs hw hx _ ?_).mono (Nat.zero_le _)
    simp only [compile, Code.run, map, hv, Option.map_some]
  | unit =>
    exact alloc_spec (w := w) (leaf := L) (t := .unit) store hs hw (.word []) (by simp [NodeBound]) ()
      (.unit (alloc_lookup store heap hs _))
  | bool b =>
    exact alloc_spec (w := w) (leaf := L) (t := .bool) store hs hw (.word [b]) (by simp [NodeBound]) b
      (.bool (alloc_lookup store heap hs _))
  | nat n =>
    have h := alloc_spec (w := w) (leaf := L) (t := .nat) store hs hw (.word (natBits w n))
      (by simp [NodeBound, natBits]; omega) n (.nat (alloc_lookup store heap hs _) ht)
    exact h.mono (by simp [Expr.run])
  | nil =>
    exact alloc_spec (w := w) (leaf := L) (t := .list _) store hs hw .nil trivial []
      (.nil (alloc_lookup store heap hs _))
  | pair l right ihl ihr =>
    have hx := ihl heap roots env store hs hw he ht.1
    have h : ResultSpec w (3*w+1) L heap (t := .pair _ _)
        ((l.run P env).steps + ((right.run P env).steps + 1))
        ((l.run P env).value, (right.run P env).value)
        ((compile w r W₁ W₂ (.pair l right)).run (frameBits roots) store) := by
      apply bind_spec hx
      intro extra left s₁ _ hs₁ hw₁ hl _
      apply bind_spec (ihr (heap ++ extra) roots env s₁ hs₁ hw₁ (he.append extra) ht.2)
      intro more right s₂ _ hs₂ hw₂ hr _
      have hl' := hl.append more
      exact alloc_spec s₂ hs₂ hw₂ (.pair left right) ⟨hl'.address_lt, hr.address_lt⟩ _
        (alloc_pair s₂ hs₂ hl' hr)
    simpa only [Expr.run, Nat.add_assoc] using h
  | cons head tail ihh iht =>
    have hx := ihh heap roots env store hs hw he ht.1
    have h : ResultSpec w (3*w+1) L heap (t := .list _)
        ((head.run P env).steps + ((tail.run P env).steps + 1))
        ((head.run P env).value :: (tail.run P env).value)
        ((compile w r W₁ W₂ (.cons head tail)).run (frameBits roots) store) := by
      apply bind_spec hx
      intro extra head s₁ _ hs₁ hw₁ hh _
      apply bind_spec (iht (heap ++ extra) roots env s₁ hs₁ hw₁ (he.append extra) ht.2)
      intro more tail s₂ _ hs₂ hw₂ ht _
      have hh' := hh.append more
      exact alloc_spec s₂ hs₂ hw₂ (.cons head tail) ⟨hh'.address_lt, ht.address_lt⟩ _
        (alloc_cons s₂ hs₂ hh' ht)
    simpa only [Expr.run, Nat.add_assoc] using h
  | fst arg ih =>
    have h : ResultSpec w (3*w+1) L heap ((arg.run P env).steps + 0)
        (arg.run P env).value.1 ((compile w r W₁ W₂ (.fst arg)).run (frameBits roots) store) := by
      apply bind_spec (ih heap roots env store hs hw he ht)
      intro extra root next _ hn hwell hv _
      obtain ⟨left, right, h, hl, _⟩ := hv.pair_parts
      apply root_spec next hn hwell hl
      simp only [map, hn.2, project_value false _ _ _ _ h, Bool.false_eq_true, ite_false, Option.map_some]
    exact h.mono (by simp [Expr.run])
  | snd arg ih =>
    have h : ResultSpec w (3*w+1) L heap ((arg.run P env).steps + 0)
        (arg.run P env).value.2 ((compile w r W₁ W₂ (.snd arg)).run (frameBits roots) store) := by
      apply bind_spec (ih heap roots env store hs hw he ht)
      intro extra root next _ hn hwell hv _
      obtain ⟨left, right, h, _, hr⟩ := hv.pair_parts
      apply root_spec next hn hwell hr
      simp only [map, hn.2, project_value true _ _ _ _ h, ite_true, Option.map_some]
    exact h.mono (by simp [Expr.run])
  | letE arg body iharg ihbody =>
    have h : ResultSpec w (3*w+1) L heap
        ((arg.run P env).steps + (body.run P ((arg.run P env).value, env)).steps)
        (body.run P ((arg.run P env).value, env)).value
        ((compile w r W₁ W₂ (.letE arg body)).run (frameBits roots) store) := by
      apply bind_spec (iharg heap roots env store hs hw he ht.1)
      intro extra root next _ hn hwell hv _
      have hb := ihbody (heap ++ extra) (root :: roots) ((arg.run P env).value, env) next
        hn hwell (.cons hv (he.append extra)) ht.2
      apply hb.of_value_eq
      simp only [framePush_value]
    exact h.mono (by simp [Expr.run])
  | branch cond yes no ihcond ihyes ihno =>
    have hc := ihcond heap roots env store hs hw he ht.1
    cases hbool : (cond.run P env).value with
    | false =>
      have h : ResultSpec w (3*w+1) L heap ((cond.run P env).steps + (no.run P env).steps)
          (no.run P env).value ((compile w r W₁ W₂ (.branch cond yes no)).run (frameBits roots) store) := by
        apply bind_spec hc
        intro extra root next _ hn hwell hv _
        cases hv with
        | bool h =>
          have hb := ihno (heap ++ extra) roots env next hn hwell (he.append extra)
            (by simpa only [P, hbool, Bool.false_eq_true, ite_false] using ht.2)
          apply hb.of_value_eq
          simp only [bind, hn.2, readBool_value _ _ _ h, hbool, Bool.false_eq_true, ite_false]
      simpa only [Expr.run, hbool, Bool.false_eq_true, ite_false] using h.mono (Nat.le_succ _)
    | true =>
      have h : ResultSpec w (3*w+1) L heap ((cond.run P env).steps + (yes.run P env).steps)
          (yes.run P env).value ((compile w r W₁ W₂ (.branch cond yes no)).run (frameBits roots) store) := by
        apply bind_spec hc
        intro extra root next _ hn hwell hv _
        cases hv with
        | bool h =>
          have hb := ihyes (heap ++ extra) roots env next hn hwell (he.append extra)
            (by simpa only [P, hbool, ite_true] using ht.2)
          apply hb.of_value_eq
          simp only [bind, hn.2, readBool_value _ _ _ h, hbool, ite_true]
      simpa only [Expr.run, hbool, ite_true] using h.mono (Nat.le_succ _)
  | op op arg ih =>
    have ha := ih heap roots env store hs hw he ht.1
    have safe : CryptoCircuit.Safe (w := w) H₁ H₂ op (arg.run P env).value := by
      cases op with
      | natAdd => exact ht.2
      | _ => trivial
    have h : ResultSpec w (3*w+1) L heap ((arg.run P env).steps + 1)
        (P.execute op (arg.run P env).value)
        ((compile w r W₁ W₂ (.op op arg)).run (frameBits roots) store) := by
      apply bind_spec ha
      intro extra root next _ hn hwell hv _
      let y := P.execute op (arg.run P env).value
      let node := Node.word (CryptoCircuit.portBits H₁ H₂ encodeK encodeM y)
      have hv' := represents_range H₁ H₂ encodeK encodeM hv
      have hresult := primitive_result_represents H₁ H₂ encodeK encodeM cost op next hn _ hv' safe
      have hlen := portBits_length H₁ H₂ encodeK encodeM (outputLayout op) y
      have hnode : NodeBound (3*w+1) (heap ++ extra).length node := by
        change (CryptoCircuit.portBits H₁ H₂ encodeK encodeM y).length ≤ 3*w+1
        rw [hlen, outputLayout_width]
        exact primitive_word_bound w op
      have hout := alloc_spec next hn hwell node hnode y hresult
      apply hout.of_value_eq
      exact runPrimitive_value H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost op next hn root _ hv safe
    exact h.mono (by simp [Expr.run])
  | fold input init body ihinput ihinit ihbody =>
    let source := fun x acc => body.run P (x, acc, env)
    have h : ResultSpec w (3*w+1) L heap
        ((input.run P env).steps + ((init.run P env).steps +
          (foldRun source (input.run P env).value (init.run P env).value).steps))
        (foldRun source (input.run P env).value (init.run P env).value).value
        ((compile w r W₁ W₂ (.fold input init body)).run (frameBits roots) store) := by
      apply bind_spec (ihinput heap roots env store hs hw he ht.1)
      intro extra listRoot s₁ _ hs₁ hw₁ hlist _
      apply bind_spec (ihinit (heap ++ extra) roots env s₁ hs₁ hw₁ (he.append extra) ht.2.1)
      intro more acc s₂ _ hs₂ hw₂ hacc _
      have hlist' := hlist.append more
      have hframe := (he.append extra).append more
      have hfuel : (input.run P env).value.length < s₂.count.length := by
        rw [hs₂.1]
        exact (hlist'.list_length hw₂).trans_lt hlist'.address_lt
      have hfold := foldLoop_spec (fun heap => EnvRep w L heap roots env)
        (fun _ added h => h.append added) source
        (fun x acc => NaturalRange.ExprBound cost w body (x, acc, env))
        (fun head acc store =>
          let accFrame := framePush acc (frameBits roots)
          let headFrame := framePush head accFrame.value
          let out := (compile w r W₁ W₂ body).run headFrame.value store
          ⟨out.value, accFrame.steps + headFrame.steps + out.steps + 2⟩)
        (by
          intro heap head acc store x y hi hs hw hx hy hc
          have hb := ihbody heap (head :: acc :: roots) (x, y, env) store hs hw (.cons hx (.cons hy hi)) hc
          apply hb.of_value_eq
          simp only [framePush_value])
        ((heap ++ extra) ++ more) listRoot acc s₂ s₂.count
        (input.run P env).value (init.run P env).value hframe hs₂ hw₂ hlist' hacc hfuel ht.2.2
      apply hfold.of_value_eq
      simp only [copy_value]
    exact h.mono (by simp only [Expr.run]; dsimp only [source]; omega)

/-- Derive all intermediate range conditions from the original expression
budget, rather than requiring a separate overflow premise at each primitive. -/
theorem compile_spec_of_budget
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
    ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) heap
      (e.run (arithmetic (ZMod r) H₁ H₂ K M cost) env).steps
      (e.run (arithmetic (ZMod r) H₁ H₂ K M cost) env).value
      ((compile w r W₁ W₂ e).run (frameBits roots) store) :=
  compile_spec H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost e heap roots env store hs hw he
    (NaturalRange.expr_trace_bound cost e bits w env hebits hb)

end Signatures.Runtime.HeapExpression
