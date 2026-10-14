import Signatures.Runtime.BackendLanguageBudget
import Signatures.Runtime.BackendIterationGrowth

/-! Complete resource composition for a compiled input-bounded loop. The
invariant is indexed by remaining iterations. Count computation, initialization,
retained local contexts, loop tests, and final projection are all charged. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.Language

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {I S : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)
  {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) → Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  (store : C.Str S)
  (effect : {a b : Ty Atom} → Cmd a b →
    Code Q spec iface (StepClass.HasProd.prod (rep.ty a) store)
      (StepClass.HasProd.prod (rep.ty b) store))

include sizes laws mono routing

theorem loop_bound_remaining {Γ : List (Ty Atom)} {a : Ty Atom}
    (count : Expr Op Γ .nat) (init : Expr Op Γ a) (body : Program Op Cmd (a :: Γ) a)
    (env : Env base Γ) (saved : S) (inv : Nat → a.Value base × S → Prop)
    (width cap countTime initTime bodyTime tickTime : Nat)
    (hh : header ≤ width) (henv : Q.size (rep.env Γ) env ≤ width)
    (hn : ∀ n ≤ cap, Q.size rep.data.nat n ≤ width)
    (hcap : count.denote P env ≤ cap)
    (hi : inv (count.denote P env) (init.denote P env, saved))
    (hsize : ∀ remaining ≤ cap, ∀ p, inv remaining p →
      Q.size (rep.ty a) p.1 ≤ width ∧ Q.size store p.2 ≤ width)
    (hcount : Q.cost (Expression.compile rep data P primitive count) env ≤ countTime)
    (hinit : Q.cost (Expression.compile rep data P primitive init) env ≤ initTime)
    (hbody : ∀ remaining < cap, ∀ acc state, inv (remaining + 1) (acc, state) →
      ∀ out ∈ support ((compile rep data P primitive store effect body).run control queryCost ((acc, env), state)),
        inv remaining out.value ∧ out.steps ≤ bodyTime)
    (htick : ∀ n ≤ cap, ∀ encoded ≤ 7 * width, control.loop n encoded ≤ tickTime)
    (out : Run (a.Value base × S))
    (hout : out ∈ support ((compile rep data P primitive store effect (.loop count init body)).run
      control queryCost (env, saved))) :
    inv 0 out.value ∧ out.steps ≤ countTime + initTime +
      cap * (bodyTime + 19 * overhead (128 * width) + tickTime) + tickTime +
        32 * overhead (128 * width) := by
  let fee := overhead (128 * width)
  let frame := rep.env (a :: Γ)
  let step := withContext store (QP.snd (rep.ty a) (rep.env Γ))
    (compile rep data P primitive store effect body)
  let loopInv := fun remaining (p : Env base (a :: Γ) × S) =>
    p.1.2 = env ∧ inv remaining (p.1.1, p.2)
  have h3 : width ≤ 3 * width := by omega
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ fee := fun _ h => mono h
  have hframe (acc : a.Value base) (ha : Q.size (rep.ty a) acc ≤ width) :
      Q.size frame (acc, env) ≤ 3 * width := by
    have hp := sizes.prod_le (rep.ty a) (rep.env Γ) (acc, env)
    dsimp only at hp
    exact hp.trans (by omega)
  have hstep : ∀ remaining < cap, Bounds control queryCost step
      (loopInv (remaining + 1)) (loopInv remaining) (bodyTime + 19 * fee) := by
    intro remaining hr input hinput z hz
    obtain ⟨⟨acc, kept⟩, state⟩ := input
    obtain ⟨hkept, hinv⟩ := hinput
    dsimp only at hkept hinv
    subst kept
    obtain ⟨ha, hs⟩ := hsize (remaining + 1) (by omega) (acc, state) hinv
    have hf := hframe acc ha
    have hcontext := withContext_bound_of_width sizes laws mono control queryCost routing store
      (QP.snd (rep.ty a) (rep.env Γ)) (compile rep data P primitive store effect body)
      (fun p => p = ((acc, env), state)) (inv remaining) (fun e => e = env)
      (3 * width) fee bodyTime (hh.trans h3)
      (by
        intro p hp
        subst p
        refine ⟨hf, hs.trans h3, henv.trans h3, rfl, ?_⟩
        exact (laws.snd (rep.ty a) (rep.env Γ) (acc, env)).trans (hfee _ (by
          change Q.size frame (acc, env) + Q.size (rep.env Γ) env ≤ 128 * width
          omega)))
      (by intro p hp; obtain ⟨ha', hs'⟩ := hsize remaining (by omega) p hp; exact ⟨ha'.trans h3, hs'.trans h3⟩)
      (by intro p hp result hresult; subst p; exact hbody remaining hr acc state hinv result hresult)
    obtain ⟨⟨hinv', henv'⟩, ht⟩ := hcontext ((acc, env), state) rfl z hz
    have hsmall : overhead (32 * (3 * width)) ≤ fee := hfee _ (by omega)
    exact ⟨⟨henv', hinv'⟩, by omega⟩
  have hiter := Bounds.iterate_remaining control queryCost rep.data.nat step loopInv
    (bodyTime + 19 * fee) tickTime cap hstep (by
      intro remaining hr p hp
      obtain ⟨⟨acc, kept⟩, state⟩ := p
      obtain ⟨hkept, hinv⟩ := hp
      dsimp only at hkept hinv
      subst kept
      obtain ⟨ha, hs⟩ := hsize remaining hr (acc, state) hinv
      have hf := hframe acc ha
      have hnat := hn remaining hr
      apply htick remaining hr
      dsimp only [frame, LanguageRepresentation.env] at *
      grind only)
  obtain ⟨hinitSize, hsaved⟩ := hsize _ hcap _ hi
  have hnSize := hn _ hcap
  have hinputCost : Q.cost (loopInput rep data P primitive store count init) (env, saved) ≤
      countTime + initTime + 9 * fee := by
    have h := (LocalBound.pair laws
      (LocalBound.compose laws (LocalBound.fst laws (rep.env Γ) store)
        (LocalBound.measured (Expression.compile rep data P primitive count)))
      (LocalBound.pair laws
        (LocalBound.pair laws (LocalBound.compose laws (LocalBound.fst laws (rep.env Γ) store)
          (LocalBound.measured (Expression.compile rep data P primitive init)))
          (LocalBound.fst laws (rep.env Γ) store))
        (LocalBound.snd laws (rep.env Γ) store))).cost_le (env, saved)
    change Q.cost (loopInput rep data P primitive store count init) (env, saved) ≤ _ at h
    apply h.trans
    dsimp only [LocalBound.pair, LocalBound.compose, LocalBound.measured,
      LocalBound.fst, LocalBound.snd, LanguageRepresentation.env] at *
    grind only
  rw [compile] at hout
  simp only [Code.run, sequenceRun, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, exists_eq_left] at hout
  obtain ⟨_, ⟨iter, hrun, rfl⟩, rfl⟩ := hout
  have h := hiter (count.denote P env, ((init.denote P env, env), saved))
    ⟨hcap, rfl, hi⟩ iter hrun
  obtain ⟨henvOut, hinvOut⟩ := h.1
  obtain ⟨haccOut, hstoreOut⟩ := hsize 0 (Nat.zero_le cap) _ hinvOut
  have hcontextOut : Q.size (rep.env Γ) iter.value.1.2 ≤ width := by rw [henvOut]; exact henv
  have houtputCost : Q.cost (loopOutput (Γ := Γ) (a := a) rep store) iter.value ≤ 5 * fee := by
    apply ((loopOutputBound laws rep store (Γ := Γ) (a := a)).cost_le iter.value).trans
    dsimp only [loopOutputBound, LocalBound.pair, LocalBound.compose, LocalBound.fst,
      LocalBound.snd, LanguageRepresentation.env] at *
    grind only
  have hcall := routing.localCall
  have hseq := routing.sequence
  refine ⟨hinvOut, ?_⟩
  dsimp only [Run.value, Run.steps, frame, fee, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.BackendProgram.Language
