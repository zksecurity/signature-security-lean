import Proofs.Runtime.BackendCacheCost
import Proofs.Runtime.BackendLookupExprCost
import Proofs.Runtime.CacheExpr

/-! Complete native cache access with an expression comparator and a stateful
sampler. A miss can advance the store invariant; a hit preserves the old store
and embeds it into the reserved output capacity. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.CacheCompiler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty Atom} → (instr : Op a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  {key val : Ty Atom}

omit [C.HasSum] [C.HasOption] [Q.HasCategory] QP QS in
theorem lookupExpr_value_size (eq : Expr Op [key, key] .bool) [DecidableEq (key.Value base)]
    (heq : ∀ x y, eq.denote P (x, y, ()) = decide (x = y))
    (width cap : Nat) (env : Env base [key, val, .list (.pair key val)])
    (hi : Input (Q := Q) rep width cap env) :
    Q.size (rep.ty val) ((lookupExpr eq).denote P env).2 ≤ width := by
  obtain ⟨k, d, xs, u⟩ := env
  cases u
  have hc := lookupExpr_value P eq heq k d xs
  rw [Expr.run_value] at hc
  rw [hc]
  have hx : ∀ p ∈ xs, Q.size (rep.ty val) p.2 ≤ width := fun p hp => (hi.2.2.1 p hp).2
  have hd := hi.2.1
  clear hc hi
  induction xs with
  | nil => exact hd
  | cons p xs ih =>
      by_cases h : p.1 = k
      · simpa [lookupValue, h] using hx p (by simp)
      · simpa [lookupValue, h] using ih (fun q hq => hx q (by simp [hq])) hd

variable {I S : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (store : C.Str S)
  (effect : {a b : Ty Atom} → Cmd a b →
    Code Q spec iface (StepClass.HasProd.prod (rep.ty a) store)
      (StepClass.HasProd.prod (rep.ty b) store))

include routing

include sizes lists laws dataLaws primitiveBound mono

theorem cacheGetExpr_bound (eq : Expr Op [key, key] .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, eq.denote P (x, y, ()) = decide (x = y))
    (inv nextInv : S → Prop) (advance : ∀ s, inv s → nextInv s) (width cap comparisonTime drawTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (hsNext : ∀ saved, nextInv saved → Q.size store saved ≤ width)
    (he : ∀ k d xs, Input (Q := Q) rep width cap (k, d, xs, ()) →
      ∀ p ∈ xs, ∀ acc : Bool × val.Value base, Q.size (rep.ty val) acc.2 ≤ (4 * cap + 1) * width →
      (Expression.compileBound rep data P primitive laws dataLaws primitiveBound
        (eq.weakenTail [.pair key val, .pair .bool val, key, val, .list (.pair key val)])).time
          (p.1, k, p, acc, k, d, xs, ()) ≤ comparisonTime)
    (hd : Bounds control queryCost (effect draw) (fun p => inv p.2)
      (fun p => Q.size (rep.ty val) p.1 ≤ width ∧ nextInv p.2) drawTime) :
    Bounds control queryCost (Language.compile rep data P primitive store effect (cacheGetExpr eq draw))
      (fun p => Input (Q := Q) rep width cap p.1 ∧ inv p.2)
      (fun p => Output (Q := Q) rep width (cap + 1) p.1 ∧ nextInv p.2)
      (cap * (comparisonTime + 513 * overhead (32 * frameWidth width cap)) + drawTime +
        132 * overhead (32 * frameWidth width cap)) := by
  let W := frameWidth width cap
  let fee := overhead (32 * W)
  let scan := cap * (comparisonTime + 513 * fee) + 32 * fee
  let pre := Input (Q := Q) rep (key := key) (val := val) width cap
  let found := fun p : Bool × val.Value base => Q.size (rep.ty val) p.2 ≤ width
  let branchPre := fun env : Env base [.pair .bool val, key, val, .list (.pair key val)] =>
    found env.1 ∧ pre env.2
  let missPre := fun env : Env base [.pair .bool val, key, val, .list (.pair key val)] =>
    branchPre env ∧ (Expr.fst (Expr.var Var.here) : Expr Op _ .bool).denote P env ≠ true
  let post := Output (Q := Q) rep (key := key) (val := val) width (cap + 1)
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hW := hh.trans hw
  have hstore : ∀ saved, inv saved → Q.size store saved ≤ W := fun s h => (hs s h).trans hw
  have hstoreNext : ∀ saved, nextInv saved → Q.size store saved ≤ W := fun s h => (hsNext s h).trans hw
  have hinput : ∀ env, pre env → Q.size (rep.env [key, val, .list (.pair key val)]) env ≤ W := by
    intro env hi
    have h := input_size rep sizes lists width cap hh hu env hi
    dsimp [W, frameWidth]
    nlinarith
  have hfound : ∀ p, found p → Q.size (rep.ty (.pair .bool val)) p ≤ 3 * width := by
    intro p hp
    have h := sizes.prod_le rep.data.bool (rep.ty val) p
    have hbool := hb p.1
    dsimp only [LanguageRepresentation.ty]
    exact h.trans (by dsimp [found] at hp; omega)
  have hbranchSmall : ∀ env, branchPre env →
      Q.size (rep.env [.pair .bool val, key, val, .list (.pair key val)]) env ≤ (4 * cap + 11) * width := by
    intro env hi
    have hf := hfound env.1 hi.1
    have ht := input_size rep sizes lists width cap hh hu env.2 hi.2
    have hp := sizes.prod_le (rep.ty (.pair .bool val)) (rep.env [key, val, .list (.pair key val)]) env
    dsimp only [LanguageRepresentation.env]
    nlinarith
  have hbranch : ∀ env, branchPre env →
      Q.size (rep.env [.pair .bool val, key, val, .list (.pair key val)]) env ≤ W := by
    intro env hi
    have h := hbranchSmall env hi
    dsimp [W, frameWidth]
    nlinarith
  have hmiss : ∀ env : Env base [val, .pair .bool val, key, val, .list (.pair key val)],
      (Q.size (rep.ty val) env.1 ≤ width ∧ missPre env.2) → Q.size (rep.env _) env ≤ W := by
    intro env hi
    have ht := hbranchSmall env.2 hi.2.1
    have hp := sizes.prod_le (rep.ty val)
      (rep.env [.pair .bool val, key, val, .list (.pair key val)]) env
    dsimp only [LanguageRepresentation.env] at hp ⊢
    dsimp [W, frameWidth]
    nlinarith [hi.1]
  have houtput : ∀ value, post value → Q.size (rep.ty (.pair val (.list (.pair key val)))) value ≤ W := by
    intro value ho
    have h := output_size rep sizes lists width (cap + 1) hh value ho
    dsimp [W, frameWidth]
    nlinarith
  have hscan : Bounds control queryCost
      (Language.compile rep data P primitive store effect (.ret (lookupExpr eq)))
      (fun p => pre p.1 ∧ inv p.2) (fun p => found p.1 ∧ inv p.2) (scan + 2 * fee) := by
    apply Language.ret_bound_of_width mono control queryCost routing rep data P primitive store effect
      (lookupExpr eq) pre found inv W scan hinput hstore
    · intro env hi
      have hf := lookupExpr_value_size rep P eq heq width cap env hi
      exact ⟨hf, (hfound _ hf).trans (by dsimp [W, frameWidth]; nlinarith)⟩
    · intro env hi
      obtain ⟨k, d, xs, u⟩ := env
      cases u
      have h := LookupExprCompiler.lookup_cost_bound rep data P primitive laws dataLaws primitiveBound
        sizes mono lists eq k d xs width comparisonTime cap hh hu hb hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
        (he k d xs hi)
      apply h.trans
      have hc : overhead (128 * ((4 * cap + 1) * width)) ≤ fee := by
        apply mono
        dsimp [W, frameWidth]
        nlinarith
      dsimp only [scan]
      gcongr
  have hhitOld : Bounds control queryCost
      (Language.compile rep data P primitive store effect (.ret (hit (Op := Op) (key := key) (val := val))))
      (fun p => (branchPre p.1 ∧ (Expr.fst (Expr.var Var.here) : Expr Op _ .bool).denote P p.1 = true) ∧ inv p.2)
      (fun p => post p.1 ∧ inv p.2) (16 * fee + 2 * fee) := by
    apply Language.ret_bound_of_width mono control queryCost routing rep data P primitive store effect
      hit (fun env => branchPre env ∧ (Expr.fst (Expr.var Var.here) : Expr Op _ .bool).denote P env = true)
      post inv W (16 * fee) (fun env hi => hbranch env hi.1) hstore
    · intro env hi
      have hout : post (hit.denote P env) := by
        refine ⟨hi.1.1, hi.1.2.2.2.1, ?_⟩
        exact hi.1.2.2.2.2.trans (Nat.le_succ cap)
      exact ⟨hout, houtput _ hout⟩
    · intro env hi
      exact hit_cost rep data P primitive sizes laws dataLaws primitiveBound mono env W hW (hbranch env hi.1)
  have hhit : Bounds control queryCost
      (Language.compile rep data P primitive store effect (.ret (hit (Op := Op) (key := key) (val := val))))
      (fun p => (branchPre p.1 ∧ (Expr.fst (Expr.var Var.here) : Expr Op _ .bool).denote P p.1 = true) ∧ inv p.2)
      (fun p => post p.1 ∧ nextInv p.2) (16 * fee + 2 * fee) := by
    intro input hi z hz
    obtain ⟨ho, ht⟩ := hhitOld input hi z hz
    exact ⟨⟨ho.1, advance _ ho.2⟩, ht⟩
  have hquery : Bounds control queryCost
      (Language.compile rep data P primitive store effect (.query draw .unit))
      (fun p => missPre p.1 ∧ inv p.2)
      (fun p => Q.size (rep.ty val) p.1 ≤ width ∧ nextInv p.2) (fee + drawTime + 3 * fee) := by
    apply Language.query_bound_of_width sizes mono control queryCost routing rep data P primitive store effect
      draw .unit missPre (fun _ => True) inv _ W fee drawTime hW
      (fun env hi => hbranch env hi.1) hstore (fun _ _ => ⟨True.intro, hu.trans hw⟩)
    · intro env hi
      apply (dataLaws.unit (rep.env _) env).trans
      apply mono
      have henv := hbranch env hi.1
      dsimp only [W, fee] at *
      omega
    · intro input hi
      exact hd input hi.2
  have hinsert : Bounds control queryCost
      (Language.compile rep data P primitive store effect (.ret (insert (Op := Op) (key := key) (val := val))))
      (fun p => (Q.size (rep.ty val) p.1.1 ≤ width ∧ missPre p.1.2) ∧ nextInv p.2)
      (fun p => post p.1 ∧ nextInv p.2) (24 * fee + 2 * fee) := by
    apply Language.ret_bound_of_width mono control queryCost routing rep data P primitive store effect
      insert _ post nextInv W (24 * fee) hmiss hstoreNext
    · intro env hi
      have hout : post (insert.denote P env) := by
        refine ⟨hi.1, ?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨hi.2.1.2.1, hi.1⟩
          · exact hi.2.1.2.2.2.1 p hp
        · exact Nat.succ_le_succ hi.2.1.2.2.2.2
      exact ⟨hout, houtput _ hout⟩
    · intro env hi
      exact insert_cost rep data P primitive sizes lists laws dataLaws primitiveBound mono env W hW (hmiss env hi)
  have hmissCode := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data P primitive
    store effect (.query draw .unit) (.ret insert) missPre (fun v => Q.size (rep.ty val) v ≤ width)
    inv nextInv (fun p => post p.1 ∧ nextInv p.2) W (fee + drawTime + 3 * fee) (24 * fee + 2 * fee)
    hW (fun env hi => hbranch env hi.1) (fun _ hv => hv.trans hw) hstore hstoreNext hquery hinsert
  have hbranchCode := Language.branch_bound_of_width sizes laws mono control queryCost routing rep data P primitive
    store effect (.fst (.var .here)) (.ret hit) (.bind (.query draw .unit) (.ret insert))
    branchPre inv (fun p => post p.1 ∧ nextInv p.2) W (3 * fee) (16 * fee + 2 * fee)
    ((fee + drawTime + 3 * fee) + (24 * fee + 2 * fee) + 20 * fee)
    hW hbranch hstore (fun b => (hb b).trans hw) dataLaws
    (fun env hi => condition_cost rep data P primitive sizes laws dataLaws primitiveBound mono env W hW (hbranch env hi))
    hhit hmissCode
  have hall := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data P primitive
    store effect (.ret (lookupExpr eq)) (.branch (.fst (.var .here)) (.ret hit)
      (.bind (.query draw .unit) (.ret insert))) pre found inv (fun p => post p.1 ∧ nextInv p.2)
    W (scan + 2 * fee) _ hW hinput
    (fun p hp => (hfound p hp).trans (by dsimp [W, frameWidth]; nlinarith)) hstore hscan hbranchCode
  intro input hi z hz
  obtain ⟨hout, ht⟩ := hall input hi z hz
  refine ⟨hout, ?_⟩
  have hm : max (16 * fee + 2 * fee)
      ((fee + drawTime + 3 * fee) + (24 * fee + 2 * fee) + 20 * fee) ≤ drawTime + 50 * fee := by
    apply max_le <;> omega
  dsimp only [scan, fee, W] at *
  omega

end Signatures.Runtime.BackendProgram.CacheCompiler
