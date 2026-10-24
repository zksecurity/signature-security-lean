import Proofs.Runtime.BackendLanguageBudget
import Proofs.Runtime.BackendLookupCost
import Proofs.Runtime.Cache

/-! Native budgets for complete association-list cache access. The scan, cache
hit, sampling on a miss, insertion, and retained compiler environments all use
the same backend. Only comparison and sampling primitives need external cost
contracts; the cache procedure's cost is derived from its compiled syntax. -/

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

def Entries (width : Nat) (xs : List (key.Value base × val.Value base)) : Prop :=
  ∀ p ∈ xs, Q.size (rep.ty key) p.1 ≤ width ∧ Q.size (rep.ty val) p.2 ≤ width

def Input (width cap : Nat) (env : Env base [key, val, .list (.pair key val)]) : Prop :=
  Q.size (rep.ty key) env.1 ≤ width ∧ Q.size (rep.ty val) env.2.1 ≤ width ∧
    Entries (Q := Q) rep width env.2.2.1 ∧ env.2.2.1.length ≤ cap

def Output (width cap : Nat) (value : val.Value base × List (key.Value base × val.Value base)) : Prop :=
  Q.size (rep.ty val) value.1 ≤ width ∧ Entries (Q := Q) rep width value.2 ∧ value.2.length ≤ cap

/-- Includes the largest local environment on the miss path, independently of
the cardinality of the key type. The ambient store is bounded separately. -/
def frameWidth (width cap : Nat) : Nat := 4 * ((4 * cap + 32) * width)

include sizes lists

omit [Q.HasCategory] QP QS in
theorem list_size (xs : List (key.Value base × val.Value base)) (width cap : Nat)
    (hh : header ≤ width) (he : Entries (Q := Q) rep width xs) (hn : xs.length ≤ cap) :
    Q.size (rep.ty (.list (.pair key val))) xs ≤ (4 * cap + 1) * width := by
  have h := lists.size_le_cap (rep.ty (.pair key val)) xs (3 * width) cap (by
    intro p hp
    have hs := sizes.prod_le (rep.ty key) (rep.ty val) p
    obtain ⟨hk, hv⟩ := he p hp
    exact hs.trans (by omega)) hn
  dsimp only [LanguageRepresentation.ty] at h ⊢
  nlinarith [Nat.mul_le_mul_left cap hh]

omit [Q.HasCategory] QP QS in
theorem input_size (width cap : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (env : Env base [key, val, .list (.pair key val)]) (hi : Input (Q := Q) rep width cap env) :
    Q.size (rep.env [key, val, .list (.pair key val)]) env ≤ (4 * cap + 7) * width := by
  obtain ⟨k, d, xs, u⟩ := env
  cases u
  obtain ⟨hk, hd, he, hn⟩ := hi
  have hl := list_size rep sizes lists xs width cap hh he hn
  have hprod := @sizes.prod_le
  dsimp only [LanguageRepresentation.env] at *
  grind only

omit [Q.HasCategory] QP QS in
theorem output_size (width cap : Nat) (hh : header ≤ width)
    (value : val.Value base × List (key.Value base × val.Value base))
    (ho : Output (Q := Q) rep width cap value) :
    Q.size (rep.ty (.pair val (.list (.pair key val)))) value ≤ (4 * cap + 3) * width := by
  obtain ⟨hv, he, hn⟩ := ho
  have hl := list_size rep sizes lists value.2 width cap hh he hn
  have hp := sizes.prod_le (rep.ty val) (rep.ty (.list (.pair key val))) value
  dsimp only [LanguageRepresentation.ty] at *
  nlinarith

omit sizes lists in
private theorem lookupValue_property {K V : Type} [DecidableEq K] (valid : V → Prop)
    (k : K) (d : V) (xs : List (K × V)) (hd : valid d) (hx : ∀ p ∈ xs, valid p.2) :
    valid (lookupValue k d xs).2 := by
  induction xs with
  | nil => exact hd
  | cons p xs ih =>
      by_cases h : p.1 = k
      · simpa [lookupValue, h] using hx p (by simp)
      · simpa [lookupValue, h] using ih (fun q hq => hx q (by simp [hq]))

omit sizes lists [C.HasSum] [C.HasOption] [Q.HasCategory] QP QS in
theorem lookup_value_size (eq : Op (.pair key key) .bool) [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (width cap : Nat) (env : Env base [key, val, .list (.pair key val)])
    (hi : Input (Q := Q) rep width cap env) :
    Q.size (rep.ty val) ((lookup eq).denote P env).2 ≤ width := by
  obtain ⟨k, d, xs, u⟩ := env
  cases u
  have hc := lookup_correct P eq heq k d xs
  rw [Expr.run_value] at hc
  rw [hc]
  exact lookupValue_property (fun v => Q.size (rep.ty val) v ≤ width) k d xs hi.2.1
    (fun p hp => (hi.2.2.1 p hp).2)

def hit : Expr Op [.pair .bool val, key, val, .list (.pair key val)]
    (.pair val (.list (.pair key val))) :=
  .pair (.snd (.var .here)) (.var (.there (.there (.there .here))))

def insert : Expr Op [val, .pair .bool val, key, val, .list (.pair key val)]
    (.pair val (.list (.pair key val))) :=
  .pair (.var .here) (.cons (.pair (.var (.there (.there .here))) (.var .here))
    (.var (.there (.there (.there (.there .here))))))

include laws dataLaws primitiveBound mono

omit lists in
theorem hit_cost (env : Env base [.pair .bool val, key, val, .list (.pair key val)])
    (width : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [.pair .bool val, key, val, .list (.pair key val)]) env ≤ width) :
    Q.cost (Expression.compile rep data P primitive hit) env ≤ 16 * overhead (32 * width) := by
  refine (Expression.cost_compile_le rep data P primitive laws dataLaws primitiveBound hit env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [hit, Expression.compileBound, Expression.variableBound, LocalBound.pair,
    LocalBound.compose, LocalBound.fst, LocalBound.snd, LanguageRepresentation.ty,
    LanguageRepresentation.env, Expr.denote, Var.get] at *
  grind only

theorem insert_cost (env : Env base [val, .pair .bool val, key, val, .list (.pair key val)])
    (width : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [val, .pair .bool val, key, val, .list (.pair key val)]) env ≤ width) :
    Q.cost (Expression.compile rep data P primitive insert) env ≤ 24 * overhead (32 * width) := by
  refine (Expression.cost_compile_le rep data P primitive laws dataLaws primitiveBound insert env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [insert, Expression.compileBound, Expression.variableBound, LocalBound.pair,
    LocalBound.compose, LocalBound.fst, LocalBound.snd, DataCostLaws.consBound,
    LanguageRepresentation.ty, LanguageRepresentation.env, Expr.denote, Var.get] at *
  grind only

omit lists in
theorem condition_cost (env : Env base [.pair .bool val, key, val, .list (.pair key val)])
    (width : Nat) (_hh : header ≤ width)
    (hi : Q.size (rep.env [.pair .bool val, key, val, .list (.pair key val)]) env ≤ width) :
    Q.cost (Expression.compile rep data P primitive (.fst (.var .here))) env ≤
      3 * overhead (32 * width) := by
  refine (Expression.cost_compile_le rep data P primitive laws dataLaws primitiveBound (.fst (.var .here)) env).trans ?_
  have hfst := @sizes.fst_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.fst, LanguageRepresentation.ty, LanguageRepresentation.env, Expr.denote, Var.get] at *
  grind only

variable {I S : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (store : C.Str S)
  (effect : {a b : Ty Atom} → Cmd a b →
    Code Q spec iface (StepClass.HasProd.prod (rep.ty a) store)
      (StepClass.HasProd.prod (rep.ty b) store))

include routing

/-- Complete compiled cache access, including context copies and the sampling
effect on a miss. The resulting cache has at most one additional entry. Bounds
on the key type's cardinality, or on unencountered keys, are not required. -/
theorem cacheGet_bound (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (inv : S → Prop) (width cap comparisonTime drawTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (he : ∀ x y, Q.size (rep.ty key) x ≤ width → Q.size (rep.ty key) y ≤ width →
      (primitiveBound eq).time (x, y) ≤ comparisonTime)
    (hd : Bounds control queryCost (effect draw) (fun p => inv p.2)
      (fun p => Q.size (rep.ty val) p.1 ≤ width ∧ inv p.2) drawTime) :
    Bounds control queryCost (Language.compile rep data P primitive store effect (cacheGet eq draw))
      (fun p => Input (Q := Q) rep width cap p.1 ∧ inv p.2)
      (fun p => Output (Q := Q) rep width (cap + 1) p.1 ∧ inv p.2)
      (cap * (comparisonTime + 257 * overhead (32 * frameWidth width cap)) + drawTime +
        132 * overhead (32 * frameWidth width cap)) := by
  let W := frameWidth width cap
  let fee := overhead (32 * W)
  let scan := cap * (comparisonTime + 257 * fee) + 32 * fee
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
      (Language.compile rep data P primitive store effect (.ret (lookup eq)))
      (fun p => pre p.1 ∧ inv p.2) (fun p => found p.1 ∧ inv p.2) (scan + 2 * fee) := by
    apply Language.ret_bound_of_width mono control queryCost routing rep data P primitive store effect
      (lookup eq) pre found inv W scan hinput hstore
    · intro env hi
      have hf := lookup_value_size rep P eq heq width cap env hi
      exact ⟨hf, (hfound _ hf).trans (by dsimp [W, frameWidth]; nlinarith)⟩
    · intro env hi
      obtain ⟨k, d, xs, u⟩ := env
      cases u
      have h := LookupCompiler.lookup_cost_bound rep data P primitive laws dataLaws primitiveBound
        sizes mono lists eq k d xs width comparisonTime cap hh hu hb hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
        (fun p hp => he p.1 k (hi.2.2.1 p hp).1 hi.1)
      apply h.trans
      have hc : overhead (128 * ((4 * cap + 1) * width)) ≤ fee := by
        apply mono
        dsimp [W, frameWidth]
        nlinarith
      dsimp only [scan]
      gcongr
  have hhit : Bounds control queryCost
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
  have hquery : Bounds control queryCost
      (Language.compile rep data P primitive store effect (.query draw .unit))
      (fun p => missPre p.1 ∧ inv p.2)
      (fun p => Q.size (rep.ty val) p.1 ≤ width ∧ inv p.2) (fee + drawTime + 3 * fee) := by
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
      (fun p => (Q.size (rep.ty val) p.1.1 ≤ width ∧ missPre p.1.2) ∧ inv p.2)
      (fun p => post p.1 ∧ inv p.2) (24 * fee + 2 * fee) := by
    apply Language.ret_bound_of_width mono control queryCost routing rep data P primitive store effect
      insert _ post inv W (24 * fee) hmiss hstore
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
  have hmissCode := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data P primitive
    store effect (.query draw .unit) (.ret insert) missPre (fun v => Q.size (rep.ty val) v ≤ width)
    inv (fun p => post p.1 ∧ inv p.2) W (fee + drawTime + 3 * fee) (24 * fee + 2 * fee)
    hW (fun env hi => hbranch env hi.1) (fun _ hv => hv.trans hw) hstore hquery hinsert
  have hbranchCode := Language.branch_bound_of_width sizes laws mono control queryCost routing rep data P primitive
    store effect (.fst (.var .here)) (.ret hit) (.bind (.query draw .unit) (.ret insert))
    branchPre inv (fun p => post p.1 ∧ inv p.2) W (3 * fee) (16 * fee + 2 * fee)
    ((fee + drawTime + 3 * fee) + (24 * fee + 2 * fee) + 20 * fee)
    hW hbranch hstore (fun b => (hb b).trans hw) dataLaws
    (fun env hi => condition_cost rep data P primitive sizes laws dataLaws primitiveBound mono env W hW (hbranch env hi))
    hhit hmissCode
  have hall := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data P primitive
    store effect (.ret (lookup eq)) (.branch (.fst (.var .here)) (.ret hit)
      (.bind (.query draw .unit) (.ret insert))) pre found inv (fun p => post p.1 ∧ inv p.2)
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

/-- Specialize to a sampling leaf that retains the ambient store. In addition
to the complete budget, this proves that cache access returns the same ambient
store: the updated cache is an ordinary output until its caller writes it. -/
theorem cacheGet_sampling_bound (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (drawCode : Code Q spec iface rep.data.unit (rep.ty val))
    (heffect : effect draw = .first store drawCode)
    (width cap comparisonTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (he : ∀ x y, Q.size (rep.ty key) x ≤ width → Q.size (rep.ty key) y ≤ width →
      (primitiveBound eq).time (x, y) ≤ comparisonTime)
    (hd : Bounds control queryCost drawCode (fun _ => True)
      (fun v => Q.size (rep.ty val) v ≤ width) sampleTime)
    (env : Env base [key, val, .list (.pair key val)])
    (hi : Input (Q := Q) rep width cap env) (saved : S) (hs : Q.size store saved ≤ width)
    (z : Run ((val.Value base × List (key.Value base × val.Value base)) × S))
    (hz : z ∈ support ((Language.compile rep data P primitive store effect (cacheGet eq draw)).run
      control queryCost (env, saved))) :
    Output (Q := Q) rep width (cap + 1) z.value.1 ∧ z.value.2 = saved ∧
      z.steps ≤ cap * (comparisonTime + 257 * overhead (32 * frameWidth width cap)) + sampleTime +
        133 * overhead (32 * frameWidth width cap) := by
  let fee := overhead (32 * frameWidth width cap)
  have hretain := Bounds.first control queryCost store drawCode (fun _ => True)
    (fun v => Q.size (rep.ty val) v ≤ width) (fun s => s = saved) sampleTime fee hd (by
      intro state hstate value hv
      subst state
      apply (routing.retain _ _).trans
      apply mono
      dsimp [frameWidth]
      nlinarith)
  have hcache := cacheGet_bound rep data P primitive sizes lists laws dataLaws primitiveBound mono
    control queryCost routing store effect eq draw heq (fun s => s = saved)
    width cap comparisonTime (sampleTime + fee) hh hu hb
    (by intro state hstate; simpa only [hstate] using hs) he (by
      intro input hinput out hout
      rw [heffect] at hout
      exact hretain input ⟨True.intro, hinput⟩ out hout)
  obtain ⟨⟨hout, hstore⟩, ht⟩ := hcache (env, saved) ⟨hi, rfl⟩ z hz
  exact ⟨hout, hstore, by dsimp only [fee] at ht; omega⟩

end Signatures.Runtime.BackendProgram.CacheCompiler
