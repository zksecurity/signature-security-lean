import Proofs.Runtime.BackendSchnorrROMParts

/-! Complete runtime and output-capacity bounds for the actual managed-cache
program. Both caches and the stateful draw are charged, including retained copies. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeCache

open BackendProgram Parts

def managedFrameWidth (width managedCap liveCap : Nat) : Nat :=
  (16 * (managedCap + liveCap) + 128) * width

def managedTime (overhead : Nat → Nat) (width managedCap liveCap messageTime pointTime drawTime : Nat) : Nat :=
  scanTime overhead width managedCap messageTime pointTime +
    liveTime overhead width liveCap messageTime pointTime drawTime +
      512 * overhead (128 * managedFrameWidth width managedCap liveCap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M S : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def ManagedInput (width managedCap liveCap : Nat) (env : Env (cryptoBase F G₁ G₂ K M) ManagedEnv) : Prop :=
  CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep width managedCap
      (env.1, env.2.1, env.2.2.1, ()) ∧
    CacheCompiler.Entries (Q := Q) (key := hashKey) (val := scalar) rep width env.2.2.2.1 ∧
      env.2.2.2.1.length ≤ liveCap

def ManagedOutput (width managedCap liveCap : Nat)
    (out : F × List ((M × G₁) × F) × List ((M × G₁) × F)) : Prop :=
  CacheCompiler.Output (Q := Q) (key := hashKey) (val := scalar) rep width managedCap (out.1, out.2.1) ∧
    CacheCompiler.Entries (Q := Q) (key := hashKey) (val := scalar) rep width out.2.2 ∧ out.2.2.length ≤ liveCap

variable (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (store : C.Str S)
  (draw : Code Q unifSpec iface (StepClass.HasProd.prod rep.data.unit store)
    (StepClass.HasProd.prod (rep.ty scalar) store))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat) (routing : RoutingCostLaws control overhead)

include sizes lists

omit [Q.HasCategory] QP QS [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₁]
  [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem managed_input_size (width managedCap liveCap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (env : Env (cryptoBase F G₁ G₂ K M) ManagedEnv)
    (hi : ManagedInput (Q := Q) rep width managedCap liveCap env) :
    Q.size (rep.env ManagedEnv) env ≤ (4 * (managedCap + liveCap) + 9) * width := by
  obtain ⟨k, d, xs, ys, u⟩ := env
  cases u
  obtain ⟨⟨hk, hd, hx, hn⟩, hy, hm⟩ := hi
  have hsx := CacheCompiler.list_size (key := hashKey) (val := scalar) rep sizes lists xs width managedCap hh hx hn
  have hsy := CacheCompiler.list_size (key := hashKey) (val := scalar) rep sizes lists ys width liveCap hh hy hm
  have hprod := @sizes.prod_le
  dsimp only [ManagedEnv, LanguageRepresentation.env] at *
  grind only

omit [Q.HasCategory] QP QS [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₁]
  [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem managed_output_size (width managedCap liveCap : Nat) (hh : header ≤ width)
    (out : F × List ((M × G₁) × F) × List ((M × G₁) × F))
    (ho : ManagedOutput (Q := Q) rep width managedCap liveCap out) :
    Q.size (rep.ty (.pair scalar (.pair hashCache hashCache))) out ≤ (4 * (managedCap + liveCap) + 5) * width := by
  obtain ⟨⟨hv, hx, hn⟩, hy, hm⟩ := ho
  have hsx := CacheCompiler.list_size (key := hashKey) (val := scalar) rep sizes lists out.2.1 width managedCap hh hx hn
  have hsy := CacheCompiler.list_size (key := hashKey) (val := scalar) rep sizes lists out.2.2 width liveCap hh hy hm
  have hprod := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty] at *
  grind only

include laws dataLaws mono routing

theorem managed_bound (inv nextInv : S → Prop) (advance : ∀ saved, inv saved → nextInv saved)
    (width managedCap liveCap messageTime pointTime drawTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (hsNext : ∀ saved, nextInv saved → Q.size store saved ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ width → Q.size (rep.ty point₁) y ≤ width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (hd : Bounds control queryCost draw (fun p => inv p.2)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ nextInv p.2) drawTime) :
    Bounds control queryCost (managed rep data cost primitive store draw)
      (fun p => ManagedInput (Q := Q) rep width managedCap liveCap p.1 ∧ inv p.2)
      (fun p => ManagedOutput (Q := Q) rep width (managedCap + 1) (liveCap + 1) p.1 ∧ nextInv p.2)
      (managedTime overhead width managedCap liveCap messageTime pointTime drawTime) := by
  let W := managedFrameWidth width managedCap liveCap
  let fee := overhead (128 * W)
  let scan := scanTime overhead width managedCap messageTime pointTime
  let liveBudget := liveTime overhead width liveCap messageTime pointTime drawTime
  let pre := ManagedInput (Q := Q) rep width managedCap liveCap
  let found := fun p : Bool × F => Q.size (rep.ty scalar) p.2 ≤ width
  let checked := fun env : Env (cryptoBase F G₁ G₂ K M) CheckedEnv => found env.1 ∧ pre env.2
  let miss := fun env : Env (cryptoBase F G₁ G₂ K M) CheckedEnv =>
    checked env ∧ condition.denote (arithmetic F G₁ G₂ K M cost) env ≠ true
  let fetched := CacheCompiler.Output (Q := Q) (key := hashKey) (val := scalar) rep width (liveCap + 1)
  let post := ManagedOutput (Q := Q) rep width (managedCap + 1) (liveCap + 1)
  have hw : width ≤ W := by dsimp [W, managedFrameWidth]; nlinarith
  have hW := hh.trans hw
  have hroute : overhead (32 * W) ≤ fee := mono (by omega)
  have hstore : ∀ s, inv s → Q.size store s ≤ W := fun s h => (hs s h).trans hw
  have hnext : ∀ s, nextInv s → Q.size store s ≤ W := fun s h => (hsNext s h).trans hw
  have hinput : ∀ env, pre env → Q.size (rep.env ManagedEnv) env ≤ W := by
    intro env hi
    have h := managed_input_size rep sizes lists width managedCap liveCap hh hu env hi
    dsimp [W, managedFrameWidth]; nlinarith
  have hfound : ∀ p, found p → Q.size (rep.ty (.pair .bool scalar)) p ≤ 3 * width := by
    intro p hp
    have h := sizes.prod_le rep.data.bool (rep.ty scalar) p
    have hb' := hb p.1
    dsimp only [found, LanguageRepresentation.ty] at *
    omega
  have hcheckedSmall : ∀ env, checked env → Q.size (rep.env CheckedEnv) env ≤
      (4 * (managedCap + liveCap) + 13) * width := by
    intro env hi
    have hf := hfound env.1 hi.1
    have ht := managed_input_size rep sizes lists width managedCap liveCap hh hu env.2 hi.2
    have hp := sizes.prod_le (rep.ty (.pair .bool scalar)) (rep.env ManagedEnv) env
    dsimp only [CheckedEnv, LanguageRepresentation.env] at hp ⊢
    nlinarith
  have hchecked : ∀ env, checked env → Q.size (rep.env CheckedEnv) env ≤ W := by
    intro env hi
    have h := hcheckedSmall env hi
    dsimp [W, managedFrameWidth]; nlinarith
  have hfetched : ∀ p, fetched p → Q.size (rep.ty (.pair scalar hashCache)) p ≤
      (4 * (liveCap + 1) + 3) * width :=
    CacheCompiler.output_size rep sizes lists width (liveCap + 1) hh
  have hfetchEnv : ∀ env : Env (cryptoBase F G₁ G₂ K M) FetchedEnv,
      fetched env.1 ∧ miss env.2 → Q.size (rep.env FetchedEnv) env ≤ W := by
    intro env hi
    have hf := hfetched env.1 hi.1
    have ht := hcheckedSmall env.2 hi.2.1
    have hp := sizes.prod_le (rep.ty (.pair scalar hashCache)) (rep.env CheckedEnv) env
    dsimp only [FetchedEnv, LanguageRepresentation.env] at hp ⊢
    dsimp [W, managedFrameWidth]; nlinarith
  have houtput : ∀ p, post p → Q.size (rep.ty (.pair scalar (.pair hashCache hashCache))) p ≤ W := by
    intro p hp
    have h := managed_output_size rep sizes lists width (managedCap + 1) (liveCap + 1) hh p hp
    dsimp [W, managedFrameWidth]; nlinarith
  have hcacheInput (cap : Nat) (hcap : cap ≤ managedCap + liveCap) (env : Env (cryptoBase F G₁ G₂ K M) [hashKey, scalar, hashCache])
      (hi : CacheCompiler.Input (Q := Q) rep width cap env) : Q.size (rep.env _) env ≤ W := by
    have h := CacheCompiler.input_size (key := hashKey) (val := scalar) rep sizes lists width cap hh hu env hi
    dsimp [W, managedFrameWidth]
    nlinarith [Nat.mul_le_mul_right width hcap]
  have hscan := Language.ret_bound_of_width mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) (lookupExpr (val := scalar) hashEq)
    (CacheCompiler.Input (Q := Q) rep width managedCap) found inv W scan
    (hcacheInput managedCap (by omega)) hstore
    (by
      intro env hi
      have h := CacheCompiler.lookupExpr_value_size (val := scalar) rep (arithmetic F G₁ G₂ K M cost)
        hashEq (hashEq_value cost) width managedCap env hi
      exact ⟨h, (hfound _ h).trans (by dsimp [W, managedFrameWidth]; nlinarith)⟩)
    (by
      rintro ⟨k, d, xs, u⟩ hi
      cases u
      exact lookup_cost rep data cost primitive sizes laws dataLaws primitiveBound mono lists
        width managedCap messageTime pointTime hh hu hb hm hg k d xs hi)
  have hscanCall := Language.call_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) (.ret (lookupExpr hashEq)) managedArgs
    pre (CacheCompiler.Input (Q := Q) rep width managedCap) inv (fun p => found p.1 ∧ inv p.2)
    W (64 * fee) (scan + 2 * overhead (32 * W)) hW hinput hstore
    (fun env hi => ⟨hi.1, hcacheInput managedCap (by omega) _ hi.1⟩)
    (fun env hi => managedArgs_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hinput env hi)) hscan
  have hlive := live_bound rep data cost primitive store draw sizes lists laws dataLaws primitiveBound mono
    control queryCost routing inv nextInv advance width liveCap messageTime pointTime drawTime hh hu hb hs hsNext hm hg hd
  have hliveCall := Language.call_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) (cacheGetExpr hashEq .sample) liveArgs
    miss (CacheCompiler.Input (Q := Q) rep width liveCap) inv (fun p => fetched p.1 ∧ nextInv p.2)
    W (64 * fee) liveBudget hW (fun env hi => hchecked env hi.1) hstore
    (by
      intro env hi
      have hp : CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep width liveCap
          (env.2.1, env.2.2.1, env.2.2.2.2.1, ()) :=
        ⟨hi.1.2.1.1, hi.1.2.1.2.1, hi.1.2.2.1, hi.1.2.2.2⟩
      exact ⟨hp, hcacheInput liveCap (by omega) _ hp⟩)
    (fun env hi => liveArgs_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hchecked env hi.1)) hlive
  have hhitOld := Language.ret_bound_of_width mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) managedHit
    (fun env => checked env ∧ condition.denote (arithmetic F G₁ G₂ K M cost) env = true) post inv W (64 * fee)
    (fun env hi => hchecked env hi.1) hstore
    (by
      intro env hi
      have ho : post (managedHit.denote (arithmetic F G₁ G₂ K M cost) env) :=
        ⟨⟨hi.1.1, hi.1.2.1.2.2.1, hi.1.2.1.2.2.2.trans (Nat.le_succ _)⟩,
          hi.1.2.2.1, hi.1.2.2.2.trans (Nat.le_succ _)⟩
      exact ⟨ho, houtput _ ho⟩)
    (fun env hi => managedHit_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hchecked env hi.1))
  have hhit : Bounds control queryCost
      (Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) (.ret managedHit))
      (fun p => (checked p.1 ∧ condition.denote (arithmetic F G₁ G₂ K M cost) p.1 = true) ∧ inv p.2)
      (fun p => post p.1 ∧ nextInv p.2) (64 * fee + 2 * overhead (32 * W)) := by
    intro input hi z hz
    obtain ⟨ho, ht⟩ := hhitOld input hi z hz
    exact ⟨⟨ho.1, advance _ ho.2⟩, ht⟩
  have hinsert := Language.ret_bound_of_width mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) managedInsert
    (fun env => fetched env.1 ∧ miss env.2) post nextInv W (128 * fee) hfetchEnv hnext
    (by
      intro env hi
      have ho : post (managedInsert.denote (arithmetic F G₁ G₂ K M cost) env) := by
        refine ⟨⟨hi.1.1, ?_, Nat.succ_le_succ hi.2.1.2.1.2.2.2⟩, hi.1.2.1, hi.1.2.2⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨hi.2.1.2.1.1, hi.1.1⟩
        · exact hi.2.1.2.1.2.2.1 p hp
      exact ⟨ho, houtput _ ho⟩)
    (fun env hi => managedInsert_cost rep data cost primitive sizes laws dataLaws primitiveBound mono lists env W hW
      (hu.trans hw) (hfetchEnv env hi))
  have hmiss := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw)
    (.call (cacheGetExpr hashEq .sample) liveArgs) (.ret managedInsert) miss fetched inv nextInv
    (fun p => post p.1 ∧ nextInv p.2) W _ _ hW (fun env hi => hchecked env hi.1)
    (fun p hp => (hfetched p hp).trans (by dsimp [W, managedFrameWidth]; nlinarith))
    hstore hnext hliveCall hinsert
  have hbranch := Language.branch_bound_of_width sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) condition (.ret managedHit)
    (.bind (.call (cacheGetExpr hashEq .sample) liveArgs) (.ret managedInsert)) checked inv
    (fun p => post p.1 ∧ nextInv p.2) W (8 * fee) _ _ hW hchecked hstore (fun b => (hb b).trans hw) dataLaws
    (fun env hi => condition_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hchecked env hi)) hhit hmiss
  have hall := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw)
    (.call (.ret (lookupExpr hashEq)) managedArgs)
    (.branch condition (.ret managedHit) (.bind (.call (cacheGetExpr hashEq .sample) liveArgs) (.ret managedInsert)))
    pre found inv (fun p => post p.1 ∧ nextInv p.2) W _ _ hW hinput
    (fun p hp => (hfound p hp).trans (by dsimp [W, managedFrameWidth]; nlinarith)) hstore hscanCall hbranch
  intro input hi z hz
  rw [managed, managedGet_eq] at hz
  obtain ⟨ho, ht⟩ := hall input hi z hz
  refine ⟨ho, ?_⟩
  have hmax : max (64 * fee + 2 * overhead (32 * W))
      (64 * fee + liveBudget + 3 * overhead (32 * W) +
        (128 * fee + 2 * overhead (32 * W)) + 20 * overhead (32 * W)) ≤ liveBudget + 217 * fee := by
    apply max_le <;> omega
  change z.steps ≤ scan + liveBudget + 512 * fee
  omega

omit sizes lists laws dataLaws mono routing in
theorem managedTime_polynomial (overhead : Nat → Nat → Nat)
    (width managedCap liveCap messageTime pointTime drawTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hManaged : PolynomiallyBounded managedCap) (hLive : PolynomiallyBounded liveCap)
    (hMessage : PolynomiallyBounded messageTime) (hPoint : PolynomiallyBounded pointTime)
    (hDraw : PolynomiallyBounded drawTime) :
    PolynomiallyBounded (fun n => managedTime (overhead n) (width n) (managedCap n) (liveCap n)
      (messageTime n) (pointTime n) (drawTime n)) := by
  unfold managedTime scanTime liveTime scanComparisonTime scanFrameWidth managedFrameWidth CacheCompiler.frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.ListROM.NativeCache
