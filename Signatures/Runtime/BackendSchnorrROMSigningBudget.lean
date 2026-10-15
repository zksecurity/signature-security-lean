import Signatures.Runtime.BackendSchnorrROMParts

/-! Runtime of the existing ordinary-ROM signing simulator. The two actual
draws advance distinct store invariants. Cache keys have a fixed width allowance
for a message/point pair, so repeated signing does not multiply that allowance. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeCache

open BackendProgram Parts

def signingFrameWidth (width cap : Nat) : Nat := (64 * cap + 128) * width

def signingTime (overhead : Nat → Nat)
    (width cap messageTime pointTime scaleTime subTime firstTime secondTime : Nat) : Nat :=
  firstTime + secondTime + 2 * scaleTime + subTime +
    programmingTime overhead (3 * width) cap messageTime pointTime +
      1024 * overhead (128 * signingFrameWidth width cap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M S : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def SigningInput (width cap : Nat) (env : Env (cryptoBase F G₁ G₂ K M) SigningEnv) : Prop :=
  Q.size (rep.ty message) env.1 ≤ width ∧ Q.size (rep.ty point₁) env.2.1 ≤ width ∧
    Q.size (rep.ty point₁) env.2.2.1 ≤ width ∧
    CacheCompiler.Entries (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) env.2.2.2.1 ∧
      env.2.2.2.1.length ≤ cap

def SigningOutput (width cap : Nat) (out : (G₁ × F) × List ((M × G₁) × F)) : Prop :=
  Q.size (rep.ty point₁) out.1.1 ≤ width ∧ Q.size (rep.ty scalar) out.1.2 ≤ width ∧
    CacheCompiler.Entries (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) out.2 ∧ out.2.length ≤ cap

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
theorem signing_input_size (width cap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (env : Env (cryptoBase F G₁ G₂ K M) SigningEnv)
    (hi : SigningInput (Q := Q) rep width cap env) :
    Q.size (rep.env SigningEnv) env ≤ (12 * cap + 12) * width := by
  obtain ⟨msg, g, pk, xs, u⟩ := env
  cases u
  obtain ⟨hm, hg, hp, hx, hn⟩ := hi
  have hl := CacheCompiler.list_size (key := hashKey) (val := scalar) rep sizes lists xs (3 * width) cap
    (by omega) hx hn
  have hprod := @sizes.prod_le
  dsimp only [SigningEnv, LanguageRepresentation.env] at *
  grind only

omit [Q.HasCategory] QP QS [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₁]
  [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem signing_output_size (width cap : Nat) (hh : header ≤ width)
    (out : (G₁ × F) × List ((M × G₁) × F)) (ho : SigningOutput (Q := Q) rep width cap out) :
    Q.size (rep.ty (.pair (.pair point₁ scalar) hashCache)) out ≤ (12 * cap + 7) * width := by
  obtain ⟨hr, hz, hx, hn⟩ := ho
  have hl := CacheCompiler.list_size (key := hashKey) (val := scalar) rep sizes lists out.2 (3 * width) cap
    (by omega) hx hn
  have hprod := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty] at *
  grind only

include laws dataLaws mono routing

theorem signing_bound (inv firstInv finalInv : S → Prop)
    (width cap messageTime pointTime scaleTime subTime firstTime secondTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (hsFirst : ∀ saved, firstInv saved → Q.size store saved ≤ width)
    (hsFinal : ∀ saved, finalInv saved → Q.size store saved ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ 3 * width → Q.size (rep.ty message) y ≤ 3 * width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ 3 * width → Q.size (rep.ty point₁) y ≤ 3 * width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (hscale : ∀ z : F, ∀ g : G₁, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty point₁) g ≤ width →
      Q.size (rep.ty point₁) (z • g) ≤ width ∧ (primitiveBound .scale₁).time (z, g) ≤ scaleTime)
    (hsub : ∀ g pk : G₁, Q.size (rep.ty point₁) g ≤ width → Q.size (rep.ty point₁) pk ≤ width →
      Q.size (rep.ty point₁) (g - pk) ≤ width ∧ (primitiveBound .sub₁).time (g, pk) ≤ subTime)
    (hdFirst : Bounds control queryCost draw (fun p => inv p.2)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ firstInv p.2) firstTime)
    (hdSecond : Bounds control queryCost draw (fun p => firstInv p.2)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ finalInv p.2) secondTime) :
    Bounds control queryCost (signing rep data cost primitive store draw)
      (fun p => SigningInput (Q := Q) rep width cap p.1 ∧ inv p.2)
      (fun p => SigningOutput (Q := Q) rep width (cap + 1) p.1 ∧ finalInv p.2)
      (signingTime overhead width cap messageTime pointTime scaleTime subTime firstTime secondTime) := by
  let W := signingFrameWidth width cap
  let fee := overhead (128 * W)
  let programTime := programmingTime overhead (3 * width) cap messageTime pointTime
  let pre := SigningInput (Q := Q) rep width cap
  let scalarOK := fun z : F => Q.size (rep.ty scalar) z ≤ width
  let pointOK := fun g : G₁ => Q.size (rep.ty point₁) g ≤ width
  let firstPre := fun env : Env (cryptoBase F G₁ G₂ K M) (scalar :: SigningEnv) => scalarOK env.1 ∧ pre env.2
  let sampled := fun env : Env (cryptoBase F G₁ G₂ K M) SampledEnv => scalarOK env.1 ∧ firstPre env.2
  let committed := fun env : Env (cryptoBase F G₁ G₂ K M) CommittedEnv => pointOK env.1 ∧ sampled env.2
  let programmed := fun xs : List ((M × G₁) × F) =>
    CacheCompiler.Entries (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) xs ∧ xs.length ≤ cap + 1
  let commitPre := fun env : Env (cryptoBase F G₁ G₂ K M) [scalar, scalar, point₁, point₁] =>
    scalarOK env.1 ∧ scalarOK env.2.1 ∧ pointOK env.2.2.1 ∧ pointOK env.2.2.2.1
  let programPre := CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) cap
  let post := SigningOutput (Q := Q) rep width (cap + 1)
  have hw : width ≤ W := by dsimp [W, signingFrameWidth]; nlinarith
  have hW := hh.trans hw
  have hroute : overhead (32 * W) ≤ fee := mono (by omega)
  have hstore : ∀ s, inv s → Q.size store s ≤ W := fun s h => (hs s h).trans hw
  have hfirstStore : ∀ s, firstInv s → Q.size store s ≤ W := fun s h => (hsFirst s h).trans hw
  have hfinalStore : ∀ s, finalInv s → Q.size store s ≤ W := fun s h => (hsFinal s h).trans hw
  have hinput : ∀ env, pre env → Q.size (rep.env SigningEnv) env ≤ W := by
    intro env hi
    have h := signing_input_size rep sizes lists width cap hh hu env hi
    dsimp [W, signingFrameWidth]; nlinarith
  have hfirstSmall : ∀ env, firstPre env → Q.size (rep.env (scalar :: SigningEnv)) env ≤ (12 * cap + 14) * width := by
    intro env hi
    have ht := signing_input_size rep sizes lists width cap hh hu env.2 hi.2
    have hp := sizes.prod_le (rep.ty scalar) (rep.env SigningEnv) env
    dsimp only [LanguageRepresentation.env] at hp ⊢
    have hz := hi.1
    dsimp only [scalarOK] at hz
    nlinarith
  have hfirst : ∀ env, firstPre env → Q.size (rep.env (scalar :: SigningEnv)) env ≤ W := by
    intro env hi
    have h := hfirstSmall env hi
    dsimp [W, signingFrameWidth]; nlinarith
  have hsampledSmall : ∀ env, sampled env → Q.size (rep.env SampledEnv) env ≤ (12 * cap + 16) * width := by
    intro env hi
    have ht := hfirstSmall env.2 hi.2
    have hp := sizes.prod_le (rep.ty scalar) (rep.env (scalar :: SigningEnv)) env
    dsimp only [SampledEnv, LanguageRepresentation.env] at hp ⊢
    have hz := hi.1
    dsimp only [scalarOK] at hz
    nlinarith
  have hsampled : ∀ env, sampled env → Q.size (rep.env SampledEnv) env ≤ W := by
    intro env hi
    have h := hsampledSmall env hi
    dsimp [W, signingFrameWidth]; nlinarith
  have hcommittedSmall : ∀ env, committed env → Q.size (rep.env CommittedEnv) env ≤ (12 * cap + 18) * width := by
    intro env hi
    have ht := hsampledSmall env.2 hi.2
    have hp := sizes.prod_le (rep.ty point₁) (rep.env SampledEnv) env
    dsimp only [CommittedEnv, LanguageRepresentation.env] at hp ⊢
    have hr := hi.1
    dsimp only [pointOK] at hr
    nlinarith
  have hcommitted : ∀ env, committed env → Q.size (rep.env CommittedEnv) env ≤ W := by
    intro env hi
    have h := hcommittedSmall env hi
    dsimp [W, signingFrameWidth]; nlinarith
  have hprogrammedSmall : ∀ xs, programmed xs → Q.size (rep.ty hashCache) xs ≤ (12 * cap + 15) * width := by
    intro xs hx
    have h := CacheCompiler.list_size (key := hashKey) (val := scalar) rep sizes lists xs (3 * width) (cap + 1)
      (by omega) hx.1 hx.2
    nlinarith
  have hprogrammed : ∀ xs, programmed xs → Q.size (rep.ty hashCache) xs ≤ W := by
    intro xs hx
    have h := hprogrammedSmall xs hx
    dsimp [W, signingFrameWidth]; nlinarith
  have hreturnEnv : ∀ env : Env (cryptoBase F G₁ G₂ K M) ProgrammedEnv,
      programmed env.1 ∧ committed env.2 → Q.size (rep.env ProgrammedEnv) env ≤ W := by
    intro env hi
    have ht := hcommittedSmall env.2 hi.2
    have hx := hprogrammedSmall env.1 hi.1
    have hp := sizes.prod_le (rep.ty hashCache) (rep.env CommittedEnv) env
    dsimp only [ProgrammedEnv, LanguageRepresentation.env] at hp ⊢
    dsimp [W, signingFrameWidth]; nlinarith
  have hcommitInput : ∀ env, commitPre env → Q.size (rep.env [scalar, scalar, point₁, point₁]) env ≤ W := by
    rintro ⟨z, c, g, pk, u⟩ ⟨hz, hc, hg', hp⟩
    cases u
    have hp0 := sizes.prod_le (rep.ty point₁) rep.data.unit (pk, ())
    have hp1 := sizes.prod_le (rep.ty point₁) (rep.env [point₁]) (g, pk, ())
    have hp2 := sizes.prod_le (rep.ty scalar) (rep.env [point₁, point₁]) (c, g, pk, ())
    have hp3 := sizes.prod_le (rep.ty scalar) (rep.env [scalar, point₁, point₁]) (z, c, g, pk, ())
    dsimp only [scalarOK, pointOK] at hz hc hg' hp
    dsimp only [W, signingFrameWidth, LanguageRepresentation.env] at hp0 hp1 hp2 hp3 ⊢
    nlinarith
  have hcommitResult (env : Env (cryptoBase F G₁ G₂ K M) [scalar, scalar, point₁, point₁]) (hi : commitPre env) :
      pointOK (simulatedCommit.denote (arithmetic F G₁ G₂ K M cost) env) :=
    (hsub _ _ (hscale _ _ hi.1 hi.2.2.1).1 (hscale _ _ hi.2.1 hi.2.2.2).1).1
  have hcommit := Language.ret_bound_of_width mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) simulatedCommit
    commitPre pointOK finalInv W (2 * scaleTime + subTime + 64 * fee) hcommitInput hfinalStore
    (fun env hi => ⟨hcommitResult env hi, (hcommitResult env hi).trans hw⟩)
    (by
      rintro ⟨z, c, g, pk, u⟩ hi
      cases u
      obtain ⟨hzg, htZ⟩ := hscale z g hi.1 hi.2.2.1
      obtain ⟨hcp, htC⟩ := hscale c pk hi.2.1 hi.2.2.2
      obtain ⟨hR, htR⟩ := hsub _ _ hzg hcp
      exact commit_cost rep data cost primitive sizes laws dataLaws primitiveBound mono z c g pk W scaleTime subTime
        hW (hcommitInput _ hi) (hzg.trans hw) (hcp.trans hw) (hR.trans hw) htZ htC htR)
  have hcommitCall := Language.call_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) (.ret simulatedCommit) commitArgs
    sampled commitPre finalInv (fun p => pointOK p.1 ∧ finalInv p.2) W (64 * fee) _ hW hsampled hfinalStore
    (by
      intro env hi
      have hp : commitPre (commitArgs.denote (arithmetic F G₁ G₂ K M cost) env) :=
        ⟨hi.1, hi.2.1, hi.2.2.2.1, hi.2.2.2.2.1⟩
      exact ⟨hp, hcommitInput _ hp⟩)
    (fun env hi => commitArgs_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hsampled env hi)) hcommit
  have hprogramInput : ∀ env, programPre env → Q.size (rep.env [hashKey, scalar, hashCache]) env ≤ W := by
    intro env hi
    have h := CacheCompiler.input_size (key := hashKey) (val := scalar) rep sizes lists (3 * width) cap
      (by omega) (by omega) env hi
    dsimp [W, signingFrameWidth]; nlinarith
  have hprogram := Language.ret_bound_of_width mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) (cacheProgram (val := scalar) hashEq)
    programPre programmed finalInv W programTime hprogramInput hfinalStore
    (by
      rintro ⟨k, c, xs, u⟩ hi
      cases u
      have hp := programming_property rep cost (3 * width) cap k c xs hi
      exact ⟨hp, hprogrammed _ hp⟩)
    (by
      rintro ⟨k, c, xs, u⟩ hi
      cases u
      exact programming_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
        (3 * width) cap messageTime pointTime (by omega) (by omega) (fun b => (hb b).trans (by omega)) hm hg k c xs hi)
  have hprogramCall := Language.call_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) (.ret (cacheProgram hashEq)) programArgs
    committed programPre finalInv (fun p => programmed p.1 ∧ finalInv p.2) W (64 * fee) _ hW hcommitted hfinalStore
    (by
      intro env hi
      have hk : Q.size (rep.ty hashKey) (env.2.2.2.1, env.1) ≤ 3 * width := by
        have hp := sizes.prod_le (rep.ty message) (rep.ty point₁) (env.2.2.2.1, env.1)
        have hm' := hi.2.2.2.1
        have hr := hi.1
        dsimp only [pointOK, LanguageRepresentation.ty] at *
        omega
      have hp : programPre (programArgs.denote (arithmetic F G₁ G₂ K M cost) env) :=
        ⟨hk, hi.2.2.1.trans (by omega), hi.2.2.2.2.2.2.1, hi.2.2.2.2.2.2.2⟩
      exact ⟨hp, hprogramInput _ hp⟩)
    (fun env hi => programArgs_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hcommitted env hi)) hprogram
  have hreturn := Language.ret_bound_of_width mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) signingReturn
    (fun env => programmed env.1 ∧ committed env.2) post finalInv W (64 * fee) hreturnEnv hfinalStore
    (by
      intro env hi
      have ho : post (signingReturn.denote (arithmetic F G₁ G₂ K M cost) env) :=
        ⟨hi.2.1, hi.2.2.1, hi.1.1, hi.1.2⟩
      refine ⟨ho, ?_⟩
      have h := signing_output_size rep sizes lists width (cap + 1) hh _ ho
      dsimp [W, signingFrameWidth]; nlinarith)
    (fun env hi => signingReturn_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hreturnEnv env hi))
  have hlast := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw)
    (.call (.ret (cacheProgram hashEq)) programArgs) (.ret signingReturn) committed programmed finalInv
    (fun p => post p.1 ∧ finalInv p.2) W _ _ hW hcommitted hprogrammed hfinalStore hprogramCall hreturn
  have htail := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw)
    (.call (.ret simulatedCommit) commitArgs)
    (.bind (.call (.ret (cacheProgram hashEq)) programArgs) (.ret signingReturn)) sampled pointOK finalInv
    (fun p => post p.1 ∧ finalInv p.2) W _ _ hW hsampled (fun _ hp => hp.trans hw) hfinalStore hcommitCall hlast
  have hqueryFirst := Language.query_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) .sample .unit
    pre (fun _ => True) inv (fun p => scalarOK p.1 ∧ firstInv p.2) W fee firstTime hW hinput hstore
    (fun _ _ => ⟨True.intro, hu.trans hw⟩)
    (fun env hi => (dataLaws.unit (rep.env _) env).trans (mono (by have h := hinput env hi; omega)))
    (fun input hi => hdFirst input hi.2)
  have hquerySecond := Language.query_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) .sample .unit
    firstPre (fun _ => True) firstInv (fun p => scalarOK p.1 ∧ finalInv p.2) W fee secondTime hW hfirst hfirstStore
    (fun _ _ => ⟨True.intro, hu.trans hw⟩)
    (fun env hi => (dataLaws.unit (rep.env _) env).trans (mono (by have h := hfirst env hi; omega)))
    (fun input hi => hdSecond input hi.2)
  have hsecond := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) (.query .sample .unit)
    (.bind (.call (.ret simulatedCommit) commitArgs)
      (.bind (.call (.ret (cacheProgram hashEq)) programArgs) (.ret signingReturn))) firstPre scalarOK firstInv finalInv
    (fun p => post p.1 ∧ finalInv p.2) W _ _ hW hfirst (fun _ hp => hp.trans hw) hfirstStore hfinalStore hquerySecond htail
  have hall := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) (.query .sample .unit)
    (.bind (.query .sample .unit) (.bind (.call (.ret simulatedCommit) commitArgs)
      (.bind (.call (.ret (cacheProgram hashEq)) programArgs) (.ret signingReturn)))) pre scalarOK inv firstInv
    (fun p => post p.1 ∧ finalInv p.2) W _ _ hW hinput (fun _ hp => hp.trans hw) hstore hfirstStore hqueryFirst hsecond
  intro input hi z hz
  rw [signing, signCached_eq] at hz
  obtain ⟨ho, ht⟩ := hall input hi z hz
  refine ⟨ho, ?_⟩
  change z.steps ≤ firstTime + secondTime + 2 * scaleTime + subTime + programTime + 1024 * fee
  omega

omit sizes lists laws dataLaws mono routing in
theorem signingTime_polynomial (overhead : Nat → Nat → Nat)
    (width cap messageTime pointTime scaleTime subTime firstTime secondTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) (hMessage : PolynomiallyBounded messageTime)
    (hPoint : PolynomiallyBounded pointTime) (hScale : PolynomiallyBounded scaleTime)
    (hSub : PolynomiallyBounded subTime) (hFirst : PolynomiallyBounded firstTime)
    (hSecond : PolynomiallyBounded secondTime) :
    PolynomiallyBounded (fun n => signingTime (overhead n) (width n) (cap n) (messageTime n)
      (pointTime n) (scaleTime n) (subTime n) (firstTime n) (secondTime n)) := by
  unfold signingTime programmingTime scanTime scanComparisonTime scanFrameWidth
    CacheProgramming.frameWidth signingFrameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.ListROM.NativeCache
