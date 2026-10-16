import Signatures.Runtime.BackendSchnorrNonzeroSigningParts

/-! Complete all-path runtime of the actual nonzero signing code. Three
successive sampler states are distinguished, and every retained environment,
repair operation and cache-programming traversal is charged. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroSigning.Native

open BackendProgram Parts ListROM.NativeCache

def signingFrameWidth (width cap : Nat) : Nat := (128 * cap + 256) * width

def signingTime (overhead : Nat → Nat)
    (width cap messageTime pointTime scaleTime subTime zeroTime addTime firstTime secondTime thirdTime : Nat) : Nat :=
  firstTime + secondTime + thirdTime + 3 * scaleTime + subTime + zeroTime + pointTime + addTime +
    programmingTime overhead (3 * width) cap messageTime pointTime +
      2048 * overhead (128 * signingFrameWidth width cap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {F G₁ G₂ K M S : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (store : C.Str S)
  (fieldDraw nonzeroDraw : Code Q unifSpec iface (StepClass.HasProd.prod rep.data.unit store)
    (StepClass.HasProd.prod (rep.ty scalar) store))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat) (routing : RoutingCostLaws control overhead)

include sizes lists

omit [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
private theorem frame_bounds (width cap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) :
  let W := signingFrameWidth width cap
  let pre := SigningInput (Q := Q) rep width cap
  let scalarOK := fun z : F => Q.size (rep.ty scalar) z ≤ width
  let pointOK := fun g : G₁ => Q.size (rep.ty point₁) g ≤ width
  let signatureOK := fun p : G₁ × F => pointOK p.1 ∧ scalarOK p.2
  let firstPre := fun env : Env (cryptoBase F G₁ G₂ K M) (scalar :: Input) => scalarOK env.1 ∧ pre env.2
  let secondPre := fun env : Env (cryptoBase F G₁ G₂ K M) (scalar :: scalar :: Input) => scalarOK env.1 ∧ firstPre env.2
  let sampled := fun env : Env (cryptoBase F G₁ G₂ K M) Sampled => scalarOK env.1 ∧ secondPre env.2
  let committed := fun env : Env (cryptoBase F G₁ G₂ K M) Committed => pointOK env.1 ∧ sampled env.2
  let repaired := fun env : Env (cryptoBase F G₁ G₂ K M) Repaired => signatureOK env.1 ∧ committed env.2
  let programmed := fun xs : List ((M × G₁) × F) =>
    CacheCompiler.Entries (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) xs ∧ xs.length ≤ cap + 1
  let commitPre := fun env : Env (cryptoBase F G₁ G₂ K M) [scalar, scalar, point₁, point₁] =>
    scalarOK env.1 ∧ scalarOK env.2.1 ∧ pointOK env.2.2.1 ∧ pointOK env.2.2.2.1
  let repairPre := fun env : Env (cryptoBase F G₁ G₂ K M) [point₁, scalar, scalar, point₁] =>
    pointOK env.1 ∧ scalarOK env.2.1 ∧ scalarOK env.2.2.1 ∧ pointOK env.2.2.2.1
  let programPre := CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) cap
  (∀ env, pre env → Q.size (rep.env Input) env ≤ W) ∧
    (∀ env, firstPre env → Q.size (rep.env (scalar :: Input)) env ≤ W) ∧
    (∀ env, secondPre env → Q.size (rep.env (scalar :: scalar :: Input)) env ≤ W) ∧
    (∀ env, sampled env → Q.size (rep.env Sampled) env ≤ W) ∧
    (∀ env, committed env → Q.size (rep.env Committed) env ≤ W) ∧
    (∀ p, signatureOK p → Q.size (rep.ty (.pair point₁ scalar)) p ≤ W) ∧
    (∀ env, repaired env → Q.size (rep.env Repaired) env ≤ W) ∧
    (∀ xs, programmed xs → Q.size (rep.ty hashCache) xs ≤ W) ∧
    (∀ env : Env (cryptoBase F G₁ G₂ K M) (hashCache :: Repaired), programmed env.1 ∧ repaired env.2 → Q.size (rep.env (hashCache :: Repaired)) env ≤ W) ∧
    (∀ env, commitPre env → Q.size (rep.env [scalar, scalar, point₁, point₁]) env ≤ W) ∧
    (∀ env, repairPre env → Q.size (rep.env [point₁, scalar, scalar, point₁]) env ≤ W) ∧
    (∀ env, programPre env → Q.size (rep.env [hashKey, scalar, hashCache]) env ≤ W) := by
  let W := signingFrameWidth width cap
  let pre := SigningInput (Q := Q) rep width cap
  let scalarOK := fun z : F => Q.size (rep.ty scalar) z ≤ width
  let pointOK := fun g : G₁ => Q.size (rep.ty point₁) g ≤ width
  let signatureOK := fun p : G₁ × F => pointOK p.1 ∧ scalarOK p.2
  let firstPre := fun env : Env (cryptoBase F G₁ G₂ K M) (scalar :: Input) => scalarOK env.1 ∧ pre env.2
  let secondPre := fun env : Env (cryptoBase F G₁ G₂ K M) (scalar :: scalar :: Input) => scalarOK env.1 ∧ firstPre env.2
  let sampled := fun env : Env (cryptoBase F G₁ G₂ K M) Sampled => scalarOK env.1 ∧ secondPre env.2
  let committed := fun env : Env (cryptoBase F G₁ G₂ K M) Committed => pointOK env.1 ∧ sampled env.2
  let repaired := fun env : Env (cryptoBase F G₁ G₂ K M) Repaired => signatureOK env.1 ∧ committed env.2
  let programmed := fun xs : List ((M × G₁) × F) =>
    CacheCompiler.Entries (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) xs ∧ xs.length ≤ cap + 1
  let commitPre := fun env : Env (cryptoBase F G₁ G₂ K M) [scalar, scalar, point₁, point₁] =>
    scalarOK env.1 ∧ scalarOK env.2.1 ∧ pointOK env.2.2.1 ∧ pointOK env.2.2.2.1
  let repairPre := fun env : Env (cryptoBase F G₁ G₂ K M) [point₁, scalar, scalar, point₁] =>
    pointOK env.1 ∧ scalarOK env.2.1 ∧ scalarOK env.2.2.1 ∧ pointOK env.2.2.2.1
  let programPre := CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) cap
  have hinputSmall : ∀ env, pre env → Q.size (rep.env Input) env ≤ (12 * cap + 12) * width :=
    signing_input_size rep sizes lists width cap hh hu
  have hinput : ∀ env, pre env → Q.size (rep.env Input) env ≤ W := by
    intro env hi
    have h := hinputSmall env hi
    dsimp [W, signingFrameWidth]; nlinarith
  have hfirstSmall : ∀ env, firstPre env → Q.size (rep.env (scalar :: Input)) env ≤ (12 * cap + 14) * width := by
    intro env hi
    have ht := hinputSmall env.2 hi.2
    have hp := sizes.prod_le (rep.ty scalar) (rep.env Input) env
    dsimp only [LanguageRepresentation.env] at hp ⊢
    have hz := hi.1
    dsimp only [scalarOK] at hz
    nlinarith
  have hfirst : ∀ env, firstPre env → Q.size (rep.env (scalar :: Input)) env ≤ W := by
    intro env hi
    have h := hfirstSmall env hi
    dsimp [W, signingFrameWidth]; nlinarith
  have hsecondSmall : ∀ env, secondPre env → Q.size (rep.env (scalar :: scalar :: Input)) env ≤ (12 * cap + 16) * width := by
    intro env hi
    have ht := hfirstSmall env.2 hi.2
    have hp := sizes.prod_le (rep.ty scalar) (rep.env (scalar :: Input)) env
    dsimp only [LanguageRepresentation.env] at hp ⊢
    have hz := hi.1
    dsimp only [scalarOK] at hz
    nlinarith
  have hsecond : ∀ env, secondPre env → Q.size (rep.env (scalar :: scalar :: Input)) env ≤ W := by
    intro env hi
    have h := hsecondSmall env hi
    dsimp [W, signingFrameWidth]; nlinarith
  have hsampledSmall : ∀ env, sampled env → Q.size (rep.env Sampled) env ≤ (12 * cap + 18) * width := by
    intro env hi
    have ht := hsecondSmall env.2 hi.2
    have hp := sizes.prod_le (rep.ty scalar) (rep.env (scalar :: scalar :: Input)) env
    dsimp only [Sampled, LanguageRepresentation.env] at hp ⊢
    have hz := hi.1
    dsimp only [scalarOK] at hz
    nlinarith
  have hsampled : ∀ env, sampled env → Q.size (rep.env Sampled) env ≤ W := by
    intro env hi
    have h := hsampledSmall env hi
    dsimp [W, signingFrameWidth]; nlinarith
  have hcommittedSmall : ∀ env, committed env → Q.size (rep.env Committed) env ≤ (12 * cap + 20) * width := by
    intro env hi
    have ht := hsampledSmall env.2 hi.2
    have hp := sizes.prod_le (rep.ty point₁) (rep.env Sampled) env
    dsimp only [Committed, LanguageRepresentation.env] at hp ⊢
    have hr := hi.1
    dsimp only [pointOK] at hr
    nlinarith
  have hcommitted : ∀ env, committed env → Q.size (rep.env Committed) env ≤ W := by
    intro env hi
    have h := hcommittedSmall env hi
    dsimp [W, signingFrameWidth]; nlinarith
  have hsignatureSmall : ∀ p, signatureOK p → Q.size (rep.ty (.pair point₁ scalar)) p ≤ 3 * width := by
    intro p hp
    have hh' := sizes.prod_le (rep.ty point₁) (rep.ty scalar) p
    dsimp only [signatureOK, scalarOK, pointOK, LanguageRepresentation.ty] at *
    omega
  have hsignature : ∀ p, signatureOK p → Q.size (rep.ty (.pair point₁ scalar)) p ≤ W := by
    intro p hp
    have h := hsignatureSmall p hp
    dsimp [W, signingFrameWidth]; nlinarith
  have hrepairedSmall : ∀ env, repaired env → Q.size (rep.env Repaired) env ≤ (12 * cap + 24) * width := by
    intro env hi
    have ht := hcommittedSmall env.2 hi.2
    have hr := hsignatureSmall env.1 hi.1
    have hp := sizes.prod_le (rep.ty (.pair point₁ scalar)) (rep.env Committed) env
    dsimp only [Repaired, LanguageRepresentation.env] at hp ⊢
    nlinarith
  have hrepaired : ∀ env, repaired env → Q.size (rep.env Repaired) env ≤ W := by
    intro env hi
    have h := hrepairedSmall env hi
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
  have hreturnEnv : ∀ env : Env (cryptoBase F G₁ G₂ K M) (hashCache :: Repaired),
      programmed env.1 ∧ repaired env.2 → Q.size (rep.env (hashCache :: Repaired)) env ≤ W := by
    intro env hi
    have ht := hrepairedSmall env.2 hi.2
    have hx := hprogrammedSmall env.1 hi.1
    have hp := sizes.prod_le (rep.ty hashCache) (rep.env Repaired) env
    dsimp only [LanguageRepresentation.env] at hp ⊢
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
  have hrepairInput : ∀ env, repairPre env → Q.size (rep.env [point₁, scalar, scalar, point₁]) env ≤ W := by
    rintro ⟨R, z, a, g, u⟩ ⟨hR, hz, ha, hg'⟩
    cases u
    have hp0 := sizes.prod_le (rep.ty point₁) rep.data.unit (g, ())
    have hp1 := sizes.prod_le (rep.ty scalar) (rep.env [point₁]) (a, g, ())
    have hp2 := sizes.prod_le (rep.ty scalar) (rep.env [scalar, point₁]) (z, a, g, ())
    have hp3 := sizes.prod_le (rep.ty point₁) (rep.env [scalar, scalar, point₁]) (R, z, a, g, ())
    dsimp only [scalarOK, pointOK] at hR hz ha hg'
    dsimp only [W, signingFrameWidth, LanguageRepresentation.env] at hp0 hp1 hp2 hp3 ⊢
    nlinarith
  have hprogramInput : ∀ env, programPre env → Q.size (rep.env [hashKey, scalar, hashCache]) env ≤ W := by
    intro env hi
    have h := CacheCompiler.input_size (key := hashKey) (val := scalar) rep sizes lists (3 * width) cap
      (by omega) (by omega) env hi
    dsimp [W, signingFrameWidth]; nlinarith
  exact ⟨hinput, hfirst, hsecond, hsampled, hcommitted, hsignature, hrepaired, hprogrammed, hreturnEnv, hcommitInput, hrepairInput, hprogramInput⟩

include laws dataLaws mono routing

theorem code_bound (inv firstInv secondInv finalInv : S → Prop)
    (width cap messageTime pointTime scaleTime subTime zeroTime addTime firstTime secondTime thirdTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (hsFirst : ∀ saved, firstInv saved → Q.size store saved ≤ width)
    (hsSecond : ∀ saved, secondInv saved → Q.size store saved ≤ width)
    (hsFinal : ∀ saved, finalInv saved → Q.size store saved ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ 3 * width → Q.size (rep.ty message) y ≤ 3 * width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ 3 * width → Q.size (rep.ty point₁) y ≤ 3 * width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (hscale : ∀ z : F, ∀ g : G₁, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty point₁) g ≤ width →
      Q.size (rep.ty point₁) (z • g) ≤ width ∧ (primitiveBound .scale₁).time (z, g) ≤ scaleTime)
    (hsub : ∀ g pk : G₁, Q.size (rep.ty point₁) g ≤ width → Q.size (rep.ty point₁) pk ≤ width →
      Q.size (rep.ty point₁) (g - pk) ≤ width ∧ (primitiveBound .sub₁).time (g, pk) ≤ subTime)
    (hzero : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (htzero : (primitiveBound .zero₁).time () ≤ zeroTime)
    (hadd : ∀ z a : F, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty scalar) a ≤ width →
      Q.size (rep.ty scalar) (z + a) ≤ width ∧ (primitiveBound .add).time (z, a) ≤ addTime)
    (hdFirst : Bounds control queryCost fieldDraw (fun p => inv p.2)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ firstInv p.2) firstTime)
    (hdSecond : Bounds control queryCost fieldDraw (fun p => firstInv p.2)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ secondInv p.2) secondTime)
    (hdThird : Bounds control queryCost nonzeroDraw (fun p => secondInv p.2)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ finalInv p.2) thirdTime) :
    Bounds control queryCost (code rep data cost primitive store fieldDraw nonzeroDraw)
      (fun p => SigningInput (Q := Q) rep width cap p.1 ∧ inv p.2)
      (fun p => SigningOutput (Q := Q) rep width (cap + 1) p.1 ∧ finalInv p.2)
      (signingTime overhead width cap messageTime pointTime scaleTime subTime zeroTime addTime firstTime secondTime thirdTime) := by
  let W := signingFrameWidth width cap
  let fee := overhead (128 * W)
  let programTime := programmingTime overhead (3 * width) cap messageTime pointTime
  let pre := SigningInput (Q := Q) rep width cap
  let scalarOK := fun z : F => Q.size (rep.ty scalar) z ≤ width
  let pointOK := fun g : G₁ => Q.size (rep.ty point₁) g ≤ width
  let signatureOK := fun p : G₁ × F => pointOK p.1 ∧ scalarOK p.2
  let firstPre := fun env : Env (cryptoBase F G₁ G₂ K M) (scalar :: Input) => scalarOK env.1 ∧ pre env.2
  let secondPre := fun env : Env (cryptoBase F G₁ G₂ K M) (scalar :: scalar :: Input) => scalarOK env.1 ∧ firstPre env.2
  let sampled := fun env : Env (cryptoBase F G₁ G₂ K M) Sampled => scalarOK env.1 ∧ secondPre env.2
  let committed := fun env : Env (cryptoBase F G₁ G₂ K M) Committed => pointOK env.1 ∧ sampled env.2
  let repaired := fun env : Env (cryptoBase F G₁ G₂ K M) Repaired => signatureOK env.1 ∧ committed env.2
  let programmed := fun xs : List ((M × G₁) × F) =>
    CacheCompiler.Entries (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) xs ∧ xs.length ≤ cap + 1
  let commitPre := fun env : Env (cryptoBase F G₁ G₂ K M) [scalar, scalar, point₁, point₁] =>
    scalarOK env.1 ∧ scalarOK env.2.1 ∧ pointOK env.2.2.1 ∧ pointOK env.2.2.2.1
  let repairPre := fun env : Env (cryptoBase F G₁ G₂ K M) [point₁, scalar, scalar, point₁] =>
    pointOK env.1 ∧ scalarOK env.2.1 ∧ scalarOK env.2.2.1 ∧ pointOK env.2.2.2.1
  let programPre := CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) cap
  let post := SigningOutput (Q := Q) rep width (cap + 1)
  have hw : width ≤ W := by dsimp [W, signingFrameWidth]; nlinarith
  have hW := hh.trans hw
  have hroute : overhead (32 * W) ≤ fee := mono (by omega)
  have hstore : ∀ s, inv s → Q.size store s ≤ W := fun s h => (hs s h).trans hw
  have hfirstStore : ∀ s, firstInv s → Q.size store s ≤ W := fun s h => (hsFirst s h).trans hw
  have hsecondStore : ∀ s, secondInv s → Q.size store s ≤ W := fun s h => (hsSecond s h).trans hw
  have hfinalStore : ∀ s, finalInv s → Q.size store s ≤ W := fun s h => (hsFinal s h).trans hw
  obtain ⟨hinput, hfirst, hsecond, hsampled, hcommitted, hsignature, hrepaired, hprogrammed, hreturnEnv, hcommitInput, hrepairInput, hprogramInput⟩ :=
    frame_bounds rep sizes lists width cap hh hu
  have hcommitResult (env : Env (cryptoBase F G₁ G₂ K M) [scalar, scalar, point₁, point₁]) (hi : commitPre env) :
      pointOK (simulatedCommit.denote (arithmetic F G₁ G₂ K M cost) env) :=
    (hsub _ _ (hscale _ _ hi.1 hi.2.2.1).1 (hscale _ _ hi.2.1 hi.2.2.2).1).1
  have hcommit := Language.ret_bound_of_width mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) simulatedCommit
    commitPre pointOK finalInv W (2 * scaleTime + subTime + 64 * fee) hcommitInput hfinalStore
    (fun env hi => ⟨hcommitResult env hi, (hcommitResult env hi).trans hw⟩)
    (by
      rintro ⟨z, c, g, pk, u⟩ hi
      cases u
      obtain ⟨hzg, htZ⟩ := hscale z g hi.1 hi.2.2.1
      obtain ⟨hcp, htC⟩ := hscale c pk hi.2.1 hi.2.2.2
      obtain ⟨hR, htR⟩ := hsub _ _ hzg hcp
      exact ListROM.NativeCache.Parts.commit_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
        z c g pk W scaleTime subTime hW (hcommitInput _ hi) (hzg.trans hw) (hcp.trans hw) (hR.trans hw) htZ htC htR)
  have hcommitCall := Language.call_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) (.ret simulatedCommit) commitArgs
    sampled commitPre finalInv (fun p => pointOK p.1 ∧ finalInv p.2) W (128 * fee) _ hW hsampled hfinalStore
    (by
      rintro ⟨a, z, c, msg, g, pk, xs, u⟩ ⟨ha, hz, hc, hm', hg', hp, hx, hn⟩
      cases u
      have hp' : commitPre (commitArgs.denote (arithmetic F G₁ G₂ K M cost) (a, z, c, msg, g, pk, xs, ())) :=
        ⟨hz, hc, hg', hp⟩
      exact ⟨hp', hcommitInput _ hp'⟩)
    (fun env hi => commitArgs_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hsampled env hi)) hcommit
  have hrepairResult (env : Env (cryptoBase F G₁ G₂ K M) [point₁, scalar, scalar, point₁]) (hi : repairPre env) :
      signatureOK (repair.denote (arithmetic F G₁ G₂ K M cost) env) := by
    rcases env with ⟨R, z, a, g, u⟩
    cases u
    rw [repair_denote]
    by_cases h : R = 0
    · simp only [h, ↓reduceIte]
      exact ⟨(hscale a g hi.2.2.1 hi.2.2.2).1, (hadd z a hi.2.1 hi.2.2.1).1⟩
    · simp only [h, ↓reduceIte]
      exact ⟨hi.1, hi.2.1⟩
  have hrepair := Language.ret_bound_of_width mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) repair
    repairPre signatureOK finalInv W (repairTime overhead W zeroTime pointTime scaleTime addTime) hrepairInput hfinalStore
    (fun env hi => ⟨hrepairResult env hi, hsignature _ (hrepairResult env hi)⟩)
    (by
      rintro ⟨R, z, a, g, u⟩ hi
      cases u
      obtain ⟨hs', hts⟩ := hscale a g hi.2.2.1 hi.2.2.2
      obtain ⟨ha', hta⟩ := hadd z a hi.2.1 hi.2.2.1
      apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
        laws dataLaws primitiveBound _ _).trans
      exact repair_expression_time rep data cost primitive sizes laws dataLaws primitiveBound mono R z a g W
        zeroTime pointTime scaleTime addTime hW (hu.trans hw) (fun b => (hb b).trans hw)
        (hrepairInput _ hi) (hzero.trans hw) (hs'.trans hw) (ha'.trans hw) htzero
        (hg R 0 (hi.1.trans (by omega)) (hzero.trans (by omega))) hts hta)
  have hrepairCall := Language.call_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) (.ret repair) repairArgs
    committed repairPre finalInv (fun p => signatureOK p.1 ∧ finalInv p.2) W (128 * fee) _ hW hcommitted hfinalStore
    (by
      rintro ⟨R, a, z, c, msg, g, pk, xs, u⟩ ⟨hR, ha, hz, hc, hm', hg', hp, hx, hn⟩
      cases u
      have hp' : repairPre (repairArgs.denote (arithmetic F G₁ G₂ K M cost) (R, a, z, c, msg, g, pk, xs, ())) :=
        ⟨hR, hz, ha, hg'⟩
      exact ⟨hp', hrepairInput _ hp'⟩)
    (fun env hi => repairArgs_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hcommitted env hi)) hrepair
  have hprogram := Language.ret_bound_of_width mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) (cacheProgram (val := scalar) hashEq)
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
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) (.ret (cacheProgram hashEq)) programArgs
    repaired programPre finalInv (fun p => programmed p.1 ∧ finalInv p.2) W (128 * fee) _ hW hrepaired hfinalStore
    (by
      rintro ⟨sig, R, a, z, c, msg, g, pk, xs, u⟩ ⟨⟨hr, hz'⟩, hR, ha, hz, hc, hm', hg', hp, hx, hn⟩
      cases u
      have hk : Q.size (rep.ty hashKey) (msg, sig.1) ≤ 3 * width := by
        have hp' := sizes.prod_le (rep.ty message) (rep.ty point₁) (msg, sig.1)
        dsimp only [scalarOK, pointOK, LanguageRepresentation.ty] at *
        omega
      have hp' : programPre (programArgs.denote (arithmetic F G₁ G₂ K M cost) (sig, R, a, z, c, msg, g, pk, xs, ())) :=
        ⟨hk, hc.trans (by omega), hx, hn⟩
      exact ⟨hp', hprogramInput _ hp'⟩)
    (fun env hi => programArgs_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hrepaired env hi)) hprogram
  have hreturn := Language.ret_bound_of_width mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) returnValue
    (fun env => programmed env.1 ∧ repaired env.2) post finalInv W (128 * fee) hreturnEnv hfinalStore
    (by
      intro env hi
      have ho : post (returnValue.denote (arithmetic F G₁ G₂ K M cost) env) :=
        ⟨hi.2.1.1, hi.2.1.2, hi.1.1, hi.1.2⟩
      refine ⟨ho, ?_⟩
      have h := signing_output_size rep sizes lists width (cap + 1) hh _ ho
      dsimp [W, signingFrameWidth]; nlinarith)
    (fun env hi => returnValue_cost rep data cost primitive sizes laws dataLaws primitiveBound mono env W hW
      (hu.trans hw) (hreturnEnv env hi))
  have hfinish := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw)
    (.call (.ret (cacheProgram hashEq)) programArgs) (.ret returnValue) repaired programmed finalInv
    (fun p => post p.1 ∧ finalInv p.2) W _ _ hW hrepaired hprogrammed hfinalStore hprogramCall hreturn
  have hrepairThen := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw)
    (.call (.ret repair) repairArgs) finish committed signatureOK finalInv
    (fun p => post p.1 ∧ finalInv p.2) W _ _ hW hcommitted hsignature hfinalStore hrepairCall hfinish
  have hcommitThen := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw)
    (.call (.ret simulatedCommit) commitArgs) repairThen sampled pointOK finalInv
    (fun p => post p.1 ∧ finalInv p.2) W _ _ hW hsampled (fun _ hp => hp.trans hw) hfinalStore hcommitCall hrepairThen
  have hqueryFirst := Language.query_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) .field .unit
    pre (fun _ => True) inv (fun p => scalarOK p.1 ∧ firstInv p.2) W fee firstTime hW hinput hstore
    (fun _ _ => ⟨True.intro, hu.trans hw⟩)
    (fun env hi => (dataLaws.unit (rep.env Input) env).trans (mono (by have h := hinput env hi; omega)))
    (fun input hi => hdFirst input hi.2)
  have hquerySecond := Language.query_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) .field .unit
    firstPre (fun _ => True) firstInv (fun p => scalarOK p.1 ∧ secondInv p.2) W fee secondTime hW hfirst hfirstStore
    (fun _ _ => ⟨True.intro, hu.trans hw⟩)
    (fun env hi => (dataLaws.unit (rep.env (scalar :: Input)) env).trans (mono (by have h := hfirst env hi; omega)))
    (fun input hi => hdSecond input hi.2)
  have hqueryThird := Language.query_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) .nonzero .unit
    secondPre (fun _ => True) secondInv (fun p => scalarOK p.1 ∧ finalInv p.2) W fee thirdTime hW hsecond hsecondStore
    (fun _ _ => ⟨True.intro, hu.trans hw⟩)
    (fun env hi => (dataLaws.unit (rep.env (scalar :: scalar :: Input)) env).trans (mono (by have h := hsecond env hi; omega)))
    (fun input hi => hdThird input hi.2)
  have hthird := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) (.query .nonzero .unit)
    commitThen secondPre scalarOK secondInv finalInv (fun p => post p.1 ∧ finalInv p.2)
    W _ _ hW hsecond (fun _ hp => hp.trans hw) hsecondStore hfinalStore hqueryThird hcommitThen
  have hsecondBound := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) (.query .field .unit)
    nonzeroThen firstPre scalarOK firstInv secondInv (fun p => post p.1 ∧ finalInv p.2)
    W _ _ hW hfirst (fun _ hp => hp.trans hw) hfirstStore hsecondStore hquerySecond hthird
  have hall := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store fieldDraw nonzeroDraw) (.query .field .unit)
    secondThen pre scalarOK inv firstInv (fun p => post p.1 ∧ finalInv p.2)
    W _ _ hW hinput (fun _ hp => hp.trans hw) hstore hfirstStore hqueryFirst hsecondBound
  intro input hi out hout
  rw [code, body_eq] at hout
  obtain ⟨ho, ht⟩ := hall input hi out hout
  refine ⟨ho, ?_⟩
  change out.steps ≤ firstTime + secondTime + thirdTime + 3 * scaleTime + subTime + zeroTime + pointTime + addTime +
    programTime + 2048 * fee
  dsimp only [repairTime] at ht
  omega

omit sizes lists laws dataLaws mono routing in
theorem signingTime_polynomial (overhead : Nat → Nat → Nat)
    (width cap messageTime pointTime scaleTime subTime zeroTime addTime firstTime secondTime thirdTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) (hMessage : PolynomiallyBounded messageTime)
    (hPoint : PolynomiallyBounded pointTime) (hScale : PolynomiallyBounded scaleTime)
    (hSub : PolynomiallyBounded subTime) (hZero : PolynomiallyBounded zeroTime)
    (hAdd : PolynomiallyBounded addTime) (hFirst : PolynomiallyBounded firstTime)
    (hSecond : PolynomiallyBounded secondTime) (hThird : PolynomiallyBounded thirdTime) :
    PolynomiallyBounded (fun n => signingTime (overhead n) (width n) (cap n) (messageTime n)
      (pointTime n) (scaleTime n) (subTime n) (zeroTime n) (addTime n) (firstTime n) (secondTime n) (thirdTime n)) := by
  unfold signingTime programmingTime scanTime scanComparisonTime scanFrameWidth
    CacheProgramming.frameWidth signingFrameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.NonzeroSigning.Native
