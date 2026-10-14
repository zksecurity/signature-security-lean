import Signatures.Runtime.BackendCoronReplySize

/-! Complete native budgets for Coron's hash/sign replies. Argument code,
default initialization, both caches, store read/write, group arithmetic, retained
environments, and entry/control machinery are included. `BackendCoronFinishBudget`
separately certifies extraction; complete solver assembly remains open. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Coron.ReplyCompiler

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

def cacheWork (overhead : Nat → Nat) (width cap comparisonTime sampleTime : Nat) : Nat :=
  cap * (comparisonTime + 257 * overhead (32 * replyFrameWidth width cap)) + sampleTime +
    133 * overhead (32 * replyFrameWidth width cap)

include localLaws dataLaws sizes lists mono routing

theorem cacheCall_bound (qS : Nat) {Γ val} (draw : Machine.Effect (machineStore qS) .unit val)
    (args : Args CryptoOp Γ [message, val, .list (.pair message val)])
    (pre : Env (cryptoBase F G₁ G₂ M M) Γ → Prop)
    (drawCode : Code Q unifSpec iface rep.data.unit (rep.ty val))
    (heffect : MachineCompiler.effects rep data samplingCode (machineStore qS) draw =
      .first (rep.ty (machineStore qS)) drawCode)
    (width cap comparisonTime sampleTime argumentTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : ∀ env, pre env → Q.size (rep.env Γ) env ≤ replyFrameWidth width cap)
    (ha : ∀ env, pre env → CacheCompiler.Input (Q := Q) rep (key := message) (val := val) width cap
      (args.denote (arithmetic F G₁ G₂ M M cost) env))
    (ht : ∀ env, pre env → Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive args) env ≤ argumentTime)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : Bounds control queryCost drawCode (fun _ => True)
      (fun v => Q.size (rep.ty val) v ≤ width) sampleTime) :
    Bounds control queryCost (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS)
      (.call (cacheGet CryptoOp.messageEq draw) args))
      (fun p => pre p.1 ∧ StoreReady (Q := Q) rep qS width cap p.2)
      (fun p => CacheCompiler.Output (Q := Q) rep (key := message) (val := val) width (cap + 1) p.1 ∧
        StoreReady (Q := Q) rep qS width cap p.2)
      (argumentTime + cacheWork overhead width cap comparisonTime sampleTime +
        3 * overhead (32 * replyFrameWidth width cap)) := by
  have hw : width ≤ replyFrameWidth width cap := by dsimp [replyFrameWidth]; nlinarith
  refine Language.call_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
    (MachineCompiler.effects rep data samplingCode (machineStore qS)) (cacheGet CryptoOp.messageEq draw)
    args pre (CacheCompiler.Input (Q := Q) rep (key := message) (val := val) width cap)
    (StoreReady (Q := Q) rep qS width cap) _ (replyFrameWidth width cap) argumentTime
    (cacheWork overhead width cap comparisonTime sampleTime) (hh.trans hw) hi
    (fun _ hs => hs.1.trans hw) ?_ ht ?_
  · intro env hp
    refine ⟨ha env hp, ?_⟩
    have h := CacheCompiler.input_size rep sizes lists width cap hh hu _ (ha env hp)
    dsimp [replyFrameWidth]
    nlinarith
  · intro input hp z hz
    obtain ⟨hout, hs, ht'⟩ := CacheCompiler.cacheGet_sampling_bound (key := message) (val := val)
      rep data (arithmetic F G₁ G₂ M M cost) primitive sizes lists localLaws dataLaws primitiveBound mono
      control queryCost routing (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS)) CryptoOp.messageEq draw
      (fun _ _ => rfl) drawCode heffect width cap comparisonTime sampleTime hh hu hb he hd input.1 hp.1
      input.2 hp.2.1 z hz
    refine ⟨⟨hout, by simpa only [hs] using hp.2⟩, ht'.trans ?_⟩
    have hc : overhead (32 * CacheCompiler.frameWidth width cap) ≤ overhead (32 * replyFrameWidth width cap) := by
      apply mono
      dsimp [CacheCompiler.frameWidth, replyFrameWidth]
      nlinarith
    dsimp only [cacheWork]
    gcongr

theorem scalarCall_bound (qS width cap comparisonTime sampleTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : ∀ z ∈ support (samplingCode.scalar.run control queryCost ()), z.steps ≤ sampleTime) :
    Bounds control queryCost (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS)
      (.call (cacheGet CryptoOp.messageEq .scalar) (scalarArgs qS)))
      (fun p => ReadPre (Q := Q) rep qS width cap p.1 ∧ StoreReady (Q := Q) rep qS width cap p.2)
      (fun p => CacheCompiler.Output (Q := Q) rep (key := message) (val := scalar) width (cap + 1) p.1 ∧
        StoreReady (Q := Q) rep qS width cap p.2)
      (zeroTime + 32 * overhead (32 * replyFrameWidth width cap) +
        cacheWork overhead width cap comparisonTime sampleTime + 3 * overhead (32 * replyFrameWidth width cap)) := by
  have hw : width ≤ replyFrameWidth width cap := by dsimp [replyFrameWidth]; nlinarith
  have hi : ∀ env, ReadPre (Q := Q) rep qS width cap env → Q.size (rep.env (ReadEnv qS)) env ≤ replyFrameWidth width cap := by
    intro env hp
    have h := readPre_size rep sizes qS width cap hh hu env hp
    dsimp [replyFrameWidth]
    nlinarith
  refine cacheCall_bound rep data samplingCode cost primitive localLaws dataLaws primitiveBound sizes lists mono
    control queryCost routing qS .scalar (scalarArgs qS) (ReadPre (Q := Q) rep qS width cap)
    samplingCode.scalar rfl width cap comparisonTime sampleTime _ hh hu hb hi ?_ ?_ he ?_
  · intro env hp
    rw [scalarArgs_denote]
    exact ⟨hp.2, hf 0, hp.1.2.1, hp.1.2.2.1⟩
  · intro env hp
    exact scalarArgs_cost rep data cost primitive localLaws dataLaws primitiveBound sizes mono qS env
      (replyFrameWidth width cap) zeroTime (hh.trans hw) (hu.trans hw) ((hf 0).trans hw) (hi env hp) hz
  · intro u _ z hz'
    cases u
    exact ⟨hf z.value, hd z hz'⟩

theorem coinCall_bound (qS width cap comparisonTime sampleTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ width)
    (hz : (primitiveBound (CryptoOp.finZero qS)).time () ≤ zeroTime)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : ∀ z ∈ support ((samplingCode.uniform qS).run control queryCost ()), z.steps ≤ sampleTime) :
    Bounds control queryCost (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS)
      (.call (cacheGet CryptoOp.messageEq (.uniform qS)) (coinArgs qS)))
      (fun p => ScalarPre (Q := Q) rep qS width cap p.1 ∧ StoreReady (Q := Q) rep qS width cap p.2)
      (fun p => CacheCompiler.Output (Q := Q) rep (key := message) (val := boundedNat qS) width (cap + 1) p.1 ∧
        StoreReady (Q := Q) rep qS width cap p.2)
      (zeroTime + 32 * overhead (32 * replyFrameWidth width cap) +
        cacheWork overhead width cap comparisonTime sampleTime + 3 * overhead (32 * replyFrameWidth width cap)) := by
  have hw : width ≤ replyFrameWidth width cap := by dsimp [replyFrameWidth]; nlinarith
  have hi : ∀ env, ScalarPre (Q := Q) rep qS width cap env → Q.size (rep.env (ScalarEnv qS)) env ≤ replyFrameWidth width cap := by
    intro env hp
    have h := scalarPre_size rep sizes lists qS width cap hh hu env hp
    dsimp [replyFrameWidth]
    nlinarith
  refine cacheCall_bound rep data samplingCode cost primitive localLaws dataLaws primitiveBound sizes lists mono
    control queryCost routing qS (.uniform qS) (coinArgs qS) (ScalarPre (Q := Q) rep qS width cap)
    (samplingCode.uniform qS) rfl width cap comparisonTime sampleTime _ hh hu hb hi ?_ ?_ he ?_
  · intro env hp
    rw [coinArgs_denote]
    exact ⟨hp.2.2, hf 0, hp.2.1.2.2.2.1, hp.2.1.2.2.2.2⟩
  · intro env hp
    exact coinArgs_cost rep data cost primitive localLaws dataLaws primitiveBound sizes mono qS env
      (replyFrameWidth width cap) zeroTime (hh.trans hw) (hu.trans hw) ((hf 0).trans hw) (hi env hp) hz
  · intro u _ z hz'
    cases u
    exact ⟨hf z.value, hd z hz'⟩


theorem signResult_bound (qS width cap opTime : Nat)
    (inv : (machineStore qS).Value (cryptoBase F G₁ G₂ M M) → Prop)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hn : ∀ n ≤ qS, Q.size rep.data.nat n ≤ width)
    (hs : ∀ saved, inv saved → Q.size (rep.ty (machineStore qS)) saved ≤ replyFrameWidth width cap)
    (hconvert : ∀ n : Fin (qS + 1), (primitiveBound (CryptoOp.finVal qS)).time n ≤ opTime)
    (heq : ∀ n ≤ qS, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ opTime)
    (hzero : (primitiveBound CryptoOp.zero₁).time () ≤ opTime)
    (hscale : ∀ rho : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ opTime)
    :
    Bounds control queryCost (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS)
      (.call (.ret signReply) (signArgs qS)))
      (fun p => WrittenPre (Q := Q) rep qS width cap p.1 ∧ inv p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ inv p.2)
      (5 * opTime + 165 * overhead (32 * replyFrameWidth width cap)) := by
  let W := replyFrameWidth width cap
  let fee := overhead (32 * W)
  let mathTime := 4 * opTime + 96 * fee
  let argPre := fun env : Env (cryptoBase F G₁ G₂ M M) [scalar, point₁, .nat] => env.2.2.1 ≤ qS
  have hw : width ≤ W := by dsimp [W, replyFrameWidth]; nlinarith
  have hmono : overhead (128 * width) ≤ fee := by
    apply mono
    dsimp [W, replyFrameWidth]
    nlinarith
  have hargSize : ∀ env, argPre env → Q.size (rep.env [scalar, point₁, .nat]) env ≤ W := by
    intro env hp
    obtain ⟨rho, X, coin, u⟩ := env
    cases u
    have hnat := hn coin hp
    have hprod := @sizes.prod_le
    have hsmall : Q.size (rep.env [scalar, point₁, .nat]) (rho, X, coin, ()) ≤ 9 * width := by
      dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
      grind only
    exact hsmall.trans (by dsimp [W, replyFrameWidth]; nlinarith)
  have henvSize : ∀ env, WrittenPre (Q := Q) rep qS width cap env →
      Q.size (rep.env (WrittenEnv qS)) env ≤ W := by
    intro env hp
    have h := writtenPre_size rep sizes lists qS width cap hh hu env hp
    dsimp [W, replyFrameWidth]
    nlinarith
  have hret : Bounds control queryCost
      (Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
        (MachineCompiler.effects rep data samplingCode (machineStore qS)) (.ret signReply))
      (fun p => argPre p.1 ∧ inv p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ inv p.2) (mathTime + 2 * fee) := by
    refine Language.ret_bound_of_width mono control queryCost routing rep data
      (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS)) signReply argPre
      (fun g => Q.size (rep.ty point₁) g ≤ width) inv W mathTime hargSize hs
      (fun env _ => ⟨hg _, (hg _).trans hw⟩) ?_
    intro env hp
    obtain ⟨rho, X, coin, u⟩ := env
    cases u
    have h := signReply_cost rep data cost primitive localLaws dataLaws primitiveBound sizes mono rho X coin width opTime opTime opTime hh hu hb (hn coin hp) (hn 0 (Nat.zero_le _)) (hf rho) hg (heq coin hp) hzero (hscale rho X)
    dsimp only [mathTime]
    nlinarith
  have hcall := Language.call_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
    (MachineCompiler.effects rep data samplingCode (machineStore qS)) (.ret signReply) (signArgs qS)
    (WrittenPre (Q := Q) rep qS width cap) argPre inv
    (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ inv p.2) W (opTime + 64 * fee)
    (mathTime + 2 * fee) (hh.trans hw) henvSize hs
    (by
      intro env _
      rw [signArgs_denote]
      have hcoin : env.2.1.1.val ≤ qS := Nat.le_of_lt_succ env.2.1.1.isLt
      exact ⟨hcoin, hargSize _ hcoin⟩)
    (fun env hp => signArgs_cost rep data cost primitive localLaws dataLaws primitiveBound sizes mono qS env
      W opTime (hh.trans hw) (hu.trans hw) (fun n => (hn n.val (Nat.le_of_lt_succ n.isLt)).trans hw)
      (henvSize env hp) hconvert) hret
  intro input hp z hz
  obtain ⟨hout, ht⟩ := hcall input hp z hz
  exact ⟨hout, by dsimp only [mathTime, fee, W] at ht; omega⟩

theorem hashResult_bound (qS width cap opTime : Nat)
    (inv : (machineStore qS).Value (cryptoBase F G₁ G₂ M M) → Prop)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hn : ∀ n ≤ qS, Q.size rep.data.nat n ≤ width)
    (hs : ∀ saved, inv saved → Q.size (rep.ty (machineStore qS)) saved ≤ replyFrameWidth width cap)
    (hconvert : ∀ n : Fin (qS + 1), (primitiveBound (CryptoOp.finVal qS)).time n ≤ opTime)
    (heq : ∀ n ≤ qS, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ opTime)
    (hzero : (primitiveBound CryptoOp.zero₁).time () ≤ opTime)
    (hscale : ∀ rho : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ opTime)
    (hadd : ∀ g h : G₁, (primitiveBound CryptoOp.add₁).time (g, h) ≤ opTime)
    :
    Bounds control queryCost (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS)
      (.call (.ret hashReply) (hashArgs qS)))
      (fun p => WrittenPre (Q := Q) rep qS width cap p.1 ∧ inv p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ inv p.2)
      (5 * opTime + 165 * overhead (32 * replyFrameWidth width cap)) := by
  let W := replyFrameWidth width cap
  let fee := overhead (32 * W)
  let mathTime := 4 * opTime + 96 * fee
  let argPre := fun env : Env (cryptoBase F G₁ G₂ M M) [scalar, point₁, point₁, .nat] => env.2.2.2.1 ≤ qS
  have hw : width ≤ W := by dsimp [W, replyFrameWidth]; nlinarith
  have hmono : overhead (128 * width) ≤ fee := by
    apply mono
    dsimp [W, replyFrameWidth]
    nlinarith
  have hargSize : ∀ env, argPre env → Q.size (rep.env [scalar, point₁, point₁, .nat]) env ≤ W := by
    intro env hp
    obtain ⟨rho, g, h, coin, u⟩ := env
    cases u
    have hnat := hn coin hp
    have hprod := @sizes.prod_le
    have hsmall : Q.size (rep.env [scalar, point₁, point₁, .nat]) (rho, g, h, coin, ()) ≤ 9 * width := by
      dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
      grind only
    exact hsmall.trans (by dsimp [W, replyFrameWidth]; nlinarith)
  have henvSize : ∀ env, WrittenPre (Q := Q) rep qS width cap env →
      Q.size (rep.env (WrittenEnv qS)) env ≤ W := by
    intro env hp
    have h := writtenPre_size rep sizes lists qS width cap hh hu env hp
    dsimp [W, replyFrameWidth]
    nlinarith
  have hret : Bounds control queryCost
      (Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
        (MachineCompiler.effects rep data samplingCode (machineStore qS)) (.ret hashReply))
      (fun p => argPre p.1 ∧ inv p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ inv p.2) (mathTime + 2 * fee) := by
    refine Language.ret_bound_of_width mono control queryCost routing rep data
      (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS)) hashReply argPre
      (fun g => Q.size (rep.ty point₁) g ≤ width) inv W mathTime hargSize hs
      (fun env _ => ⟨hg _, (hg _).trans hw⟩) ?_
    intro env hp
    obtain ⟨rho, g, h, coin, u⟩ := env
    cases u
    have h := hashReply_cost rep data cost primitive localLaws dataLaws primitiveBound sizes mono rho g h coin width opTime opTime opTime opTime hh hu hb (hn coin hp) (hn 0 (Nat.zero_le _)) (hf rho) hg (heq coin hp) hzero (hscale rho g) (fun y => hadd (rho • g) y)
    dsimp only [mathTime]
    nlinarith
  have hcall := Language.call_bound_of_width sizes mono control queryCost routing rep data
    (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
    (MachineCompiler.effects rep data samplingCode (machineStore qS)) (.ret hashReply) (hashArgs qS)
    (WrittenPre (Q := Q) rep qS width cap) argPre inv
    (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ inv p.2) W (opTime + 64 * fee)
    (mathTime + 2 * fee) (hh.trans hw) henvSize hs
    (by
      intro env _
      rw [hashArgs_denote]
      have hcoin : env.2.1.1.val ≤ qS := Nat.le_of_lt_succ env.2.1.1.isLt
      exact ⟨hcoin, hargSize _ hcoin⟩)
    (fun env hp => hashArgs_cost rep data cost primitive localLaws dataLaws primitiveBound sizes mono qS env
      W opTime (hh.trans hw) (hu.trans hw) (fun n => (hn n.val (Nat.le_of_lt_succ n.isLt)).trans hw)
      (henvSize env hp) hconvert) hret
  intro input hp z hz
  obtain ⟨hout, ht⟩ := hcall input hp z hz
  exact ⟨hout, by dsimp only [mathTime, fee, W] at ht; omega⟩

set_option maxHeartbeats 800000 in
/-- Complete native hash/sign reply. Every assumption prices an individual
primitive or bounds a representation; the handler budget itself is derived from
the compiled program. The source-semantic invariant gives a sharper persistent
store bound after this routine when it is composed across queries. -/
theorem backendReply_bound (qS : Nat) (signing : Bool)
    (width cap comparisonTime scalarTime coinTime opTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hn : ∀ n ≤ qS, Q.size rep.data.nat n ≤ width)
    (hmessage : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hfieldZero : (primitiveBound CryptoOp.zero).time () ≤ opTime)
    (hcoinZero : (primitiveBound (CryptoOp.finZero qS)).time () ≤ opTime)
    (hconvert : ∀ n : Fin (qS + 1), (primitiveBound (CryptoOp.finVal qS)).time n ≤ opTime)
    (heq : ∀ n ≤ qS, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ opTime)
    (hzero : (primitiveBound CryptoOp.zero₁).time () ≤ opTime)
    (hscale : ∀ rho : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ opTime)
    (hadd : ∀ g h : G₁, (primitiveBound CryptoOp.add₁).time (g, h) ≤ opTime)
    (hscalarDraw : ∀ z ∈ support (samplingCode.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hcoinDraw : ∀ z ∈ support ((samplingCode.uniform qS).run control queryCost ()), z.steps ≤ coinTime) :
    Bounds control queryCost (backendReply rep data samplingCode cost primitive qS signing)
      (fun p => Q.size (rep.ty message) p.1 ≤ width ∧ StoreReady (Q := Q) rep qS width cap p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧
        Q.size (rep.ty (machineStore qS)) p.2 ≤ writtenStoreWidth width cap)
      (2 * (cap * (comparisonTime + 257 * overhead (32 * replyFrameWidth width cap))) +
        scalarTime + coinTime + 7 * opTime + 700 * overhead (32 * replyFrameWidth width cap)) := by
  let W := replyFrameWidth width cap
  let fee := overhead (32 * W)
  let inv := StoreReady (Q := Q) rep qS width cap
  let after := fun s => Q.size (rep.ty (machineStore qS)) s ≤ writtenStoreWidth width cap
  let post := fun p : G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    Q.size (rep.ty point₁) p.1 ≤ width ∧ after p.2
  let pre := fun env : Env (cryptoBase F G₁ G₂ M M) [message] => Q.size (rep.ty message) env.1 ≤ width
  let resultProg : Program CryptoOp (Machine.Effect (machineStore qS)) (WrittenEnv qS) point₁ :=
    if signing then .call (.ret signReply) (signArgs qS) else .call (.ret hashReply) (hashArgs qS)
  let writeProg := Program.bind (.query Machine.Effect.write (writeState qS signing)) resultProg
  let coinProg := Program.bind (.call (cacheGet CryptoOp.messageEq (.uniform qS)) (coinArgs qS)) writeProg
  let scalarProg := Program.bind (.call (cacheGet CryptoOp.messageEq .scalar) (scalarArgs qS)) coinProg
  let readTime := fee + 4 * fee + 3 * fee
  let writeTime := 64 * fee + 4 * fee + 3 * fee
  let resultTime := 5 * opTime + 165 * fee
  let scalarCallTime := opTime + 32 * fee + cacheWork overhead width cap comparisonTime scalarTime + 3 * fee
  let coinCallTime := opTime + 32 * fee + cacheWork overhead width cap comparisonTime coinTime + 3 * fee
  let writeBindTime := writeTime + resultTime + 20 * fee
  let coinBindTime := coinCallTime + writeBindTime + 20 * fee
  let scalarBindTime := scalarCallTime + coinBindTime + 20 * fee
  let bodyTime := readTime + scalarBindTime + 20 * fee
  have hw : width ≤ W := by dsimp [W, replyFrameWidth]; nlinarith
  have hW := hh.trans hw
  have hafterW : writtenStoreWidth width cap ≤ W := by dsimp [writtenStoreWidth, W, replyFrameWidth]; nlinarith
  have hsInv : ∀ saved, inv saved → Q.size (rep.ty (machineStore qS)) saved ≤ W :=
    fun _ hs => hs.1.trans hw
  have hsAfter : ∀ saved, after saved → Q.size (rep.ty (machineStore qS)) saved ≤ W :=
    fun _ hs => hs.trans hafterW
  have hstart : ∀ env, pre env → Q.size (rep.env [message]) env ≤ W := by
    intro env hp
    have ht : env.2 = () := rfl
    have hprod := sizes.prod_le (rep.ty message) rep.data.unit env
    dsimp only [pre] at hp
    have he : Q.size (rep.env [message]) env ≤ 3 * width := by
      dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty]
      grind only
    exact he.trans (by dsimp [W, replyFrameWidth]; nlinarith)
  have hreadSize : ∀ env, ReadPre (Q := Q) rep qS width cap env → Q.size (rep.env (ReadEnv qS)) env ≤ W := by
    intro env hp
    have h := readPre_size rep sizes qS width cap hh hu env hp
    dsimp [W, replyFrameWidth]
    nlinarith
  have hscalarSize : ∀ env, ScalarPre (Q := Q) rep qS width cap env → Q.size (rep.env (ScalarEnv qS)) env ≤ W := by
    intro env hp
    have h := scalarPre_size rep sizes lists qS width cap hh hu env hp
    dsimp [W, replyFrameWidth]
    nlinarith
  have hbothSize : ∀ env, BothPre (Q := Q) rep qS width cap env → Q.size (rep.env (BothEnv qS)) env ≤ W := by
    intro env hp
    have h := bothPre_size rep sizes lists qS width cap hh hu env hp
    dsimp [W, replyFrameWidth]
    nlinarith
  have hcached {val : Ty CryptoAtom} (value : val.Value (cryptoBase F G₁ G₂ M M) × List (M × val.Value (cryptoBase F G₁ G₂ M M)))
      (hp : CacheCompiler.Output (Q := Q) rep (key := message) (val := val) width (cap + 1) value) :
      Q.size (rep.ty (.pair val (.list (.pair message val)))) value ≤ W := by
    have h := CacheCompiler.output_size (key := message) (val := val) rep sizes lists width (cap + 1) hh value hp
    dsimp [W, replyFrameWidth]
    nlinarith
  have hresult : Bounds control queryCost
      (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS) resultProg)
      (fun p => WrittenPre (Q := Q) rep qS width cap p.1 ∧ after p.2) post resultTime := by
    cases signing
    · exact hashResult_bound rep data samplingCode cost primitive localLaws dataLaws primitiveBound sizes lists mono
        control queryCost routing qS width cap opTime after hh hu hb hf hg hn hsAfter hconvert heq hzero hscale hadd
    · exact signResult_bound rep data samplingCode cost primitive localLaws dataLaws primitiveBound sizes lists mono
        control queryCost routing qS width cap opTime after hh hu hb hf hg hn hsAfter hconvert heq hzero hscale
  have hwrite : Bounds control queryCost
      (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS) (.query .write (writeState qS signing)))
      (fun p => BothPre (Q := Q) rep qS width cap p.1 ∧ inv p.2)
      (fun p => True ∧ after p.2) writeTime := by
    refine Language.query_bound_of_width sizes mono control queryCost routing rep data
      (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS)) .write (writeState qS signing)
      (BothPre (Q := Q) rep qS width cap) after inv _ W (64 * fee) (4 * fee) hW hbothSize hsInv ?_ ?_ ?_
    · intro env hp
      have h := writeState_size rep sizes lists cost qS width cap signing hh env hp
      exact ⟨h, h.trans hafterW⟩
    · intro env hp
      exact writeState_cost rep data cost primitive localLaws dataLaws primitiveBound sizes lists mono qS signing env
        W hW (hbothSize env hp)
    · intro input hp z hz
      have h := MachineCompiler.write_bound rep data samplingCode sizes localLaws dataLaws mono control queryCost routing
        (machineStore qS) inv after W hW (hu.trans hw) hsInv hsAfter input hp z hz
      exact ⟨⟨True.intro, h.1.2⟩, h.2⟩
  have hwriteBind := Language.bind_bound_of_width_transition sizes localLaws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
    (MachineCompiler.effects rep data samplingCode (machineStore qS))
    (.query .write (writeState qS signing)) resultProg (BothPre (Q := Q) rep qS width cap) (fun _ => True)
    inv after post W writeTime resultTime hW hbothSize
    (by intro u _; cases u; exact hu.trans hw) hsInv hsAfter hwrite hresult
  have hcoin := coinCall_bound rep data samplingCode cost primitive localLaws dataLaws primitiveBound sizes lists mono
    control queryCost routing qS width cap comparisonTime coinTime opTime hh hu hb hc hcoinZero hmessage hcoinDraw
  have hcoinBind := Language.bind_bound_of_width sizes localLaws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
    (MachineCompiler.effects rep data samplingCode (machineStore qS))
    (.call (cacheGet CryptoOp.messageEq (.uniform qS)) (coinArgs qS)) writeProg
    (ScalarPre (Q := Q) rep qS width cap)
    (CacheCompiler.Output (Q := Q) rep (key := message) (val := boundedNat qS) width (cap + 1))
    inv post W coinCallTime writeBindTime hW hscalarSize (fun p hp => hcached (val := boundedNat qS) p hp) hsInv hcoin hwriteBind
  have hscalar := scalarCall_bound rep data samplingCode cost primitive localLaws dataLaws primitiveBound sizes lists mono
    control queryCost routing qS width cap comparisonTime scalarTime opTime hh hu hb hf hfieldZero hmessage hscalarDraw
  have hscalarBind := Language.bind_bound_of_width sizes localLaws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
    (MachineCompiler.effects rep data samplingCode (machineStore qS))
    (.call (cacheGet CryptoOp.messageEq .scalar) (scalarArgs qS)) coinProg
    (ReadPre (Q := Q) rep qS width cap)
    (CacheCompiler.Output (Q := Q) rep (key := message) (val := scalar) width (cap + 1))
    inv post W scalarCallTime coinBindTime hW hreadSize (fun p hp => hcached (val := scalar) p hp) hsInv hscalar hcoinBind
  have hread : Bounds control queryCost
      (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS) (.query .read (.unit : Expr CryptoOp [message] .unit)))
      (fun p => pre p.1 ∧ inv p.2) (fun p => inv p.1 ∧ inv p.2) readTime := by
    refine Language.query_bound_of_width sizes mono control queryCost routing rep data
      (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS)) .read .unit pre (fun _ => True) inv _ W
      fee (4 * fee) hW hstart hsInv (fun _ _ => ⟨True.intro, hu.trans hw⟩) ?_ ?_
    · intro env hp
      apply (dataLaws.unit (rep.env [message]) env).trans
      apply mono
      have he := hstart env hp
      omega
    · intro input hp z hz
      have h := MachineCompiler.read_bound rep data samplingCode sizes localLaws mono control queryCost routing
        (machineStore qS) inv W hW (hu.trans hw) hsInv input hp.2 z hz
      exact ⟨⟨by simpa only [h.1.1] using h.1.2, h.1.2⟩, h.2⟩
  have hbody := Language.bind_bound_of_width sizes localLaws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
    (MachineCompiler.effects rep data samplingCode (machineStore qS))
    (.query .read .unit) scalarProg pre inv inv post W readTime scalarBindTime hW hstart hsInv hsInv hread hscalarBind
  have hsyntax : Program.bind (.query Machine.Effect.read (.unit : Expr CryptoOp [message] .unit)) scalarProg =
      body qS signing := rfl
  rw [hsyntax] at hbody
  have hunary := MachineCompiler.unary_bound rep data samplingCode sizes localLaws dataLaws mono control queryCost routing
    cost primitive (machineStore qS) (body qS signing) (fun m => Q.size (rep.ty message) m ≤ width) inv post W bodyTime
    hW (hu.trans hw) (fun _ hm => hm.trans hw) hsInv hbody
  have hcode : backendReply rep data samplingCode cost primitive qS signing =
      MachineCompiler.unary rep data samplingCode cost primitive (machineStore qS) (body qS signing) := by
    unfold backendReply
    exact congrArg (MachineCompiler.unary rep data samplingCode cost primitive (machineStore qS))
      (machineReply_eq qS signing)
  have hbound : Bounds control queryCost (backendReply rep data samplingCode cost primitive qS signing)
      (fun p => Q.size (rep.ty message) p.1 ≤ width ∧ inv p.2) post (bodyTime + 7 * fee) :=
    Eq.mpr (congrArg (fun code : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.ty message) (rep.ty (machineStore qS)))
      (StepClass.HasProd.prod (rep.ty point₁) (rep.ty (machineStore qS))) =>
        Bounds control queryCost code (fun p => Q.size (rep.ty message) p.1 ≤ width ∧ inv p.2)
          post (bodyTime + 7 * fee)) hcode) hunary
  intro input hp z hz
  obtain ⟨hout, ht⟩ := hbound input hp z hz
  refine ⟨hout, ?_⟩
  dsimp only [bodyTime, readTime, scalarBindTime, scalarCallTime, coinBindTime, coinCallTime,
    writeBindTime, writeTime, resultTime, cacheWork, fee, W] at ht
  omega

end Signatures.Runtime.Coron.ReplyCompiler
