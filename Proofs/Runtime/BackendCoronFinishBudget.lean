import Proofs.Runtime.BackendCoronFinishSize

/-! Complete native final-extraction budget: lazy final hashing, store read,
the encountered scalar-cache scan, group extraction, and every retained frame
and control adapter. Only individual primitive/sampling contracts are assumed. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Coron.FinishCompiler

open BackendProgram

def nativeFinishTime (overhead : Nat → Nat)
    (width cap comparisonTime scalarTime coinTime opTime : Nat) : Nat :=
  (3 * cap + 1) * (comparisonTime + 257 * overhead (32 * finishFrameWidth width cap)) +
    scalarTime + coinTime + 10 * opTime + 1000 * overhead (32 * finishFrameWidth width cap)

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

include localLaws dataLaws sizes lists mono routing

set_option maxHeartbeats 800000 in
theorem backendFinish_bound (qS width cap comparisonTime scalarTime coinTime opTime : Nat)
    (hh : header ≤ width)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime) :
    Bounds control queryCost (backendFinish rep data samplingCode cost primitive qS)
      (fun p => Q.size (rep.ty message) p.1.1 ≤ width ∧
        ReplyCompiler.StateInvariant (Q := Q) rep qS width width cap p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧
        ReplyCompiler.StateInvariant (Q := Q) rep qS width (ReplyCompiler.writtenStoreWidth width cap) (cap + 1) p.2)
      (nativeFinishTime overhead width cap comparisonTime scalarTime coinTime opTime) := by
  let B := ReplyCompiler.writtenStoreWidth width cap
  let W := finishFrameWidth width cap
  let fee := overhead (32 * W)
  let inv := ReplyCompiler.StateInvariant (Q := Q) rep qS width width cap
  let after := ReplyCompiler.StateInvariant (Q := Q) rep qS width B (cap + 1)
  let post := fun p : G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    Q.size (rep.ty point₁) p.1 ≤ width ∧ after p.2
  let startPre := StartPre (Q := Q) rep width
  let hashPre := HashPre (Q := Q) rep width
  let readPre := ReadPre (Q := Q) rep qS width B (cap + 1)
  let lookupPre := LookupPre (Q := Q) rep qS width B (cap + 1)
  let lookupInput := CacheCompiler.Input (Q := Q) rep (key := message) (val := scalar) width (cap + 1)
  let extractProg : Program CryptoOp (Machine.Effect (machineStore qS)) (LookupEnv qS) point₁ :=
    .call (.ret extract) (extractArgs qS)
  let lookupProg := Program.bind (.call (.ret (lookup (val := scalar) CryptoOp.messageEq)) (lookupArgs qS)) extractProg
  let readProg := Program.bind (.query Machine.Effect.read (.unit : Expr CryptoOp HashEnv .unit)) lookupProg
  let scanTime := (cap + 1) * (comparisonTime + 257 * fee)
  let extractTime := 64 * fee + (opTime + opTime + 32 * fee + 2 * fee) + 3 * fee
  let lookupTime := opTime + 32 * fee + (scanTime + 32 * fee + 2 * fee) + 3 * fee
  let readTime := fee + 4 * fee + 3 * fee
  let hashTime := 16 * fee + nativeReplyTime overhead width cap comparisonTime scalarTime coinTime opTime + 3 * fee
  let lookupBindTime := lookupTime + extractTime + 20 * fee
  let readBindTime := readTime + lookupBindTime + 20 * fee
  let bodyTime := hashTime + readBindTime + 20 * fee
  have hwB : width ≤ B := by dsimp [B, ReplyCompiler.writtenStoreWidth]; nlinarith
  have hBW : B ≤ W := by dsimp [B, W, finishFrameWidth]; omega
  have hw := hwB.trans hBW
  have hW := hh.trans hw
  have hsInv : ∀ saved, inv saved → Q.size (rep.ty (machineStore qS)) saved ≤ W := fun _ hi => hi.1.trans hw
  have hsAfter : ∀ saved, after saved → Q.size (rep.ty (machineStore qS)) saved ≤ W := fun _ hi => hi.1.trans hBW
  have hstart : ∀ env, startPre env → Q.size (rep.env StartEnv) env ≤ W := by
    intro env hi
    have h := startPre_size rep sizes qS width hh values env hi
    dsimp [W, finishFrameWidth, ReplyCompiler.writtenStoreWidth]
    nlinarith
  have hhashSize : ∀ env, hashPre env → Q.size (rep.env HashEnv) env ≤ W := by
    intro env hi
    have h := hashPre_size rep sizes qS width hh values env hi
    dsimp [W, finishFrameWidth, ReplyCompiler.writtenStoreWidth]
    nlinarith
  have hreadSize : ∀ env, readPre env → Q.size (rep.env (ReadEnv qS)) env ≤ W := by
    intro env hi
    have h := readPre_size rep sizes qS width B (cap + 1) hh values env hi
    dsimp [B, W, finishFrameWidth, ReplyCompiler.writtenStoreWidth] at *
    nlinarith
  have hlookupSize : ∀ env, lookupPre env → Q.size (rep.env (LookupEnv qS)) env ≤ W := by
    intro env hi
    have h := lookupPre_size rep sizes qS width B (cap + 1) hh values env hi
    dsimp [B, W, finishFrameWidth, ReplyCompiler.writtenStoreWidth] at *
    nlinarith
  have hlookupInputSize : ∀ env, lookupInput env →
      Q.size (rep.env [message, scalar, .list (.pair message scalar)]) env ≤ W := by
    intro env hi
    have h := CacheCompiler.input_size (key := message) (val := scalar) rep sizes lists
      width (cap + 1) hh values.unit env hi
    dsimp [W, finishFrameWidth, ReplyCompiler.writtenStoreWidth]
    nlinarith
  have hlookupResult : ∀ value : Bool × F, Q.size (rep.ty LookupResult) value ≤ W := by
    intro value
    have h := lookupResult_size rep sizes value qS width hh values
    dsimp [W, finishFrameWidth, ReplyCompiler.writtenStoreWidth]
    nlinarith
  have hextractInput : ∀ env : Env (cryptoBase F G₁ G₂ M M) [point₁, scalar, point₁],
      Q.size (rep.env [point₁, scalar, point₁]) env ≤ W := by
    intro env
    have hg := values.point
    have hf := values.scalar
    have hu := values.unit
    have he : env.2.2.2 = () := rfl
    have hprod := @sizes.prod_le
    have h : Q.size (rep.env [point₁, scalar, point₁]) env ≤ 7 * width := by
      dsimp only [LanguageRepresentation.env] at *
      grind only
    dsimp [W, finishFrameWidth, ReplyCompiler.writtenStoreWidth]
    nlinarith
  have hsmallFee : overhead (128 * width) ≤ fee := by
    apply mono
    dsimp [W, finishFrameWidth, ReplyCompiler.writtenStoreWidth]
    nlinarith
  have hscanFee : overhead (128 * ((4 * (cap + 1) + 1) * width)) ≤ fee := by
    apply mono
    dsimp [W, finishFrameWidth, ReplyCompiler.writtenStoreWidth]
    nlinarith
  have hextractRet : Bounds control queryCost
      (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS) (.ret extract))
      (fun p => True ∧ after p.2) post (opTime + opTime + 32 * fee + 2 * fee) := by
    refine Language.ret_bound_of_width mono control queryCost routing rep data
      (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS)) extract (fun _ => True)
      (fun g => Q.size (rep.ty point₁) g ≤ width) after W (opTime + opTime + 32 * fee)
      (fun env _ => hextractInput env) hsAfter (fun env _ => ⟨values.point _, (values.point _).trans hw⟩) ?_
    intro env _
    obtain ⟨sigma, rho, X, u⟩ := env
    cases u
    have h := extract_cost rep data cost primitive localLaws dataLaws primitiveBound sizes mono
      rho sigma X width opTime opTime hh values.unit (values.scalar rho) values.point (ops.scale rho X) (ops.sub sigma (rho • X))
    exact h.trans (by gcongr)
  have hextract : Bounds control queryCost
      (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS) extractProg)
      (fun p => lookupPre p.1 ∧ after p.2) post extractTime := by
    refine Language.call_bound_of_width sizes mono control queryCost routing rep data
      (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS)) (.ret extract) (extractArgs qS)
      lookupPre (fun _ => True) after post W (64 * fee) (opTime + opTime + 32 * fee + 2 * fee)
      hW hlookupSize hsAfter (fun env _ => ⟨True.intro, hextractInput _⟩) ?_ hextractRet
    intro env hi
    exact extractArgs_cost rep data cost primitive localLaws dataLaws primitiveBound sizes mono qS env W
      hW (values.unit.trans hw) (hlookupSize env hi)
  have hlookupRet : Bounds control queryCost
      (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS)
        (.ret (lookup (val := scalar) CryptoOp.messageEq)))
      (fun p => lookupInput p.1 ∧ after p.2) (fun p => True ∧ after p.2)
      (scanTime + 32 * fee + 2 * fee) := by
    refine Language.ret_bound_of_width mono control queryCost routing rep data
      (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS)) (lookup (val := scalar) CryptoOp.messageEq)
      lookupInput (fun _ => True) after W (scanTime + 32 * fee) hlookupInputSize hsAfter
      (fun _ _ => ⟨True.intro, hlookupResult _⟩) ?_
    intro env hi
    obtain ⟨m, d, xs, u⟩ := env
    cases u
    have h := LookupCompiler.lookup_cost_bound (key := message) (val := scalar)
      rep data (arithmetic F G₁ G₂ M M cost) primitive localLaws dataLaws primitiveBound sizes mono lists
      CryptoOp.messageEq m d xs width comparisonTime (cap + 1) hh values.unit values.bool hi.1 hi.2.1
      hi.2.2.1 hi.2.2.2 (fun p hp => ops.message p.1 m (hi.2.2.1 p hp).1 hi.1)
    exact h.trans (by dsimp only [scanTime]; gcongr)
  have hlookup : Bounds control queryCost
      (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS)
        (.call (.ret (lookup (val := scalar) CryptoOp.messageEq)) (lookupArgs qS)))
      (fun p => readPre p.1 ∧ after p.2) (fun p => True ∧ after p.2) lookupTime := by
    refine Language.call_bound_of_width sizes mono control queryCost routing rep data
      (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS))
      (.ret (lookup (val := scalar) CryptoOp.messageEq)) (lookupArgs qS) readPre lookupInput after _
      W (opTime + 32 * fee) (scanTime + 32 * fee + 2 * fee) hW hreadSize hsAfter ?_ ?_ hlookupRet
    · intro env hi
      have ha : lookupInput ((lookupArgs qS).denote (arithmetic F G₁ G₂ M M cost) env) := by
        rw [lookupArgs_denote]
        exact ⟨hi.2.2, values.scalar 0, (fun p hp => ⟨hi.1.2.1.1 p hp, values.scalar p.2⟩),
          (Nat.le_max_left _ _).trans hi.1.2.2⟩
      exact ⟨ha, hlookupInputSize _ ha⟩
    · intro env hi
      exact lookupArgs_cost rep data cost primitive localLaws dataLaws primitiveBound sizes mono qS env W opTime
        hW (values.unit.trans hw) ((values.scalar 0).trans hw) (hreadSize env hi) ops.fieldZero
  have hlookupBind := Language.bind_bound_of_width sizes localLaws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
    (MachineCompiler.effects rep data samplingCode (machineStore qS))
    (.call (.ret (lookup (val := scalar) CryptoOp.messageEq)) (lookupArgs qS)) extractProg
    readPre (fun _ => True) after post W lookupTime extractTime hW hreadSize
    (fun value _ => hlookupResult value) hsAfter hlookup hextract
  have hread : Bounds control queryCost
      (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS)
        (.query .read (.unit : Expr CryptoOp HashEnv .unit)))
      (fun p => hashPre p.1 ∧ after p.2) (fun p => after p.1 ∧ after p.2) readTime := by
    refine Language.query_bound_of_width sizes mono control queryCost routing rep data
      (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS)) .read .unit hashPre (fun _ => True)
      after _ W fee (4 * fee) hW hhashSize hsAfter (fun _ _ => ⟨True.intro, values.unit.trans hw⟩) ?_ ?_
    · intro env hi
      apply (dataLaws.unit (rep.env HashEnv) env).trans
      apply mono
      have h := hhashSize env hi
      have hu := values.unit
      omega
    · intro input hi z hz
      have h := MachineCompiler.read_bound rep data samplingCode sizes localLaws mono control queryCost routing
        (machineStore qS) after W hW (values.unit.trans hw) hsAfter input hi.2 z hz
      exact ⟨⟨by simpa only [h.1.1] using h.1.2, h.1.2⟩, h.2⟩
  have hreadBind := Language.bind_bound_of_width sizes localLaws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
    (MachineCompiler.effects rep data samplingCode (machineStore qS)) (.query .read .unit) lookupProg
    hashPre after after post W readTime lookupBindTime hW hhashSize hsAfter hsAfter hread hlookupBind
  have hhash : Bounds control queryCost
      (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS) (.call (machineReply qS false) hashArgs))
      (fun p => startPre p.1 ∧ inv p.2) post hashTime := by
    refine Language.call_bound_of_width sizes mono control queryCost routing rep data
      (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
      (MachineCompiler.effects rep data samplingCode (machineStore qS)) (machineReply qS false) hashArgs
      startPre (fun env => Q.size (rep.ty message) env.1 ≤ width) inv post W (16 * fee)
      (nativeReplyTime overhead width cap comparisonTime scalarTime coinTime opTime) hW hstart hsInv ?_ ?_ ?_
    · intro env hi
      rw [hashArgs_denote]
      refine ⟨hi, ?_⟩
      have hp := sizes.prod_le (rep.ty message) rep.data.unit (env.1.1, ())
      dsimp only at hp
      have hu := values.unit
      have hm : Q.size (rep.ty message) env.1.1 ≤ width := hi
      change Q.size (StepClass.HasProd.prod (rep.ty message) rep.data.unit) (env.1.1, ()) ≤ W
      have hb : 3 * width ≤ W := by dsimp [W, finishFrameWidth, ReplyCompiler.writtenStoreWidth]; nlinarith
      omega
    · intro env hi
      exact hashArgs_cost rep data cost primitive localLaws dataLaws primitiveBound sizes mono env W
        hW (values.unit.trans hw) (hstart env hi)
    · exact ReplyCompiler.replyProgram_invariant_bound rep data samplingCode cost primitive control queryCost sizes lists
        localLaws dataLaws primitiveBound mono routing qS false width cap comparisonTime scalarTime coinTime opTime hh values ops samples
  have hbody := Language.bind_bound_of_width_transition sizes localLaws mono control queryCost routing rep data
    (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (machineStore qS))
    (MachineCompiler.effects rep data samplingCode (machineStore qS)) (.call (machineReply qS false) hashArgs) readProg
    startPre (fun g => Q.size (rep.ty point₁) g ≤ width) inv after post W hashTime readBindTime
    hW hstart (fun _ hg => hg.trans hw) hsInv hsAfter hhash hreadBind
  have hsyntax : Program.bind (.call (machineReply qS false) hashArgs) readProg = body qS := rfl
  rw [hsyntax] at hbody
  have hunary := MachineCompiler.unary_bound rep data samplingCode sizes localLaws dataLaws mono control queryCost routing
    cost primitive (machineStore qS) (body qS) (fun out => Q.size (rep.ty message) out.1 ≤ width) inv post W bodyTime
    hW (values.unit.trans hw) (by
      intro out hm
      have h := forgery_size rep sizes out width hh hm (values.point out.2)
      dsimp [W, finishFrameWidth, ReplyCompiler.writtenStoreWidth]
      nlinarith) hsInv hbody
  have hcode : backendFinish rep data samplingCode cost primitive qS =
      MachineCompiler.unary rep data samplingCode cost primitive (machineStore qS) (body qS) := by
    unfold backendFinish
    exact congrArg (MachineCompiler.unary rep data samplingCode cost primitive (machineStore qS)) (machineFinish_eq qS)
  have hbound : Bounds control queryCost (backendFinish rep data samplingCode cost primitive qS)
      (fun p => Q.size (rep.ty message) p.1.1 ≤ width ∧ inv p.2) post (bodyTime + 7 * fee) :=
    Eq.mpr (congrArg (fun code : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.ty Forgery) (rep.ty (machineStore qS)))
      (StepClass.HasProd.prod (rep.ty point₁) (rep.ty (machineStore qS))) =>
        Bounds control queryCost code (fun p => Q.size (rep.ty message) p.1.1 ≤ width ∧ inv p.2)
          post (bodyTime + 7 * fee)) hcode) hunary
  have hreplyFee : overhead (32 * ReplyCompiler.replyFrameWidth width cap) ≤ fee := by
    apply mono
    dsimp [W, finishFrameWidth, ReplyCompiler.writtenStoreWidth, ReplyCompiler.replyFrameWidth]
    nlinarith
  have hreplyTime : nativeReplyTime overhead width cap comparisonTime scalarTime coinTime opTime ≤
      2 * (cap * (comparisonTime + 257 * fee)) + scalarTime + coinTime + 7 * opTime + 700 * fee := by
    dsimp only [nativeReplyTime]
    gcongr
  intro input hi z hz
  obtain ⟨hout, ht⟩ := hbound input hi z hz
  refine ⟨hout, ?_⟩
  dsimp only [bodyTime, hashTime, readBindTime, readTime, lookupBindTime, lookupTime, extractTime, scanTime] at ht
  dsimp only [nativeFinishTime]
  change z.steps ≤ (3 * cap + 1) * (comparisonTime + 257 * fee) + scalarTime + coinTime + 10 * opTime + 1000 * fee
  nlinarith

end Signatures.Runtime.Coron.FinishCompiler
