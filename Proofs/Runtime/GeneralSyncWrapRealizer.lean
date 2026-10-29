import Proofs.Runtime.GeneralSyncWrapCode
import Proofs.Runtime.GeneralSyncWrapFinish

/-! # The wrapper's three codes

Initialization assembles the attacker's key pair and starts it; the readout runs the attacker's
readout and relabels a signing request as the hash of its period, a returned forgery as the
final hash, and a finished state as its compiled finish; the transition decodes the tagged reply,
feeds the attacker its own reply (corrected after a signature) and records a mark, or holds the
period's hash until the signature arrives. Every piece is structural code of the fixed backend,
the attacker's own codes, the interface adapters, compiled arithmetic, or the scheme's
correction, final-scalar and key routines. Each piece is built with the index its structure
gives it and then transported to the stated function, so that no higher-order unification is
left to elaboration. -/

open OracleComp OracleSpec PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation
open Signatures.Runtime.WeightedAGM (GeneralRequest GeneralIndex BoundedRandomReply generalSpec
  generalPositions NativePorts tagRandom tagHash tagSign)
open Signatures.Runtime.BackendProgram

namespace Signatures.Runtime.SyncWrapGeneral

set_option linter.unusedSectionVars false

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {bdI : Boundary C (generalSpec (key.Value (cryptoBase F G₁ G₂ K M))
    (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor (G₂ × G₂)
    (OutTy.Value (cryptoBase F G₁ G₂ K M))}
  (ports : NativePorts (Q := Q) rep key Weights.syncMessage bdI)
  (wports : WrapPorts rep ports)
  (correction finalFn : K × F → F) (keys : G₂ → G₂ × G₂)
  (code : SchemeCode rep correction finalFn keys)
  (R : GeneralCaller.Caller (Q := Q) (bd := bdI))

attribute [local implicit_reducible] PFunctor.Idx

local notation "sRep" => R.state
local notation "pRep" => rep.ty point₁
local notation "kRep" => rep.ty key
local notation "msgRep" => rep.ty Weights.syncMessage
local notation "mRep" => marksRep rep
local notation "boundedRep" => rep.ty (boundedNat randomBound)
local notation "restRep" => rep.ty (Ty.pair scalar (Ty.pair (Ty.list scalar) (Ty.list scalar)))
local notation "prod" => StepClass.HasProd.prod
local notation "sum" => StepClass.HasSum.sum
local notation "opt" => StepClass.HasOption.option

/-- The wrapper's boundary: the weighted public key in, the attacker's output and interface
representations otherwise. -/
def outerBoundary : Boundary C (generalSpec (key.Value (cryptoBase F G₁ G₂ K M))
    (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor G₂
    (OutTy.Value (cryptoBase F G₁ G₂ K M)) :=
  ⟨rep.ty point₂, bdI.out, bdI.pos, bdI.idx⟩

/-! ## Initialization -/

def initCode : Q.Realizer (rep.ty point₂) (stateRep rep R) (wrapped correction finalFn keys R).init :=
  (Q.compose (QP.pair (Q.compose code.keys (Q.compose wports.input R.initCode))
      (Q.compose (data.unit (rep.ty point₂)) (data.nil (rep.ty markTy))))
    (QS.inl (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))))).castFunction (by funext pk; rfl)

/-! ## Readout -/

/-- The attacked period of a decoded output. -/
def periodCode : Q.Realizer (rep.ty OutTy) kRep finalIndex :=
  (Q.compose (QP.fst msgRep restRep) (QP.fst kRep (rep.ty scalar))).castFunction (by funext result; rfl)

/-- Encode a hash request. -/
def hashPosCode : Q.Realizer kRep bdI.pos (fun t => .inl (.inr t)) :=
  (Q.compose (QS.inr boundedRep kRep)
    (Q.compose (QS.inl (sum boundedRep kRep) msgRep) wports.position)).castFunction (by funext t; rfl)

/-- A returned forgery exposes the hash of its period. -/
def finalPosCode : Q.Realizer bdI.out bdI.pos (fun result => .inl (.inr (finalIndex result))) :=
  (Q.compose wports.output (Q.compose (periodCode rep) (hashPosCode rep ports wports))).castFunction
    (by funext result; rfl)

/-- A pending signing request exposes the hash of its period; other requests pass. -/
def translatePosCode : Q.Realizer bdI.pos bdI.pos translatePos :=
  (Q.compose ports.request
    (Q.compose (QS.elim (QS.inl (sum boundedRep kRep) msgRep)
        (Q.compose (QP.fst kRep (rep.ty scalar))
          (Q.compose (QS.inr boundedRep kRep) (QS.inl (sum boundedRep kRep) msgRep))))
      wports.position)).castFunction (by
    funext pos
    rcases pos with (n | t) | m <;> rfl)

def headReadyCode : Q.Realizer (readyRep rep R) (sum bdI.out bdI.pos) (fun p => headReadyFn R p.1) :=
  (Q.compose (QP.fst sRep mRep)
    (Q.compose R.headCode
      (QS.elim (Q.compose (finalPosCode rep ports wports) (QS.inr bdI.out bdI.pos))
        (Q.compose (translatePosCode rep ports wports) (QS.inr bdI.out bdI.pos))))).castFunction (by
    funext p
    cases R.machine.head p.1 <;> rfl)

def headGotCode : Q.Realizer (gotRep rep R) (sum bdI.out bdI.pos) (fun p => headGotFn R p.1) :=
  (Q.compose (QP.fst sRep (prod pRep mRep))
    (Q.compose R.headCode
      (QS.elim (Q.compose (finalPosCode rep ports wports) (QS.inr bdI.out bdI.pos))
        (QS.inr bdI.out bdI.pos)))).castFunction (by
    funext p
    cases R.machine.head p.1 <;> rfl)

/-- Arguments of the compiled finish: output, marks, final scalar. -/
def finishArgsCode : Q.Realizer (prod (prod (rep.ty OutTy) mRep) (rep.ty scalar))
    (rep.env [OutTy, .list markTy, scalar]) (fun p => (p.1.1, (p.1.2, (p.2, ())))) :=
  (QP.pair (Q.compose (QP.fst (prod (rep.ty OutTy) mRep) (rep.ty scalar)) (QP.fst (rep.ty OutTy) mRep))
    (QP.pair (Q.compose (QP.fst (prod (rep.ty OutTy) mRep) (rep.ty scalar)) (QP.snd (rep.ty OutTy) mRep))
      (QP.pair (QP.snd (prod (rep.ty OutTy) mRep) (rep.ty scalar))
        (data.unit (prod (prod (rep.ty OutTy) mRep) (rep.ty scalar)))))).castFunction (by funext p; rfl)

/-- The final scalar of a decoded output paired with its marks. -/
def finalScalarCode : Q.Realizer (prod (rep.ty OutTy) mRep) (rep.ty scalar) (fun p => finalFn p.1.1) :=
  (Q.compose (QP.fst (rep.ty OutTy) mRep) (Q.compose (QP.fst msgRep restRep) code.fin)).castFunction
    (by funext p; rfl)

/-- The finish: decode the attacker's output, compute the final scalar, run the compiled
coefficient code, encode. -/
def finishCode : Q.Realizer (doneRep rep (bdI := bdI)) bdI.out (fun p => fin finalFn p.1 p.2) :=
  (Q.compose (QP.pair (Q.compose (QP.fst bdI.out mRep) wports.output) (QP.snd bdI.out mRep))
    (Q.compose (QP.pair (Q.identity (prod (rep.ty OutTy) mRep)) (finalScalarCode rep correction finalFn keys code))
      (Q.compose (finishArgsCode rep data)
        (Q.compose (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive finExpr)
          wports.encode)))).castFunction (by
    funext p
    simp only [Function.comp_def, id]
    exact finExpr_denote_fin cost finalFn p.1 p.2)

def headDoneCode : Q.Realizer (doneRep rep (bdI := bdI)) (sum bdI.out bdI.pos) (fun p => .inl (fin finalFn p.1 p.2)) :=
  (Q.compose (finishCode rep data cost primitive ports wports correction finalFn keys code)
    (QS.inl bdI.out bdI.pos)).castFunction (by funext p; rfl)

def headCode : Q.Realizer (stateRep rep R) (outerBoundary rep (bdI := bdI)).head (wrapped correction finalFn keys R).head :=
  (QS.elim (headReadyCode rep ports wports R)
    (QS.elim (headGotCode rep ports wports R)
      (headDoneCode rep data cost primitive ports wports correction finalFn keys code))).castFunction (by
    rw [← headFn_eq correction finalFn keys R]
    funext st
    rcases st with ⟨s, marks⟩ | ⟨s, h, marks⟩ | ⟨result, marks⟩ <;> rfl)

/-! ## Transition -/

/-- The mark of a hash reply. -/
def markHashCode : Q.Realizer rep.data.unit (rep.ty markTy) (fun _ => (markHash : Mark F)) :=
  (QP.pair (data.bool false) (primitive CryptoOp.zero)).castFunction (by funext _; rfl)

/-- The mark of a signing reply: the flag and the correction. -/
def markSignCode : Q.Realizer msgRep (rep.ty markTy) (markSign correction) :=
  (QP.pair (Q.compose (data.unit msgRep) (data.bool true)) code.corr).castFunction (by funext m; rfl)

abbrev readyCtx := prod (readyRep rep R) bdI.idx
abbrev gotCtx := prod (gotRep rep R) bdI.idx

/-- Forget the held hash. -/
def dropPointCode : Q.Realizer (gotCtx rep R) (readyCtx rep R) (fun p => ((p.1.1, p.1.2.2), p.2)) :=
  (QP.pair (QP.pair (Q.compose (QP.fst (gotRep rep R) bdI.idx) (QP.fst sRep (prod pRep mRep)))
      (Q.compose (QP.fst (gotRep rep R) bdI.idx) (Q.compose (QP.snd sRep (prod pRep mRep)) (QP.snd pRep mRep))))
    (QP.snd (gotRep rep R) bdI.idx)).castFunction (by funext p; rfl)

/-- Feed the attacker the tagged reply. -/
def fedCode : Q.Realizer (readyCtx rep R) (opt sRep) (fun p => R.machine.update? (p.1.1, p.2)) :=
  (Q.compose (QP.pair (Q.compose (QP.fst (readyRep rep R) bdI.idx) (QP.fst sRep mRep)) (QP.snd (readyRep rep R) bdI.idx))
    R.updateCode).castFunction (by funext p; rfl)

/-- A continued attacker state with its marks is a ready state. -/
def readyAgainCode : Q.Realizer (prod sRep mRep) (opt (stateRep rep R)) (fun p => some (ready R.machine p.1 p.2)) :=
  (Q.compose (QS.inl (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI)))) (OC.someCode (stateRep rep R))).castFunction
    (by funext p; rfl)

/-- Feed the attacker the tagged reply and, if it was expected, apply the mark update. -/
def stepReadyCode {update : List (Mark F) → List (Mark F)} (markCode : Q.Realizer mRep mRep update) :
    Q.Realizer (readyCtx rep R) (opt (stateRep rep R))
      (fun p => (R.machine.update? (p.1.1, p.2)).map fun s' => ready R.machine s' (update p.1.2)) :=
  (Q.compose (QP.pair (fedCode rep R)
      (Q.compose (QP.fst (readyRep rep R) bdI.idx) (Q.compose (QP.snd sRep mRep) markCode)))
    (QO.bindContext (readyAgainCode rep R))).castFunction (by
    funext p
    simp only [Function.comp_def]
    cases R.machine.update? (p.1.1, p.2) <;> rfl)

/-- Record nothing. -/
def keepMarksCode : Q.Realizer mRep mRep (fun marks => marks) := Q.identity mRep

/-- Record a hash reply. -/
def recordHashCode : Q.Realizer mRep mRep (fun marks => markHash :: marks) :=
  (Q.compose (QP.pair (Q.compose (data.unit mRep) (markHashCode rep data cost primitive)) (Q.identity mRep))
    (data.cons (rep.ty markTy))).castFunction (by funext marks; rfl)

/-- Compare the hashed period with the expected one and branch on the decoded reply. -/
def expectHashCode {E : Type} {e : C.Str E} {expected : E → K} (expectedCode : Q.Realizer e kRep expected)
    {next : (K × G₁) × E → State R.machine (F := F)}
    (nextCode : Q.Realizer (prod (prod kRep pRep) e) (stateRep rep R) next) :
    Q.Realizer (prod (replyRep rep ports) e) (opt (stateRep rep R))
      (fun p => match p.1 with
        | .inr (.inl (t', h)) => if t' = expected p.2 then some (next ((t', h), p.2)) else none
        | _ => none) :=
  let compare := Q.compose
    (QP.pair (Q.compose (QP.pair (Q.compose (QP.fst (prod kRep pRep) e) (QP.fst kRep pRep))
        (Q.compose (QP.snd (prod kRep pRep) e) expectedCode)) (primitive CryptoOp.keyEq))
      (Q.identity (prod (prod kRep pRep) e)))
    (Q.compose (data.select (prod (prod kRep pRep) e))
      (QS.elim (Q.compose nextCode (OC.someCode (stateRep rep R)))
        (QO.none (prod (prod kRep pRep) e) (stateRep rep R))))
  (QuantitativeStepClass.IsDistributive.elimContext Q QD (QO.none (prod ports.randomReply e) (stateRep rep R))
    (QuantitativeStepClass.IsDistributive.elimContext Q QD compare
      (QO.none (prod (prod msgRep pRep) e) (stateRep rep R)))).castFunction (by
      funext p
      obtain ⟨d, ctx⟩ := p
      rcases d with r | ⟨t', h⟩ | ⟨m', σ⟩
      · rfl
      · simp only [Sum.elim_inr, Sum.elim_inl, Function.comp_def, id, arithmetic]
        by_cases ht : t' = expected ctx <;> simp [ht]
      · rfl)

/-- Decode the tagged reply and keep the context. -/
def decodedCode {E : Type} (e : C.Str E)
    {idxOf : E → GeneralIndex (key.Value (cryptoBase F G₁ G₂ K M)) (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound}
    (idxCode : Q.Realizer e bdI.idx idxOf) :
    Q.Realizer e (prod (replyRep rep ports) e) (fun ctx => (decodeIdx F G₁ G₂ K M randomBound (idxOf ctx), ctx)) :=
  (QP.pair (Q.compose idxCode wports.reply) (Q.identity e)).castFunction (by funext ctx; rfl)

/-- The tagged reply of a ready context. -/
def readyIdxCode : Q.Realizer (readyCtx rep R) bdI.idx (fun p => p.2) := QP.snd (readyRep rep R) bdI.idx

/-- The forgery's period, read from the attacker's returned output. -/
def finishExpectedCode : Q.Realizer (prod bdI.out (readyCtx rep R)) kRep (fun p => finalIndex p.1) :=
  (Q.compose (QP.fst bdI.out (readyCtx rep R)) (Q.compose wports.output (periodCode rep))).castFunction
    (by funext p; rfl)

/-- The finished state: the returned output with the recorded marks. -/
def finishNextCode : Q.Realizer (prod (prod kRep pRep) (prod bdI.out (readyCtx rep R))) (stateRep rep R)
    (fun p => done R.machine p.2.1 p.2.2.1.2) :=
  (Q.compose (QP.pair (Q.compose (QP.snd (prod kRep pRep) (prod bdI.out (readyCtx rep R))) (QP.fst bdI.out (readyCtx rep R)))
      (Q.compose (QP.snd (prod kRep pRep) (prod bdI.out (readyCtx rep R))) (Q.compose (QP.snd bdI.out (readyCtx rep R))
        (Q.compose (QP.fst (readyRep rep R) bdI.idx) (QP.snd sRep mRep)))))
    (Q.compose (QS.inr (gotRep rep R) (doneRep rep (bdI := bdI))) (QS.inr (readyRep rep R) _))).castFunction
    (by funext p; rfl)

/-- From the attacker's returned forgery: wait for the final hash, then finish. -/
def finishReadyCode : Q.Realizer (prod bdI.out (readyCtx rep R)) (opt (stateRep rep R))
    (fun p => match decodeIdx F G₁ G₂ K M randomBound p.2.2 with
      | .inr (.inl (t', _)) => if t' = finalIndex p.1 then some (done R.machine p.1 p.2.1.2) else none
      | _ => none) :=
  (Q.compose (decodedCode rep ports wports (prod bdI.out (readyCtx rep R))
      (Q.compose (QP.snd bdI.out (readyCtx rep R)) (readyIdxCode rep R)))
    (expectHashCode rep data cost primitive ports R (finishExpectedCode rep ports wports R) (finishNextCode rep R))).castFunction (by
    funext p
    simp only [Function.comp_def]
    rcases decodeIdx F G₁ G₂ K M randomBound p.2.2 with r | ⟨t', h⟩ | ⟨m', σ⟩ <;> rfl)

/-- The period of a pending signing request. -/
def holdExpectedCode : Q.Realizer (prod msgRep (readyCtx rep R)) kRep (fun p => p.1.1) :=
  (Q.compose (QP.fst msgRep (readyCtx rep R)) (QP.fst kRep (rep.ty scalar))).castFunction (by funext p; rfl)

/-- The waiting state: the attacker's state, the period's hash and the marks. -/
def holdNextCode : Q.Realizer (prod (prod kRep pRep) (prod msgRep (readyCtx rep R))) (stateRep rep R)
    (fun p => gotHash R.machine p.2.2.1.1 p.1.2 p.2.2.1.2) :=
  (Q.compose (QP.pair
      (Q.compose (QP.snd (prod kRep pRep) (prod msgRep (readyCtx rep R))) (Q.compose (QP.snd msgRep (readyCtx rep R))
        (Q.compose (QP.fst (readyRep rep R) bdI.idx) (QP.fst sRep mRep))))
      (QP.pair (Q.compose (QP.fst (prod kRep pRep) (prod msgRep (readyCtx rep R))) (QP.snd kRep pRep))
        (Q.compose (QP.snd (prod kRep pRep) (prod msgRep (readyCtx rep R))) (Q.compose (QP.snd msgRep (readyCtx rep R))
          (Q.compose (QP.fst (readyRep rep R) bdI.idx) (QP.snd sRep mRep))))))
    (Q.compose (QS.inl (gotRep rep R) (doneRep rep (bdI := bdI))) (QS.inr (readyRep rep R) _))).castFunction
    (by funext p; rfl)

/-- From a pending signing request: wait for the period's hash, then hold it. -/
def holdHashCode : Q.Realizer (prod msgRep (readyCtx rep R)) (opt (stateRep rep R))
    (fun p => match decodeIdx F G₁ G₂ K M randomBound p.2.2 with
      | .inr (.inl (t', h)) => if t' = p.1.1 then some (gotHash R.machine p.2.1.1 h p.2.1.2) else none
      | _ => none) :=
  (Q.compose (decodedCode rep ports wports (prod msgRep (readyCtx rep R))
      (Q.compose (QP.snd msgRep (readyCtx rep R)) (readyIdxCode rep R)))
    (expectHashCode rep data cost primitive ports R (holdExpectedCode rep R) (holdNextCode rep R))).castFunction (by
    funext p
    simp only [Function.comp_def]
    rcases decodeIdx F G₁ G₂ K M randomBound p.2.2 with r | ⟨t', h⟩ | ⟨m', σ⟩ <;> rfl)

/-- Dispatch a ready state's pending request. -/
def requestReadyCode : Q.Realizer (prod bdI.pos (readyCtx rep R)) (opt (stateRep rep R))
    (fun p => match p.1 with
      | .inl (.inl _) => (R.machine.update? (p.2.1.1, p.2.2)).map fun s' => ready R.machine s' p.2.1.2
      | .inl (.inr _) => (R.machine.update? (p.2.1.1, p.2.2)).map fun s' => ready R.machine s' (markHash :: p.2.1.2)
      | .inr m => match decodeIdx F G₁ G₂ K M randomBound p.2.2 with
        | .inr (.inl (t', h)) => if t' = m.1 then some (gotHash R.machine p.2.1.1 h p.2.1.2) else none
        | _ => none) :=
  (Q.compose (QuantitativeStepClass.HasProd.pairRight Q QP ports.request)
    (QuantitativeStepClass.IsDistributive.elimContext Q QD
      (QuantitativeStepClass.IsDistributive.elimContext Q QD
        (Q.compose (QP.snd boundedRep (readyCtx rep R)) (stepReadyCode rep R (keepMarksCode rep)))
        (Q.compose (QP.snd kRep (readyCtx rep R)) (stepReadyCode rep R (recordHashCode rep data cost primitive))))
      (holdHashCode rep data cost primitive ports wports R))).castFunction (by
    funext p
    obtain ⟨pos, ctx⟩ := p
    rcases pos with (n | t) | m <;> rfl)

/-- The transition from a ready state. -/
def updateReadyCode : Q.Realizer (readyCtx rep R) (opt (stateRep rep R)) (fun p => updateReadyFn R p.1.1 p.1.2 p.2) :=
  (Q.compose (QuantitativeStepClass.HasProd.withInput Q QP
      (Q.compose (QP.fst (readyRep rep R) bdI.idx) (Q.compose (QP.fst sRep mRep) R.headCode)))
    (QuantitativeStepClass.IsDistributive.elimContext Q QD (finishReadyCode rep data cost primitive ports wports R)
      (requestReadyCode rep data cost primitive ports wports R))).castFunction (by
    funext p
    obtain ⟨⟨s, marks⟩, idx⟩ := p
    simp only [Function.comp_def, updateReadyFn]
    rcases R.machine.head s with result | (n | t) | m <;> rfl)

abbrev signCtx := prod msgRep (gotCtx rep R)
abbrev signFrame := prod (prod msgRep pRep) (signCtx rep R)

/-- The held hash of a signing frame. -/
def heldCode : Q.Realizer (signFrame rep R) pRep (fun p => p.2.2.1.2.1) :=
  (Q.compose (QP.snd (prod msgRep pRep) (signCtx rep R)) (Q.compose (QP.snd msgRep (gotCtx rep R))
    (Q.compose (QP.fst (gotRep rep R) bdI.idx) (Q.compose (QP.snd sRep (prod pRep mRep)) (QP.fst pRep mRep))))).castFunction
    (by funext p; rfl)

/-- The corrected signature `σ + correction m' • h`. -/
def correctedCode : Q.Realizer (signFrame rep R) pRep (fun p => p.1.2 + correction p.1.1 • p.2.2.1.2.1) :=
  (Q.compose (QP.pair (Q.compose (QP.fst (prod msgRep pRep) (signCtx rep R)) (QP.snd msgRep pRep))
      (Q.compose (QP.pair (Q.compose (QP.fst (prod msgRep pRep) (signCtx rep R)) (Q.compose (QP.fst msgRep pRep) code.corr))
          (heldCode rep R))
        (primitive CryptoOp.scale₁)))
    (primitive CryptoOp.add₁)).castFunction (by funext p; rfl)

/-- Feed the attacker the corrected signature. -/
def fedSignCode : Q.Realizer (signFrame rep R) (opt sRep)
    (fun p => R.machine.update? (p.2.2.1.1, tagSign (p.1.1, p.1.2 + correction p.1.1 • p.2.2.1.2.1))) :=
  (Q.compose (QP.pair
      (Q.compose (QP.snd (prod msgRep pRep) (signCtx rep R)) (Q.compose (QP.snd msgRep (gotCtx rep R))
        (Q.compose (QP.fst (gotRep rep R) bdI.idx) (QP.fst sRep (prod pRep mRep)))))
      (Q.compose (QP.pair (Q.compose (QP.fst (prod msgRep pRep) (signCtx rep R)) (QP.fst msgRep pRep))
          (correctedCode rep cost primitive correction finalFn keys code R))
        ports.signTag))
    R.updateCode).castFunction (by funext p; rfl)

/-- Record the signing mark. -/
def markedCode : Q.Realizer (signFrame rep R) mRep (fun p => markSign correction p.1.1 :: p.2.2.1.2.2) :=
  (Q.compose (QP.pair (Q.compose (QP.fst (prod msgRep pRep) (signCtx rep R)) (Q.compose (QP.fst msgRep pRep)
        (markSignCode rep data correction finalFn keys code)))
      (Q.compose (QP.snd (prod msgRep pRep) (signCtx rep R)) (Q.compose (QP.snd msgRep (gotCtx rep R))
        (Q.compose (QP.fst (gotRep rep R) bdI.idx) (Q.compose (QP.snd sRep (prod pRep mRep)) (QP.snd pRep mRep))))))
    (data.cons (rep.ty markTy))).castFunction (by funext p; rfl)

/-- The signature arrived: correct it, feed it to the attacker, record the mark. -/
def signedCode : Q.Realizer (signFrame rep R) (opt (stateRep rep R))
    (fun p => (R.machine.update? (p.2.2.1.1, tagSign (p.1.1, p.1.2 + correction p.1.1 • p.2.2.1.2.1))).map fun s' =>
      ready R.machine s' (markSign correction p.1.1 :: p.2.2.1.2.2)) :=
  (Q.compose (QP.pair (fedSignCode rep cost primitive ports correction finalFn keys code R)
      (markedCode rep data correction finalFn keys code R))
    (QO.bindContext (readyAgainCode rep R))).castFunction (by
    funext p
    simp only [Function.comp_def]
    cases R.machine.update? (p.2.2.1.1, tagSign (p.1.1, p.1.2 + correction p.1.1 • p.2.2.1.2.1)) <;> rfl)

/-- Dispatch the decoded reply of a signing frame. -/
def feedSignCode : Q.Realizer (signCtx rep R) (opt (stateRep rep R))
    (fun p => match decodeIdx F G₁ G₂ K M randomBound p.2.2 with
      | .inr (.inr (m', σ)) =>
        (R.machine.update? (p.2.1.1, tagSign (m', σ + correction m' • p.2.1.2.1))).map fun s' =>
          ready R.machine s' (markSign correction m' :: p.2.1.2.2)
      | _ => none) :=
  (Q.compose (decodedCode rep ports wports (signCtx rep R)
      (Q.compose (QP.snd msgRep (gotCtx rep R)) (QP.snd (gotRep rep R) bdI.idx)))
    (QuantitativeStepClass.IsDistributive.elimContext Q QD (QO.none (prod ports.randomReply (signCtx rep R)) (stateRep rep R))
      (QuantitativeStepClass.IsDistributive.elimContext Q QD (QO.none (prod (prod kRep pRep) (signCtx rep R)) (stateRep rep R))
        (signedCode rep data cost primitive ports correction finalFn keys code R)))).castFunction (by
    funext p
    simp only [Function.comp_def]
    rcases decodeIdx F G₁ G₂ K M randomBound p.2.2 with r | ⟨t', h⟩ | ⟨m', σ⟩ <;> rfl)

/-- Dispatch a waiting state's pending request. -/
def requestGotCode : Q.Realizer (prod bdI.pos (gotCtx rep R)) (opt (stateRep rep R))
    (fun p => match p.1 with
      | .inr _ => match decodeIdx F G₁ G₂ K M randomBound p.2.2 with
        | .inr (.inr (m', σ)) =>
          (R.machine.update? (p.2.1.1, tagSign (m', σ + correction m' • p.2.1.2.1))).map fun s' =>
            ready R.machine s' (markSign correction m' :: p.2.1.2.2)
        | _ => none
      | .inl (.inl _) => (R.machine.update? (p.2.1.1, p.2.2)).map fun s' => ready R.machine s' p.2.1.2.2
      | .inl (.inr _) => (R.machine.update? (p.2.1.1, p.2.2)).map fun s' => ready R.machine s' (markHash :: p.2.1.2.2)) :=
  (Q.compose (QuantitativeStepClass.HasProd.pairRight Q QP ports.request)
    (QuantitativeStepClass.IsDistributive.elimContext Q QD
      (QuantitativeStepClass.IsDistributive.elimContext Q QD
        (Q.compose (QP.snd boundedRep (gotCtx rep R))
          (Q.compose (dropPointCode rep R) (stepReadyCode rep R (keepMarksCode rep))))
        (Q.compose (QP.snd kRep (gotCtx rep R))
          (Q.compose (dropPointCode rep R) (stepReadyCode rep R (recordHashCode rep data cost primitive)))))
      (feedSignCode rep data cost primitive ports wports correction finalFn keys code R))).castFunction (by
    funext p
    obtain ⟨pos, ctx⟩ := p
    rcases pos with (n | t) | m <;> rfl)

/-- The transition from a state waiting for a signature. -/
def updateGotCode : Q.Realizer (gotCtx rep R) (opt (stateRep rep R))
    (fun p => updateGotFn correction R p.1.1 p.1.2.1 p.1.2.2 p.2) :=
  (Q.compose (QuantitativeStepClass.HasProd.withInput Q QP
      (Q.compose (QP.fst (gotRep rep R) bdI.idx) (Q.compose (QP.fst sRep (prod pRep mRep)) R.headCode)))
    (QuantitativeStepClass.IsDistributive.elimContext Q QD
      (Q.compose (QuantitativeStepClass.HasProd.pairLeft Q QP (dropPointCode rep R))
        (finishReadyCode rep data cost primitive ports wports R))
      (requestGotCode rep data cost primitive ports wports correction finalFn keys code R))).castFunction (by
    funext p
    obtain ⟨⟨s, h, marks⟩, idx⟩ := p
    simp only [Function.comp_def, updateGotFn, updateReadyFn]
    rcases R.machine.head s with result | (n | t) | m <;> rfl)

def updateCode : Q.Realizer ((outerBoundary rep (bdI := bdI)).stateIdx (stateRep rep R)) (opt (stateRep rep R))
    (wrapped correction finalFn keys R).update? :=
  (Q.compose (QD.distribute (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) bdI.idx)
    (QS.elim (updateReadyCode rep data cost primitive ports wports R)
      (Q.compose (QD.distribute (gotRep rep R) (doneRep rep (bdI := bdI)) bdI.idx)
        (QS.elim (updateGotCode rep data cost primitive ports wports correction finalFn keys code R)
          (QO.none (prod (doneRep rep (bdI := bdI)) bdI.idx) (stateRep rep R)))))).castFunction (by
    rw [← updateFn_eq correction finalFn keys R]
    funext p
    obtain ⟨st, idx⟩ := p
    rcases st with ⟨s, marks⟩ | ⟨s, h, marks⟩ | ⟨result, marks⟩ <;> rfl)

/-! ## The wrapper as a general caller -/

/-- The wrapper, realized. -/
def caller : GeneralCaller.Caller (Q := Q) (bd := outerBoundary rep (bdI := bdI)) where
  machine := wrapped correction finalFn keys R
  state := stateRep rep R
  initCode := initCode rep data ports wports correction finalFn keys code R
  headCode := headCode rep data cost primitive ports wports correction finalFn keys code R
  updateCode := updateCode rep data cost primitive ports wports correction finalFn keys code R

theorem caller_machine :
    (caller rep data cost primitive ports wports correction finalFn keys code R).machine =
      wrapped correction finalFn keys R := rfl

end Signatures.Runtime.SyncWrapGeneral
