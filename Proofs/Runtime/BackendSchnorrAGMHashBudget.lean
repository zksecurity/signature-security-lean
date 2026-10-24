import Proofs.Runtime.BackendSchnorrAGMHashLocalCost

/-! Complete native budget for the decoded Schnorr hash path. Every preparation,
coefficient scan, cache scan, draw and control transition is included. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Hash

open BackendProgram

def hashTime (overhead : Nat → Nat)
    (width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime : Nat) : Nat :=
  let W := frameWidth width cap coeffCap historyWidth
  Flatten.flattenTime overhead W basisCap coeffCap comparisonTime subtractTime incrementTime fieldTime mulTime fieldTime +
    Read.readTime overhead (3 * width) cap historyWidth messageTime pointTime fieldTime equalityTime sampleTime +
      262 * overhead (256 * W)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists mono routing

private theorem compose_bound (width cap historyWidth basisCap coeffCap preparationTime readTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hp : Bounds control queryCost (.atomic (iface := iface) (prepare rep data cost primitive))
      (Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (Read.Input (Q := Q) rep (3 * width) cap historyWidth) preparationTime)
    (hr : Bounds control queryCost (Read.code rep data cost primitive sampler)
      (Read.Input (Q := Q) rep (3 * width) cap historyWidth)
      (Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth) readTime) :
    Bounds control queryCost (code rep data cost primitive sampler)
      (Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (fun out => Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth out ∧
        out.2.2.1.length ≤ basisCap)
      (preparationTime + readTime + overhead (256 * frameWidth width cap coeffCap historyWidth)) := by
  have hwide : width ≤ 3 * width := by omega
  have hall := Bounds.seq control queryCost (.atomic (prepare rep data cost primitive))
    (Read.code rep data cost primitive sampler)
    (Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
    (Read.Input (Q := Q) rep (3 * width) cap historyWidth)
    (Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
    preparationTime readTime (overhead (256 * frameWidth width cap coeffCap historyWidth)) hp hr (by
      intro input hi output ho
      have hin := (input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf input hi).1
      have hout := Read.input_size rep sizes lists (3 * width) cap historyWidth
        (hh.trans hwide) (fun b => (hb b).trans hwide) output ho
      apply (routing.sequence _ _).trans (mono ?_)
      dsimp only [frameWidth] at hin ⊢
      omega)
  change Bounds control queryCost (code rep data cost primitive sampler)
    (Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
    (Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
    (preparationTime + readTime + overhead (256 * frameWidth width cap coeffCap historyWidth)) at hall
  intro input hi z hzrun
  obtain ⟨hout, ht⟩ := hall input hi z hzrun
  have hkeep := preserved_run rep data cost primitive sampler control queryCost input
  -- Abstract the program while applying its support property, so elaboration
  -- does not try to evaluate the whole costed interpreter.
  generalize hprogram : code rep data cost primitive sampler = program at hkeep hzrun
  have hkeep := hkeep z hzrun
  refine ⟨⟨hout, ?_⟩, ht⟩
  rw [hkeep.1]
  exact hi.2.2.1

include laws dataLaws

theorem bound (width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ basisCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hEq : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hInc : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * width → Q.size (rep.ty message) b ≤ 15 * width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * width → Q.size (rep.ty point₁) b ≤ 15 * width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (hmul : ∀ a b : F, (primitiveBound .mul).time (a, b) ≤ mulTime)
    (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime)
    (hd : Bounds control queryCost sampler (fun _ => True)
      (fun c => Q.size (rep.ty scalar) c ≤ width) sampleTime) :
    Bounds control queryCost (code rep data cost primitive sampler)
      (Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (fun out => Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth out ∧
        out.2.2.1.length ≤ basisCap)
      (hashTime overhead width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
        messageTime pointTime fieldTime mulTime equalityTime sampleTime) := by
  let W := frameWidth width cap coeffCap historyWidth
  let fee := overhead (256 * W)
  let flattenBudget := Flatten.flattenTime overhead W basisCap coeffCap comparisonTime subtractTime incrementTime fieldTime mulTime fieldTime
  let readBudget := Read.readTime overhead (3 * width) cap historyWidth messageTime pointTime fieldTime equalityTime sampleTime
  let middle := Read.Input (Q := Q) rep (3 * width) cap historyWidth
  let post := Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth
  have hwide : width ≤ 3 * width := by omega
  have hprepare := prepare_bound (iface := iface) rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    control queryCost routing width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
    fieldTime mulTime hh hu hb hn hf hEq hSub hInc hz hmul hadd
  have hread : Bounds control queryCost (Read.code rep data cost primitive sampler) middle post readBudget :=
    Read.bound rep data cost primitive sampler sizes lists laws dataLaws primitiveBound mono
    control queryCost routing (3 * width) cap historyWidth messageTime pointTime fieldTime equalityTime sampleTime
    (hh.trans hwide) (hu.trans hwide) (fun b => (hb b).trans hwide) (fun f => (hf f).trans hwide)
    (fun a b ha hb => hm a b (by omega) (by omega))
    (fun a b ha hb => hg a b (by omega) (by omega)) hz hadd heq
    (by intro input hi z hz; have h := hd input hi z hz; exact ⟨h.1.trans hwide, h.2⟩)
  have hall := compose_bound rep data cost primitive sampler sizes lists mono control queryCost routing
    width cap historyWidth basisCap coeffCap (flattenBudget + 261 * fee) readBudget hh hu hb hf hprepare hread
  intro input hi z hzrun
  obtain ⟨hout, ht⟩ := hall input hi z hzrun
  refine ⟨hout, ht.trans ?_⟩
  dsimp only [flattenBudget, readBudget, fee, W, hashTime]
  omega

end Signatures.Runtime.SchnorrAGM.Native.Hash
