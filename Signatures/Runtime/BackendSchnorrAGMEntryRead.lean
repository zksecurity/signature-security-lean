import Signatures.Runtime.BackendSchnorrAGMReadBudget
import Signatures.Runtime.SchnorrAGMExtraction

/-! Native read exposing the actual first cached entry for final extraction.
It reuses the same setup, cache scan, sampler and metadata retention as Read.
The return adapter retains all affine fields instead of projecting the challenge. -/

open OracleComp OracleSpec PFunctor Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native.EntryRead

open BackendProgram

abbrev outputTy : Ty CryptoAtom := .pair entryTy stateTy

def returnValue {F G M : Type}
    (input : Read.retainedOutputTy.Value (cryptoBase F G Unit Unit M)) :
    EncodedEntry F × EncodedState F G M :=
  (input.1.1.1, input.1.1.2, input.2.1, input.2.2.1, input.2.2.2.1, input.1.2.2)

def returnExpression : Expr CryptoOp [Read.retainedOutputTy] outputTy :=
  let input : Expr CryptoOp [Read.retainedOutputTy] Read.retainedOutputTy := .var .here
  let core := Expr.fst input
  let metadata := Expr.snd input
  .pair (.fst (.fst core))
    (.pair (.snd (.fst core))
      (.pair (.fst metadata) (.pair (.fst (.snd metadata))
        (.pair (.fst (.snd (.snd metadata))) (.snd (.snd core))))))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def finish : Q.Realizer (rep.ty Read.retainedOutputTy) (rep.ty outputTy) returnValue :=
  Q.compose (Read.frame rep data Read.retainedOutputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive returnExpression)

variable {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def code : Code Q unifSpec iface (rep.ty Read.inputTy) (rep.ty outputTy) :=
  .seq (.atomic (Read.setup rep data cost primitive))
    (.seq (.first (rep.ty metaTy) (cacheAccess rep data cost primitive sampler))
      (.atomic (finish rep data cost primitive)))

theorem denote (input : Read.inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (code rep data cost primitive sampler).denote input =
      (fun r => returnValue (r, input.2.2.2)) <$>
        (cacheAccess rep data cost primitive sampler).denote (Read.packValue input).1 := by
  simp only [code, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

theorem source [SampleableType F] (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (s : State F G₁ M) (k : M × G₁) (a : Affine F) :
    (code rep data cost primitive sampler).denote (k, encodeAffine a, encodeState s) =
      (fun p => (encodeEntry p.1, encodeState p.2)) <$> (readEntry k a).run s := by
  rw [denote, cacheAccess_denote]
  simp only [Read.packValue, Read.setupValue, encodeState, cacheMap_encode]
  cases hc : cacheMap s.cache k with
  | some e =>
      simp [hc, readEntry, StateT.run, returnValue, encodeMetadata]
  | none =>
      simp [hc, readEntry, StateT.run, hsample, bind_pure_comp, Functor.map_map,
        returnValue, record, encodeMetadata, encodeEntry, encodeAffine, freshValue]
      rfl

theorem hit_run (other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (input : Read.inputTy.Value (cryptoBase F G₁ G₂ K M)) (e : EncodedEntry F)
    (hit : cacheMap input.2.2.1 input.1 = some e) :
    (code rep data cost primitive sampler).run control queryCost input =
      (code rep data cost primitive other).run control queryCost input := by
  have h := cacheAccess_hit_run rep data cost primitive sampler other control queryCost
    input.1 (0, false, input.2.1) input.2.2.1 (input.2.1, input.2.2.2.2.2.2) e hit
  simp only [code, Code.run, sequenceRun, pure_bind, Read.packValue, Read.setupValue]
  rw [h]

/-- The complete costed read preserves both histories and the malformed flag,
including on noncanonical encoded states. -/
theorem histories_run (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (input : Read.inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    ∀ out ∈ support ((code rep data cost primitive sampler).run control queryCost input),
    out.value.2.2.1 = input.2.2.2.1 ∧ out.value.2.2.2.1 = input.2.2.2.2.1 ∧
      out.value.2.2.2.2.1 = input.2.2.2.2.2.1 := by
  intro out hout
  have h := Code.value_mem_denote control queryCost (code rep data cost primitive sampler) input out hout
  rw [denote, support_map] at h
  obtain ⟨p, _, hp⟩ := h
  rw [← hp]
  exact ⟨rfl, rfl, rfl⟩

end Signatures.Runtime.SchnorrAGM.Native.EntryRead
