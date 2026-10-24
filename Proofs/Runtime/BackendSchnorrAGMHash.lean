import Proofs.Runtime.BackendSchnorrAGMFlattenBudget
import Proofs.Runtime.BackendSchnorrAGMReadBudget

/-! Native Schnorr hashing once the request's singleton group/coefficient shape
has been decoded. The explanation is computed from the chronological basis
before the read, with the complete state retained as explicit runtime data. -/

open OracleComp OracleSpec PFunctor Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native.Hash

open BackendProgram

abbrev inputTy : Ty CryptoAtom := .pair cacheKeyTy (.pair (.list scalar) stateTy)

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))

def prepareWith (flatten : Expr CryptoOp [.list affineTy, .list scalar, inputTy] affineTy) :
    Expr CryptoOp [inputTy] Read.inputTy :=
  .letE (.fst (.snd v0))
    (.letE (.fst (.snd (.snd (.snd v1))))
      (.letE flatten (.pair (.fst v3) (.pair v0 (.snd (.snd v3))))))

def prepareExpression : Expr CryptoOp [inputTy] Read.inputTy := prepareWith Flatten.expression

def prepareValue {F G M : Type} [Field F] (input : (M × G) × List F × EncodedState F G M) :=
  (input.1, Flatten.value input.2.2.2.1 input.2.1, input.2.2)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem prepareExpression_value (cost : PrimitiveCosts)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    prepareExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = prepareValue input := by
  change (input.1, (Flatten.expression (Γ := [inputTy])).denote (arithmetic F G₁ G₂ K M cost)
    (input.2.2.2.1, input.2.1, input, ()), input.2.2) = _
  rw [Flatten.expression_denote]
  rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def prepare : Q.Realizer (rep.ty inputTy) (rep.ty Read.inputTy) prepareValue :=
  (Q.compose (Read.frame rep data inputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive prepareExpression)).castFunction
      (by funext input; exact prepareExpression_value cost input)

variable {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def code : Code Q unifSpec iface (rep.ty inputTy) (rep.ty Read.outputTy) :=
  .seq (.atomic (prepare rep data cost primitive)) (Read.code rep data cost primitive sampler)

theorem denote (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (code rep data cost primitive sampler).denote input =
      (Read.code rep data cost primitive sampler).denote (prepareValue input) := by
  simp only [code, Code.denote, pure_bind]

theorem source [SampleableType F] (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (s : State F G₁ M) (k : M × G₁) (coeff : List F) :
    (code rep data cost primitive sampler).denote (k, coeff, encodeState s) =
      (fun p => (p.1, encodeState p.2)) <$> (SchnorrAGM.read k (flatten coeff s.representations)).run s := by
  rw [denote]
  simp only [prepareValue, encodeState, encodeMetadata, Flatten.value_source]
  exact Read.source rep data cost primitive sampler hsample s k (flatten coeff s.representations)

theorem hit_run (other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (entry : EncodedEntry F)
    (hit : cacheMap input.2.2.1 input.1 = some entry) :
    (code rep data cost primitive sampler).run control queryCost input =
      (code rep data cost primitive other).run control queryCost input := by
  have h := Read.hit_run rep data cost primitive sampler other control queryCost (prepareValue input) entry hit
  simp only [code, Code.run, sequenceRun, pure_bind]
  rw [h]

/-- Even noncanonical encoded states retain both histories and the malformed
flag exactly. The read may only change the cache and bad-event flag. -/
theorem preserved_run (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    ∀ out ∈ support ((code rep data cost primitive sampler).run control queryCost input),
    out.value.2.2.1 = input.2.2.2.1 ∧ out.value.2.2.2.1 = input.2.2.2.2.1 ∧
      out.value.2.2.2.2.1 = input.2.2.2.2.2.1 := by
  intro out hout
  have h := Code.value_mem_denote control queryCost (code rep data cost primitive sampler) input out hout
  rw [denote, Read.denote] at h
  simp only [support_map, Set.mem_image] at h
  obtain ⟨r, _, hr⟩ := h
  rw [← hr]
  exact ⟨rfl, rfl, rfl⟩

theorem prepare_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    sizes.localSize (prepare rep data cost primitive) ≤
      primitiveSize .zero + primitiveSize .natEq + primitiveSize .natSub + primitiveSize .natAdd +
        2 * primitiveSize .mul + 2 * primitiveSize .add + 1800 * allowance + 16 := by
  rw [prepare, DescriptionSize.castFunction]
  have hframe : sizes.localSize (Read.frame rep data inputTy) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have h := laws.compose_bound hframe
    (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
      laws dataLaws primitiveSize hp prepareExpression)
  refine h.trans ?_
  simp only [prepareExpression, prepareWith, Flatten.expression, Flatten.sumRows, Flatten.body,
    Expression.descriptionBound, Expression.descriptionBound_weakenTail,
    AGM.attachTable, AGM.attachFold, AGM.attachBody, index, indexBody, reverseList, Expression.variableDescription]
  omega

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    (code rep data cost primitive sampler).descriptionSize sizes ≤
      sampler.descriptionSize sizes + primitiveSize .messageEq + primitiveSize .point₁Eq +
        3 * primitiveSize .add + 3 * primitiveSize .zero + primitiveSize .scalarEq +
        primitiveSize .natEq + primitiveSize .natSub + primitiveSize .natAdd +
        2 * primitiveSize .mul + 2600 * allowance + 70 := by
  have hp' := prepare_description rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
  have hr := Read.description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp
  dsimp only [code, Code.descriptionSize]
  omega

end Signatures.Runtime.SchnorrAGM.Native.Hash
