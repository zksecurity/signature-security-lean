import Signatures.Runtime.BackendSchnorrAGMCacheBudget

/-! Complete native Schnorr AGM reads. Setup constructs the fallback entry,
packs the cache arguments and retains the rest of the encoded source state.
The return adapter installs the updated cache and bad flag. These are executable
local routines, not the proof-only metadata-restoration map. -/

open OracleComp OracleSpec PFunctor Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native.Read

open BackendProgram

abbrev inputTy : Ty CryptoAtom := .pair cacheKeyTy (.pair affineTy stateTy)
abbrev coreInputTy : Ty CryptoAtom :=
  .pair (.pair cacheKeyTy (.pair entryTy (.pair cacheTy .unit))) readStoreTy
abbrev coreOutputTy : Ty CryptoAtom := .pair (.pair entryTy cacheTy) readStoreTy
abbrev retainedInputTy : Ty CryptoAtom := .pair coreInputTy metaTy
abbrev retainedOutputTy : Ty CryptoAtom := .pair coreOutputTy metaTy
abbrev outputTy : Ty CryptoAtom := .pair scalar stateTy

def setupValue {F G M : Type} [Zero F] (input : (M × G) × (F × F) × EncodedState F G M) :
    ((M × G) × EncodedEntry F × List ((M × G) × EncodedEntry F) × Unit) ×
      ReadStore F × Metadata F M :=
  ((input.1, (0, false, input.2.1), input.2.2.1, ()), (input.2.1, input.2.2.2.2.2.2), input.2.2.2)

/-- The retained pair is associated according to the actual cache-code boundary. -/
def packValue {F G M : Type} [Zero F] (input : (M × G) × (F × F) × EncodedState F G M) :=
  let p := setupValue input
  ((p.1, p.2.1), p.2.2)

def returnValue {F G M : Type}
    (input : ((EncodedEntry F × List ((M × G) × EncodedEntry F)) × ReadStore F) × Metadata F M) :
    F × EncodedState F G M :=
  (input.1.1.1.1, input.1.1.2, input.2.1, input.2.2.1, input.2.2.2.1, input.1.2.2)

def setupExpression : Expr CryptoOp [inputTy] retainedInputTy :=
  .letE (.op .zero .unit) <|
    let input : Expr CryptoOp [scalar, inputTy] inputTy := .var (.there .here)
    let state := Expr.snd (Expr.snd input)
    let metadata := Expr.snd state
    let fallback := Expr.pair (.var .here) (.pair (.bool false) (.fst (.snd input)))
    .pair
      (.pair (.pair (.fst input) (.pair fallback (.pair (.fst state) .unit)))
        (.pair (.fst (.snd input)) (.snd (.snd (.snd metadata)))))
      metadata

def returnExpression : Expr CryptoOp [retainedOutputTy] outputTy :=
  let input : Expr CryptoOp [retainedOutputTy] retainedOutputTy := .var .here
  let core := Expr.fst input
  let metadata := Expr.snd input
  .pair (.fst (.fst (.fst core)))
    (.pair (.snd (.fst core))
      (.pair (.fst metadata) (.pair (.fst (.snd metadata))
        (.pair (.fst (.snd (.snd metadata))) (.snd (.snd core))))))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem setupExpression_value (cost : PrimitiveCosts)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    setupExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = packValue input := rfl

theorem returnExpression_value (cost : PrimitiveCosts)
    (input : retainedOutputTy.Value (cryptoBase F G₁ G₂ K M)) :
    returnExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = returnValue input := rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def frame (input : Ty CryptoAtom) : Q.Realizer (rep.ty input) (rep.env [input]) (fun x => (x, ())) :=
  QP.pair (Q.identity _) (data.unit _)

def setup : Q.Realizer (rep.ty inputTy) (rep.ty retainedInputTy) packValue :=
  (Q.compose (frame rep data inputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive setupExpression)).castFunction
      (by funext input; exact setupExpression_value cost input)

def finish : Q.Realizer (rep.ty retainedOutputTy) (rep.ty outputTy) returnValue :=
  (Q.compose (frame rep data retainedOutputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive returnExpression)).castFunction
      (by funext input; exact returnExpression_value cost input)

variable {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def code : Code Q unifSpec iface (rep.ty inputTy) (rep.ty outputTy) :=
  .seq (.atomic (setup rep data cost primitive))
    (.seq (.first (rep.ty metaTy) (cacheAccess rep data cost primitive sampler))
      (.atomic (finish rep data cost primitive)))

theorem denote (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (code rep data cost primitive sampler).denote input =
      (fun r => returnValue (r, input.2.2.2)) <$>
        (cacheAccess rep data cost primitive sampler).denote (packValue input).1 := by
  simp only [code, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

/-- The entire read routine, including metadata restoration, realizes the
source read with the complete encoded result and updated state. -/
theorem source [SampleableType F] (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (s : State F G₁ M) (k : M × G₁) (a : Affine F) :
    (code rep data cost primitive sampler).denote (k, encodeAffine a, encodeState s) =
      (fun p => (p.1, encodeState p.2)) <$> (SchnorrAGM.read k a).run s := by
  rw [denote, ← cacheAccess_read rep data cost primitive sampler hsample s k a (0, false, encodeAffine a)]
  rfl

theorem hit_run (other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (e : EncodedEntry F)
    (hit : cacheMap input.2.2.1 input.1 = some e) :
    (code rep data cost primitive sampler).run control queryCost input =
      (code rep data cost primitive other).run control queryCost input := by
  have h := cacheAccess_hit_run rep data cost primitive sampler other control queryCost
    input.1 (0, false, input.2.1) input.2.2.1 (input.2.1, input.2.2.2.2.2.2) e hit
  simp only [code, Code.run, sequenceRun, retainRun, pure_bind, bind_map_left, packValue, setupValue]
  rw [h]

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    (code rep data cost primitive sampler).descriptionSize sizes ≤
      sampler.descriptionSize sizes + primitiveSize .messageEq + primitiveSize .point₁Eq +
        primitiveSize .add + 2 * primitiveSize .zero + primitiveSize .scalarEq + 800 * allowance + 50 := by
  have hframe (ty : Ty CryptoAtom) : sizes.localSize (frame rep data ty) ≤ 3 * allowance := by
    exact (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have hs : sizes.localSize (setup rep data cost primitive) ≤ primitiveSize .zero + 200 * allowance := by
    rw [setup, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe inputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes
        allowance laws dataLaws primitiveSize hp setupExpression)
    refine h.trans ?_
    simp only [setupExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hf : sizes.localSize (finish rep data cost primitive) ≤ 150 * allowance := by
    rw [finish, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe retainedOutputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes
        allowance laws dataLaws primitiveSize hp returnExpression)
    refine h.trans ?_
    simp only [returnExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hc := cacheAccess_description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp
  dsimp only [code, Code.descriptionSize]
  omega

end Signatures.Runtime.SchnorrAGM.Native.Read
