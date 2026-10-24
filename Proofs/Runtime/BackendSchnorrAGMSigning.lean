import Proofs.Runtime.BackendListSnoc
import Proofs.Runtime.BackendSchnorrAGMProgramming
import Proofs.Runtime.BackendSchnorrAGMReadLocalCost
import Proofs.Runtime.BackendPairSampling
import Proofs.Runtime.SchnorrAGMExecution

/-! Native Schnorr AGM signing for an accepted request. Both scalar draws,
response arithmetic, chronological histories, cache programming and result
packing are executable code. This uses the internal generator/public-key/message/
state interface; request-shape dispatch and external reply encoding are separate. -/

open OracleComp OracleSpec PFunctor Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native.Signing

open BackendProgram

abbrev inputTy : Ty CryptoAtom := .pair point₁ (.pair point₁ (.pair message stateTy))
abbrev sampledTy : Ty CryptoAtom := .pair affineTy inputTy
abbrev replyTy : Ty CryptoAtom := .pair point₁ scalar
abbrev cacheArgsTy : Ty CryptoAtom := .pair cacheKeyTy (.pair entryTy (.pair cacheTy .unit))
abbrev workTy : Ty CryptoAtom := .pair cacheArgsTy (.pair replyTy (.pair affineTy (.pair message metaTy)))
abbrev savedTy : Ty CryptoAtom := .pair replyTy metaTy
abbrev programInputTy : Ty CryptoAtom := .pair cacheArgsTy savedTy
abbrev programOutputTy : Ty CryptoAtom := .pair cacheTy savedTy
abbrev outputTy : Ty CryptoAtom := .pair replyTy stateTy

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))
private abbrev v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
private abbrev v6 {a b c d e f g Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: g :: Γ) g :=
  .var (.there (.there (.there (.there (.there (.there .here))))))

def arithmeticExpression : Expr CryptoOp [sampledTy] workTy :=
  .letE (.op .zero .unit) <|
    .letE (.op .neg (.fst (.fst v1))) <|
      .letE
        (.op .sub₁ (.pair
          (.op .scale₁ (.pair (.snd (.fst v2)) (.fst (.snd v2))))
          (.op .scale₁ (.pair (.fst (.fst v2)) (.fst (.snd (.snd v2))))))) <|
        let input := Expr.snd v3
        let m := Expr.fst (Expr.snd (Expr.snd input))
        let state := Expr.snd (Expr.snd (Expr.snd input))
        .pair
          (.pair (.pair m v0)
            (.pair (.pair (.fst (.fst v3)) (.pair (.bool false) (.pair v2 v2)))
              (.pair (.fst state) .unit)))
          (.pair (.pair v0 (.snd (.fst v3)))
            (.pair (.pair (.snd (.fst v3)) v1) (.pair m (.snd state))))

def historiesWith
    (signed : Expr CryptoOp [message, .list message, workTy] (.list message))
    (basis : Expr CryptoOp [affineTy, .list affineTy, .list message, message, .list message, workTy]
      (.list affineTy)) : Expr CryptoOp [workTy] programInputTy :=
  .letE (.fst (.snd (.snd (.snd (.snd (.snd v0)))))) <|
    .letE (.fst (.snd (.snd (.snd v1)))) <|
      .letE signed <|
        .letE (.fst (.snd (.snd (.snd (.snd v3))))) <|
          .letE (.fst (.snd (.snd v4))) <|
            .letE basis <|
              .pair (.fst v6) (.pair (.fst (.snd v6))
                (.pair v0 (.pair v3 (.snd (.snd (.snd (.snd (.snd (.snd v6)))))))))

def historiesExpression : Expr CryptoOp [workTy] programInputTy :=
  historiesWith ListSnoc.expression ListSnoc.expression

def returnExpression : Expr CryptoOp [programOutputTy] outputTy :=
  .pair (.fst (.snd v0)) (.pair (.fst v0) (.snd (.snd v0)))

def arithmeticValue {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
    (input : (F × F) × G × G × M × EncodedState F G M) :=
  let c := input.1.1
  let z := input.1.2
  let R := z • input.2.1 - c • input.2.2.1
  let m := input.2.2.2.1
  let s := input.2.2.2.2
  (((m, R), (c, false, (0 : F), (0 : F)), s.1, ()), ((R, z), (z, -c), m, s.2))

def historiesValue {F G M : Type}
    (input : ((M × G) × EncodedEntry F × List ((M × G) × EncodedEntry F) × Unit) ×
      (G × F) × (F × F) × M × Metadata F M) :=
  (input.1, (input.2.1,
    input.2.2.2.2.1 ++ [input.2.2.1], input.2.2.2.2.2.1 ++ [input.2.2.2.1], input.2.2.2.2.2.2))

def returnValue {F G M : Type}
    (input : List ((M × G) × EncodedEntry F) × (G × F) × Metadata F M) :=
  (input.2.1, input.1, input.2.2)

def signedValue {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq G] [DecidableEq M]
    (input : (F × F) × G × G × M × EncodedState F G M) :=
  let p := historiesValue (arithmeticValue input)
  returnValue (CacheProgramming.value p.1.1 p.1.2.1 p.1.2.2.1, p.2)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem arithmeticExpression_value (cost : PrimitiveCosts)
    (input : sampledTy.Value (cryptoBase F G₁ G₂ K M)) :
    arithmeticExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = arithmeticValue input := rfl

theorem historiesExpression_value (cost : PrimitiveCosts)
    (input : workTy.Value (cryptoBase F G₁ G₂ K M)) :
    historiesExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = historiesValue input := by
  dsimp only [historiesExpression, historiesWith, Expr.denote, Var.get]
  rw [ListSnoc.denote, ListSnoc.denote]
  rfl

theorem returnExpression_value (cost : PrimitiveCosts)
    (input : programOutputTy.Value (cryptoBase F G₁ G₂ K M)) :
    returnExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = returnValue input := rfl

omit [DecidableEq F] in
theorem signedValue_source (s : State F G₁ M) (g pk : G₁) (m : M) (c z : F) :
    signedValue ((c, z), g, pk, m, encodeState s) =
      ((z • g - c • pk, z), encodeState (signedState s g pk m c z)) := by
  dsimp only [signedValue, arithmeticValue, historiesValue, returnValue, encodeState, encodeMetadata,
    CacheProgramming.value, signedState]
  rw [cacheMap_encode]
  cases cacheMap s.cache (m, z • g - c • pk) <;>
    simp [encodeEntry, encodeAffine, signingRepresentation]

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def prepare : Q.Realizer (rep.ty sampledTy) (rep.ty workTy) arithmeticValue :=
  (Q.compose (Read.frame rep data sampledTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive arithmeticExpression)).castFunction
      (by funext input; exact arithmeticExpression_value cost input)

def histories : Q.Realizer (rep.ty workTy) (rep.ty programInputTy) historiesValue :=
  (Q.compose (Read.frame rep data workTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive historiesExpression)).castFunction
      (by funext input; exact historiesExpression_value cost input)

def finish : Q.Realizer (rep.ty programOutputTy) (rep.ty outputTy) returnValue :=
  (Q.compose (Read.frame rep data programOutputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive returnExpression)).castFunction
      (by funext input; exact returnExpression_value cost input)

variable {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def sampledCode : Code Q unifSpec iface (rep.ty sampledTy) (rep.ty outputTy) :=
  .seq (.atomic (prepare rep data cost primitive))
    (.seq (.atomic (histories rep data cost primitive))
      (.seq (.first (rep.ty savedTy) (Programming.code rep data cost primitive))
        (.atomic (finish rep data cost primitive))))

def sampleFrame : Q.Realizer (rep.ty inputTy) (StepClass.HasProd.prod rep.data.unit (rep.ty inputTy))
    (fun input => ((), input)) := QP.pair (data.unit _) (Q.identity _)

def code : Code Q unifSpec iface (rep.ty inputTy) (rep.ty outputTy) :=
  .seq (.atomic (sampleFrame rep data))
    (.seq (.first (rep.ty inputTy)
      (PairSampling.code rep.data data (rep.ty scalar) (rep.ty scalar) sampler sampler))
      (sampledCode rep data cost primitive))

theorem sampledCode_denote (input : sampledTy.Value (cryptoBase F G₁ G₂ K M)) :
    (sampledCode rep data cost primitive (iface := iface)).denote input = pure (signedValue input) := by
  simp only [sampledCode, Code.denote, pure_bind, historiesValue, arithmeticValue]
  rw [Programming.denote rep data cost primitive]
  simp only [map_pure, pure_bind]
  rfl

theorem denote (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (code rep data cost primitive sampler).denote input = (do
      let c ← sampler.denote ()
      let z ← sampler.denote ()
      pure (signedValue ((c, z), input))) := by
  simp only [code, Code.denote, pure_bind, bind_map_left,
    PairSampling.denote, bind_assoc]
  congr 1
  funext c
  congr 1
  funext z
  exact sampledCode_denote rep data cost primitive ((c, z), input)

/-- Exact accepted-signing source behavior, including both draws on collisions.
The external signing reply is only the observation map in this theorem. -/
theorem source [SampleableType F] (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (s : State F G₁ M) (g pk : G₁) (m : M) (coeff : List (List F)) :
    (fun p => (signingReply p.1.1 p.1.2, p.2)) <$>
        (code rep data cost primitive sampler).denote (g, pk, m, encodeState s) =
      (fun p => (p.1, encodeState p.2)) <$>
        (handler g pk ⟨⟨.sign m, fun _ => []⟩, fun _ => coeff⟩).run s := by
  rw [denote]
  simp only [hsample, map_bind, map_pure, signedValue_source, handler, StateT.run,
    ne_eq, not_true_eq_false, ite_false]
  rfl

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    (code rep data cost primitive sampler).descriptionSize sizes ≤
      2 * sampler.descriptionSize sizes + primitiveSize .zero + primitiveSize .neg +
        2 * primitiveSize .scale₁ + primitiveSize .sub₁ + primitiveSize .messageEq + primitiveSize .point₁Eq +
        2048 * allowance + 32 := by
  have hframe (ty : Ty CryptoAtom) : sizes.localSize (Read.frame rep data ty) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have ha : sizes.localSize (prepare rep data cost primitive) ≤
      primitiveSize .zero + primitiveSize .neg + 2 * primitiveSize .scale₁ + primitiveSize .sub₁ +
        512 * allowance := by
    rw [prepare, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe sampledTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
        laws dataLaws primitiveSize hp arithmeticExpression)
    refine h.trans ?_
    simp only [arithmeticExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hh : sizes.localSize (histories rep data cost primitive) ≤ 1024 * allowance := by
    rw [histories, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe workTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
        laws dataLaws primitiveSize hp historiesExpression)
    refine h.trans ?_
    simp only [historiesExpression, historiesWith, ListSnoc.expression, ListSnoc.withReversals,
      reverseList, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hf : sizes.localSize (finish rep data cost primitive) ≤ 128 * allowance := by
    rw [finish, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe programOutputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
        laws dataLaws primitiveSize hp returnExpression)
    refine h.trans ?_
    simp only [returnExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hc := Programming.description rep data cost primitive (iface := iface) sizes allowance laws dataLaws primitiveSize hp
  have hs := PairSampling.description rep.data data (rep.ty scalar) (rep.ty scalar) sampler sampler sizes allowance laws dataLaws
  have hp' : sizes.localSize (sampleFrame rep data) ≤ 3 * allowance :=
    (laws.pair_bound (dataLaws.unit _) (laws.identity _)).trans (by omega)
  dsimp only [code, sampledCode, Code.descriptionSize]
  omega

end Signatures.Runtime.SchnorrAGM.Native.Signing
