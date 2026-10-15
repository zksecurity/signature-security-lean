import Signatures.Runtime.BackendSchnorrAGMHashBudget
import Signatures.Runtime.BackendListSingleton
import Signatures.Runtime.SchnorrAGMExecution

/-! Native dispatch for arbitrary Schnorr AGM hash requests. Both incoming
lists are scanned before choosing the decoded hash or malformed-request path.
The latter returns zero, sets malformed, and makes no random draw. -/

open OracleComp OracleSpec PFunctor Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native.HashDispatch

open BackendProgram

abbrev inputTy : Ty CryptoAtom :=
  .pair message (.pair (.list point₁) (.pair (.list (.list scalar)) stateTy))
abbrev groupTy : Ty CryptoAtom := .pair .bool point₁
abbrev rowTy : Ty CryptoAtom := .pair .bool (.list scalar)
abbrev preparedTy : Ty CryptoAtom := .pair .bool Hash.inputTy

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))

def groupWith (scan : Expr CryptoOp [.list point₁, point₁, inputTy] groupTy) :
    Expr CryptoOp [inputTy] groupTy :=
  .letE (.op .zero₁ .unit) (.letE (.fst (.snd v1)) scan)

def rowWith (scan : Expr CryptoOp [.list (.list scalar), .list scalar, groupTy, inputTy] rowTy) :
    Expr CryptoOp [groupTy, inputTy] rowTy :=
  .letE .nil (.letE (.fst (.snd (.snd v2))) scan)

def prepareWith (groups : Expr CryptoOp [inputTy] groupTy)
    (rows : Expr CryptoOp [groupTy, inputTy] rowTy) : Expr CryptoOp [inputTy] preparedTy :=
  .letE groups (.letE rows
    (.pair (.branch (.fst v1) (.fst v0) (.bool false))
      (.pair (.pair (.fst v2) (.snd v1))
        (.pair (.snd v0) (.snd (.snd (.snd v2)))))))

def prepareExpression : Expr CryptoOp [inputTy] preparedTy :=
  prepareWith (groupWith ListSingleton.scan) (rowWith ListSingleton.scan)

def prepareValue {F G M : Type} [Zero G]
    (input : M × List G × List (List F) × EncodedState F G M) :
    Bool × (M × G) × List F × EncodedState F G M :=
  let group := ListSingleton.value (0 : G) input.2.1
  let row := ListSingleton.value ([] : List F) input.2.2.1
  (group.1 && row.1, (input.1, group.2), row.2, input.2.2.2)

def routeValue {F G M : Type} [Zero G]
    (input : M × List G × List (List F) × EncodedState F G M) :=
  let p := prepareValue input
  if p.1 = true then Sum.inl p.2 else Sum.inr p.2

def rejectValue {F G M : Type} [Zero F]
    (input : (M × G) × List F × EncodedState F G M) : F × EncodedState F G M :=
  (0, input.2.2.1, input.2.2.2.1, input.2.2.2.2.1, true, input.2.2.2.2.2.2)

def rejectExpression : Expr CryptoOp [Hash.inputTy] Read.outputTy :=
  .pair (.op .zero .unit)
    (let state := Expr.snd (Expr.snd v0)
     let metadata := Expr.snd state
     .pair (.fst state) (.pair (.fst metadata) (.pair (.fst (.snd metadata))
       (.pair (.bool true) (.snd (.snd (.snd metadata)))))))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem prepareExpression_value (cost : PrimitiveCosts)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    prepareExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = prepareValue input := by
  change ((if (ListSingleton.value (0 : G₁) input.2.1).1 = true then
      (ListSingleton.value ([] : List F) input.2.2.1).1 else false),
    (input.1, (ListSingleton.value (0 : G₁) input.2.1).2),
    (ListSingleton.value ([] : List F) input.2.2.1).2, input.2.2.2) = _
  dsimp only [prepareValue]
  cases (ListSingleton.value (0 : G₁) input.2.1).1 <;> rfl

theorem rejectExpression_value (cost : PrimitiveCosts)
    (input : Hash.inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    rejectExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = rejectValue input := rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def prepare : Q.Realizer (rep.ty inputTy) (rep.ty preparedTy) prepareValue :=
  (Q.compose (Read.frame rep data inputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive prepareExpression)).castFunction
      (by funext input; exact prepareExpression_value cost input)

def route : Q.Realizer (rep.ty inputTy) (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy))
    routeValue := Q.compose (prepare rep data cost primitive) (data.select (rep.ty Hash.inputTy))

def reject : Q.Realizer (rep.ty Hash.inputTy) (rep.ty Read.outputTy) rejectValue :=
  (Q.compose (Read.frame rep data Hash.inputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive rejectExpression)).castFunction
      (by funext input; exact rejectExpression_value cost input)

variable {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def code : Code Q unifSpec iface (rep.ty inputTy) (rep.ty Read.outputTy) :=
  .seq (.atomic (route rep data cost primitive))
    (.branch (Hash.code rep data cost primitive sampler) (.atomic (reject rep data cost primitive)))

theorem denote (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (code rep data cost primitive sampler).denote input =
      match input.2.1, input.2.2.1 with
      | [R], [coeff] => (Hash.code rep data cost primitive sampler).denote ((input.1, R), coeff, input.2.2.2)
      | _, _ => pure (0, input.2.2.2.1, input.2.2.2.2.1, input.2.2.2.2.2.1,
          true, input.2.2.2.2.2.2.2) := by
  rcases input with ⟨m, groups, rows, state⟩
  cases groups with
  | nil => simp [code, Code.denote, routeValue, prepareValue, rejectValue]
  | cons R gs =>
    cases gs with
    | cons R' gs => simp [code, Code.denote, routeValue, prepareValue, rejectValue, ListSingleton.value_multiple]
    | nil =>
      cases rows with
      | nil => simp [code, Code.denote, routeValue, prepareValue, rejectValue]
      | cons coeff cs =>
        cases cs with
        | nil => simp [code, Code.denote, routeValue, prepareValue]
        | cons coeff' cs => simp [code, Code.denote, routeValue, prepareValue, rejectValue, ListSingleton.value_multiple]

/-- Every hash-request shape preserves the actual histories. This also holds
for noncanonical encoded states and for rejected requests. -/
theorem histories_run (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    ∀ out ∈ support ((code rep data cost primitive sampler).run control queryCost input),
    out.value.2.2.1 = input.2.2.2.2.1 ∧ out.value.2.2.2.1 = input.2.2.2.2.2.1 := by
  intro out hout
  have h := Code.value_mem_denote control queryCost (code rep data cost primitive sampler) input out hout
  rw [denote] at h
  rcases input with ⟨m, groups, rows, state⟩
  rcases groups with _ | ⟨R, _ | ⟨R', gs⟩⟩
  · simp only [support_pure, Set.mem_singleton_iff] at h
    rw [h]
    exact ⟨rfl, rfl⟩
  · rcases rows with _ | ⟨coeff, _ | ⟨coeff', cs⟩⟩
    · simp only [support_pure, Set.mem_singleton_iff] at h
      rw [h]
      exact ⟨rfl, rfl⟩
    · dsimp only at h
      rw [Hash.denote, Read.denote] at h
      simp only [support_map, Set.mem_image] at h
      obtain ⟨r, _, hr⟩ := h
      rw [← hr]
      exact ⟨rfl, rfl⟩
    · simp only [support_pure, Set.mem_singleton_iff] at h
      rw [h]
      exact ⟨rfl, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at h
    rw [h]
    exact ⟨rfl, rfl⟩

/-- Malformed requests do not call even an arbitrary effectful scalar sampler. -/
theorem malformed_run (other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (invalid : (prepareValue input).1 = false) :
    (code rep data cost primitive sampler).run control queryCost input =
      (code rep data cost primitive other).run control queryCost input := by
  simp only [code, Code.run, sequenceRun, pure_bind, routeValue, invalid, Bool.false_eq_true, ↓reduceIte]

theorem source [SampleableType F] (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (g pk : G₁) (s : State F G₁ M) (m : M) (groups : List G₁) (rows : List (List F)) :
    (fun p => (scalarReply (G := G₁) p.1, p.2)) <$>
      (code rep data cost primitive sampler).denote (m, groups, rows, encodeState s) =
    (fun p => (p.1, encodeState p.2)) <$>
      (handler g pk ⟨⟨.hash m, fun _ => groups⟩, fun _ => rows⟩).run s := by
  rw [denote]
  cases groups with
  | nil => simp [handler, StateT.run, rejected, encodeState, encodeMetadata]; rfl
  | cons R gs =>
    cases gs with
    | cons R' gs => simp [handler, StateT.run, rejected, encodeState, encodeMetadata]; rfl
    | nil =>
      cases rows with
      | nil => simp [handler, StateT.run, rejected, encodeState, encodeMetadata]; rfl
      | cons coeff cs =>
        cases cs with
        | cons coeff' cs => simp [handler, StateT.run, rejected, encodeState, encodeMetadata]; rfl
        | nil =>
          simp only [handler, StateT.run]
          rw [Hash.source rep data cost primitive sampler hsample]
          simp only [bind_pure_comp, Functor.map_map]
          rfl

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    (code rep data cost primitive sampler).descriptionSize sizes ≤
      sampler.descriptionSize sizes + primitiveSize .messageEq + primitiveSize .point₁Eq +
        3 * primitiveSize .add + 4 * primitiveSize .zero + primitiveSize .zero₁ + primitiveSize .scalarEq +
        primitiveSize .natEq + primitiveSize .natSub + primitiveSize .natAdd +
        2 * primitiveSize .mul + 4000 * allowance + 80 := by
  have hframe (ty : Ty CryptoAtom) : sizes.localSize (Read.frame rep data ty) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have hprepare : sizes.localSize (prepare rep data cost primitive) ≤ primitiveSize .zero₁ + 1000 * allowance := by
    rw [prepare, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe inputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
        laws dataLaws primitiveSize hp prepareExpression)
    refine h.trans ?_
    simp only [prepareExpression, prepareWith, groupWith, rowWith, ListSingleton.scan, ListSingleton.body,
      Expression.descriptionBound, Expression.variableDescription]
    omega
  have hroute : sizes.localSize (route rep data cost primitive) ≤ primitiveSize .zero₁ + 1002 * allowance :=
    (laws.compose_bound hprepare (dataLaws.select (rep.ty Hash.inputTy))).trans (by omega)
  have hreject : sizes.localSize (reject rep data cost primitive) ≤ primitiveSize .zero + 256 * allowance := by
    rw [reject, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe Hash.inputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
        laws dataLaws primitiveSize hp rejectExpression)
    refine h.trans ?_
    simp only [rejectExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hhash := Hash.description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp
  dsimp only [code, Code.descriptionSize]
  omega

end Signatures.Runtime.SchnorrAGM.Native.HashDispatch
