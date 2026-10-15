import Signatures.Runtime.SchnorrRawTapeValid
import Signatures.Runtime.BackendUniformSampling
import Signatures.Runtime.BackendExpressionSize
import Signatures.Runtime.Weakening
import Signatures.Runtime.ListSnoc

/-! Native dynamic private draws for Schnorr's raw retained tape. The arity
is data: code computes its tag, scans actual cells, and either returns the saved
natural or makes one dynamic uniform query and appends its reply. No arity-sized
decoder or sampler dispatch is generated. Native runtime bounds are separate. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeUniform

open BackendProgram

abbrev stateTy : Ty CryptoAtom := .pair (.list Replay.Mixed.event) (.list Replay.Mixed.event)
abbrev inputTy : Ty CryptoAtom := .pair .nat stateTy
abbrev auxTy : Ty CryptoAtom := .pair .nat stateTy
abbrev drawTy : Ty CryptoAtom := .pair .nat auxTy
abbrev prepareTy : Ty CryptoAtom := .pair .bool drawTy

def encodeState {F : Type} (state : State F) : List (TapeCell F) × List (TapeCell F) :=
  (state.saved, state.remaining)

def prepareValue {F : Type} [Zero F] (input : Nat × List (TapeCell F) × List (TapeCell F)) :=
  let scan := SeedTape.pop (input.1 + 2) (0, (0 : F), 0) input.2.2
  (scan.1, (if scan.1 then scan.2.1.2.2 else input.1,
    (input.1 + 2, (input.2.1, if scan.1 then scan.2.2 else input.2.2))))

def hitValue {F : Type} (input : Nat × Nat × List (TapeCell F) × List (TapeCell F)) :=
  (input.1, input.2.2)

def saveValue {F : Type} [Zero F] (input : Nat × Nat × List (TapeCell F) × List (TapeCell F)) :=
  (input.1, (input.2.2.1 ++ [(input.2.1, (0 : F), input.1)], input.2.2.2))

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))

def prepareExpression : Expr CryptoOp [inputTy] prepareTy :=
  .letE (.snd (.snd v0))
    (.letE (.op .natAdd (.pair (.fst v1) (.nat 2)))
      (.letE (SeedTape.popCode.weakenTail [inputTy])
        (.pair (.fst v0)
          (.pair (.branch (.fst v0) (.snd (.snd (.fst (.snd v0)))) (.fst v3))
            (.pair v1 (.pair (.fst (.snd v3))
              (.branch (.fst v0) (.snd (.snd v0)) (.snd (.snd v3)))))))))

def hitExpression : Expr CryptoOp [drawTy] inputTy :=
  .pair (.fst v0) (.snd (.snd v0))

def saveExpression : Expr CryptoOp [drawTy] inputTy :=
  .letE (.fst (.snd (.snd v0)))
    (.letE (.pair (.fst (.snd v1)) (.pair (.op .zero .unit) (.fst v1)))
      (.letE ListSnoc.expression
        (.pair (.fst v3) (.pair v0 (.snd (.snd (.snd v3)))))))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem prepareExpression_value (cost : PrimitiveCosts)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    prepareExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = prepareValue input := by
  have scan := (Expr.weakenTail_denote (Δ := [inputTy])
    (arithmetic F G₁ G₂ K M cost) SeedTape.popCode
    (input.1 + 2, input.2.2, ()) (input, ())).trans
      (SeedTape.popCode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
        cost (input.1 + 2) input.2.2)
  simp only [Env.append] at scan
  have add : (arithmetic F G₁ G₂ K M cost).execute .natAdd (input.1, 2) = input.1 + 2 := rfl
  simp only [prepareExpression, Expr.denote, Var.get, add, scan, prepareValue]

theorem hitExpression_value (cost : PrimitiveCosts)
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M)) :
    hitExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = hitValue input := rfl

theorem saveExpression_value (cost : PrimitiveCosts)
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M)) :
    saveExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = saveValue input := by
  dsimp only [saveExpression, Expr.denote, Var.get]
  rw [ListSnoc.denote]
  rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def frame (input : Ty CryptoAtom) :
    Q.Realizer (rep.ty input) (rep.env [input]) (fun x => (x, ())) :=
  QP.pair (Q.identity _) (data.unit _)

def prepare : Q.Realizer (rep.ty inputTy) (rep.ty prepareTy) prepareValue :=
  (Q.compose (frame rep data inputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive prepareExpression)).castFunction
      (by funext input; exact prepareExpression_value cost input)

def hit : Q.Realizer (rep.ty drawTy) (rep.ty inputTy) hitValue :=
  (Q.compose (frame rep data drawTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive hitExpression)).castFunction
      (by funext input; exact hitExpression_value cost input)

def save : Q.Realizer (rep.ty drawTy) (rep.ty inputTy) saveValue :=
  (Q.compose (frame rep data drawTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive saveExpression)).castFunction
      (by funext input; exact saveExpression_value cost input)

def choose : Q.Realizer (rep.ty inputTy) (StepClass.HasSum.sum (rep.ty drawTy) (rep.ty drawTy))
    (fun input => if (prepareValue input).1 then .inl (prepareValue input).2
      else .inr (prepareValue input).2) :=
  Q.compose (prepare rep data cost primitive) (data.select (rep.ty drawTy))

variable {iface : Interface (C := C) unifSpec}
  (ports : UniformSampling.Ports (Q := Q) rep.data (iface := iface))

def code : Code Q unifSpec iface (rep.ty inputTy) (rep.ty inputTy) :=
  .seq (.atomic (choose rep data cost primitive))
    (.branch (.atomic (hit rep data cost primitive))
      (.seq (.first (rep.ty auxTy) (UniformSampling.code rep.data ports))
        (.atomic (save rep data cost primitive))))

theorem denote (n : Nat) (state : State F) :
    (code rep data cost primitive ports).denote (n, encodeState state) =
      let scan := SeedTape.pop (n + 2) (0, (0 : F), 0) state.remaining
      if scan.1 then pure (scan.2.1.2.2, (state.saved, scan.2.2))
      else (fun answer : Fin (n + 1) =>
        (answer.val, (state.saved ++ [(n + 2, (0 : F), answer.val)], state.remaining))) <$>
          (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp only [code, Code.denote, pure_bind, UniformSampling.denote, bind_pure_comp, Functor.map_map]
  cases found : (SeedTape.pop (n + 2) (0, (0 : F), 0) state.remaining).1 <;>
    simp [prepareValue, encodeState, found, hitValue, saveValue]

/-- On a valid retained tape, the native draw realizes the raw seeded reply
and the entire saved/remaining state. All fresh draws are appended in order. -/
theorem source [SampleableType F] (n : Nat) (state : State F)
    (valid : Valid state.remaining) :
    (code rep data cost primitive ports).denote (n, encodeState state) =
      (fun p => (p.1.val, encodeState p.2)) <$>
        simulateQ _root_.Schnorr.LazyROM.sample ((oracle (.inl n)).run state) := by
  rw [denote]
  have scan := pop_valid (n + 2) state.remaining valid
  cases found : (SeedTape.pop (n + 2) (0, (0 : F), 0) state.remaining).1 with
  | false =>
      simp [oracle, tag, family, SeedTape.familyTag, found, StateT.run,
        _root_.Schnorr.LazyROM.sample, encode, encodeReply,
        encodeState, Functor.map_map]
  | true =>
      have hdecode := decode_uniform_val n _ (scan.2 found).1 (scan.2 found).2
      simp [oracle, tag, family, SeedTape.familyTag, found, StateT.run,
        encodeState, hdecode]

/-- A static bound assembled from the three fixed expression bodies and two
uniform-interface adapters. It contains no input arity or tape length. -/
def descriptionBound (sizes : DescriptionSize Q) (allowance : Nat) : Nat :=
  Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) prepareExpression +
  Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) hitExpression +
  Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) saveExpression +
  sizes.localSize ports.request + sizes.localSize ports.response + 14 * allowance + 12

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (code rep data cost primitive ports).descriptionSize sizes ≤
      descriptionBound rep cost primitive ports sizes allowance := by
  have frameSize (ty : Ty CryptoAtom) : sizes.localSize (frame rep data ty) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have compiled {Γ a} (expression : Expr CryptoOp Γ a) :=
    Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
      laws dataLaws (fun op => sizes.localSize (primitive op)) (fun _ => le_rfl) expression
  have prep : sizes.localSize (prepare rep data cost primitive) ≤
      Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) prepareExpression +
        4 * allowance := by
    rw [prepare, DescriptionSize.castFunction]
    exact (laws.compose_bound (frameSize inputTy) (compiled prepareExpression)).trans (by omega)
  have hitSize : sizes.localSize (hit rep data cost primitive) ≤
      Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) hitExpression +
        4 * allowance := by
    rw [hit, DescriptionSize.castFunction]
    exact (laws.compose_bound (frameSize drawTy) (compiled hitExpression)).trans (by omega)
  have saveSize : sizes.localSize (save rep data cost primitive) ≤
      Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) saveExpression +
        4 * allowance := by
    rw [save, DescriptionSize.castFunction]
    exact (laws.compose_bound (frameSize drawTy) (compiled saveExpression)).trans (by omega)
  have chooseSize := laws.compose_bound prep (dataLaws.select (rep.ty drawTy))
  change sizes.localSize (choose rep data cost primitive) ≤ _ at chooseSize
  simp only [code, Code.descriptionSize, UniformSampling.description]
  dsimp only [descriptionBound]
  omega

end Signatures.Runtime.Schnorr.RawTape.NativeUniform
