import Proofs.Runtime.BackendSchnorrRawUniform

/-! Native challenge draws for the raw retained tape. A hit consumes the first
challenge cell; a miss executes the supplied scalar sampler and appends exactly
its field reply. Sampling is interpreted after raw tape handling, so private
uniform-family ordering is unchanged. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeChallenge

open BackendProgram

abbrev stateTy : Ty CryptoAtom := NativeUniform.stateTy
abbrev drawTy : Ty CryptoAtom := .pair scalar stateTy
abbrev prepareTy : Ty CryptoAtom := .pair .bool drawTy

def prepareValue {F : Type} [Zero F] (state : List (TapeCell F) × List (TapeCell F)) :=
  let scan := SeedTape.pop 1 (0, (0 : F), 0) state.2
  (scan.1, (scan.2.1.2.1, (state.1, if scan.1 then scan.2.2 else state.2)))

def saveValue {F : Type} (input : F × List (TapeCell F) × List (TapeCell F)) :=
  (input.1, (input.2.1 ++ [(1, input.1, 0)], input.2.2))

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))

def prepareExpression : Expr CryptoOp [stateTy] prepareTy :=
  .letE (.snd v0)
    (.letE (.nat 1)
      (.letE (SeedTape.popCode.weakenTail [stateTy])
        (.pair (.fst v0) (.pair (.fst (.snd (.fst (.snd v0))))
          (.pair (.fst v3) (.branch (.fst v0) (.snd (.snd v0)) (.snd v3)))))))

def saveExpression : Expr CryptoOp [drawTy] drawTy :=
  .letE (.fst (.snd v0))
    (.letE (.pair (.nat 1) (.pair (.fst v1) (.nat 0)))
      (.letE ListSnoc.expression (.pair (.fst v3) (.pair v0 (.snd (.snd v3))))))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem prepareExpression_value (cost : PrimitiveCosts)
    (state : stateTy.Value (cryptoBase F G₁ G₂ K M)) :
    prepareExpression.denote (arithmetic F G₁ G₂ K M cost) (state, ()) = prepareValue state := by
  have scan := (Expr.weakenTail_denote (Δ := [stateTy]) (arithmetic F G₁ G₂ K M cost)
    SeedTape.popCode (1, state.2, ()) (state, ())).trans (SeedTape.popCode_denote cost 1 state.2)
  simp only [Env.append] at scan
  simp only [prepareExpression, Expr.denote, Var.get, scan, prepareValue]

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

def prepare : Q.Realizer (rep.ty stateTy) (rep.ty prepareTy) prepareValue :=
  (Q.compose (NativeUniform.frame rep data stateTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive prepareExpression)).castFunction
      (by funext state; exact prepareExpression_value cost state)

def save : Q.Realizer (rep.ty drawTy) (rep.ty drawTy) saveValue :=
  (Q.compose (NativeUniform.frame rep data drawTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive saveExpression)).castFunction
      (by funext input; exact saveExpression_value cost input)

def choose : Q.Realizer (rep.ty stateTy) (StepClass.HasSum.sum (rep.ty drawTy) (rep.ty drawTy))
    (fun state => if (prepareValue state).1 then .inl (prepareValue state).2 else .inr (prepareValue state).2) :=
  Q.compose (prepare rep data cost primitive) (data.select (rep.ty drawTy))

def requestFrame : Q.Realizer (rep.ty drawTy)
    (StepClass.HasProd.prod rep.data.unit (rep.ty stateTy)) (fun input => ((), input.2)) :=
  QP.pair (data.unit _) (QP.snd (rep.ty scalar) (rep.ty stateTy))

variable {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def code : Code Q unifSpec iface (rep.ty stateTy) (rep.ty drawTy) :=
  .seq (.atomic (choose rep data cost primitive))
    (.branch (.atomic (Q.identity (rep.ty drawTy)))
      (.seq (.atomic (requestFrame rep data))
        (.seq (.first (rep.ty stateTy) sampler) (.atomic (save rep data cost primitive)))))

theorem denote (state : State F) :
    (code rep data cost primitive sampler).denote (NativeUniform.encodeState state) =
      let scan := SeedTape.pop 1 (0, (0 : F), 0) state.remaining
      if scan.1 then pure (scan.2.1.2.1, (state.saved, scan.2.2))
      else (fun answer => (answer, (state.saved ++ [(1, answer, 0)], state.remaining))) <$>
        sampler.denote () := by
  simp only [code, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  cases found : (SeedTape.pop 1 (0, (0 : F), 0) state.remaining).1 <;>
    simp [prepareValue, NativeUniform.encodeState, found, saveValue]

/-- The entire answer/state matches the raw challenge oracle after scalar
sampling is interpreted. No validity or private-family bound is required. -/
theorem source [SampleableType F]
    (sample : sampler.denote () = ($ᵗ F : ProbComp F)) (state : State F) :
    (code rep data cost primitive sampler).denote (NativeUniform.encodeState state) =
      (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
        simulateQ _root_.Schnorr.LazyROM.sample ((oracle (.inr ())).run state) := by
  rw [denote, sample]
  cases found : (SeedTape.pop 1 (0, (0 : F), 0) state.remaining).1 <;>
    simp [oracle, tag, family, SeedTape.familyTag, found, StateT.run,
      _root_.Schnorr.LazyROM.sample, encode, encodeReply, decode, decodeReply,
      NativeUniform.encodeState, Functor.map_map]

def descriptionBound (sizes : DescriptionSize Q) (allowance : Nat) : Nat :=
  Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) prepareExpression +
  Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) saveExpression +
  sampler.descriptionSize sizes + 14 * allowance + 9

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (code rep data cost primitive sampler).descriptionSize sizes ≤
      descriptionBound rep cost primitive sampler sizes allowance := by
  have frameSize (ty : Ty CryptoAtom) : sizes.localSize (NativeUniform.frame rep data ty) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have compiled {Γ a} (expression : Expr CryptoOp Γ a) :=
    Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
      laws dataLaws (fun op => sizes.localSize (primitive op)) (fun _ => le_rfl) expression
  have prep : sizes.localSize (prepare rep data cost primitive) ≤
      Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) prepareExpression +
        4 * allowance := by
    rw [prepare, DescriptionSize.castFunction]
    exact (laws.compose_bound (frameSize stateTy) (compiled prepareExpression)).trans (by omega)
  have saved : sizes.localSize (save rep data cost primitive) ≤
      Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) saveExpression +
        4 * allowance := by
    rw [save, DescriptionSize.castFunction]
    exact (laws.compose_bound (frameSize drawTy) (compiled saveExpression)).trans (by omega)
  have chosen := laws.compose_bound prep (dataLaws.select (rep.ty drawTy))
  change sizes.localSize (choose rep data cost primitive) ≤ _ at chosen
  have requested := laws.pair_bound (dataLaws.unit (rep.ty drawTy)) (laws.snd (rep.ty scalar) (rep.ty stateTy))
  change sizes.localSize (requestFrame rep data) ≤ _ at requested
  have returned := laws.identity (rep.ty drawTy)
  simp only [code, Code.descriptionSize, descriptionBound]
  omega

end Signatures.Runtime.Schnorr.RawTape.NativeChallenge
