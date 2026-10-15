import Signatures.Runtime.BackendSchnorrRawUniformSize

/-! Native reset of the raw retained tape. All private cells survive; only the
challenge family is trimmed. The resulting list is installed in both saved and
remaining state, with both copies included in the encoded-size invariant. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeReset

open BackendProgram

abbrev stateTy : Ty CryptoAtom := NativeUniform.stateTy
abbrev inputTy : Ty CryptoAtom := .pair .nat (.pair scalar stateTy)

def value {F : Type} (input : Nat × F × List (TapeCell F) × List (TapeCell F)) :=
  let tape := SeedTape.reset 1 input.1 (1, input.2.1, 0) input.2.2.1
  (tape, tape)

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))

def expression : Expr CryptoOp [inputTy] stateTy :=
  .letE (.pair (.nat 1) (.pair (.fst (.snd v0)) (.nat 0)))
    (.letE (.fst (.snd (.snd v1)))
      (.letE (.fst v2)
        (.letE (.nat 1)
          (.letE (SeedTape.resetCode.weakenTail [inputTy]) (.pair v0 v0)))))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem expression_value (cost : PrimitiveCosts)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    expression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = value input := by
  have reset := (Expr.weakenTail_denote (Δ := [inputTy]) (arithmetic F G₁ G₂ K M cost)
    SeedTape.resetCode (1, input.1, input.2.2.1, (1, input.2.1, 0), ()) (input, ())).trans
      (SeedTape.resetCode_denote cost 1 input.1 input.2.2.1 (1, input.2.1, 0))
  simp only [Env.append] at reset
  simp only [expression, Expr.denote, Var.get, reset, value]

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def compiled : Q.Realizer (rep.ty inputTy) (rep.ty stateTy) value :=
  (Q.compose (NativeUniform.frame rep data inputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive expression)).castFunction
      (by funext input; exact expression_value cost input)

def code {iface : Interface (C := C) unifSpec} :
    Code Q unifSpec iface (rep.ty inputTy) (rep.ty stateTy) :=
  .atomic (compiled rep data cost primitive)

theorem source {iface : Interface (C := C) unifSpec} (slot : Nat) (answer : F) (state : State F) :
    (code rep data cost primitive (iface := iface)).denote (slot, answer, NativeUniform.encodeState state) =
      pure (NativeUniform.encodeState (restart slot answer state)) := rfl

def descriptionBound (sizes : DescriptionSize Q) (allowance : Nat) : Nat :=
  Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) expression +
    4 * allowance + 1

theorem description {iface : Interface (C := C) unifSpec} (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (code rep data cost primitive (iface := iface)).descriptionSize sizes ≤
      descriptionBound rep cost primitive sizes allowance := by
  have frameSize : sizes.localSize (NativeUniform.frame rep data inputTy) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have compiledSize := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
    laws dataLaws (fun op => sizes.localSize (primitive op)) (fun _ => le_rfl) expression
  have h := laws.compose_bound frameSize compiledSize
  simp only [code, Code.descriptionSize, compiled, DescriptionSize.castFunction, descriptionBound]
  omega

end Signatures.Runtime.Schnorr.RawTape.NativeReset

namespace Signatures.Runtime.Schnorr.RawTape.NativeReset

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def InputBound (width savedCap remainingCap slotCap : Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  input.1 ≤ slotCap ∧ Q.size (rep.ty scalar) input.2.1 ≤ width ∧
    NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap input.2.2

theorem property (width savedCap remainingCap slotCap : Nat)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : InputBound (Q := Q) rep width savedCap remainingCap slotCap input) :
    NativeUniform.StateBound (Q := Q) rep width (savedCap + 1) (savedCap + 1) (value input) :=
  NativeUniform.restart_property rep width savedCap input.1 input.2.1
    ⟨input.2.2.1, input.2.2.2⟩ bound.2.2.1 ⟨hn1, bound.2.1, hn0⟩

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem input_size (width savedCap remainingCap slotCap : Nat) (hh : header ≤ width)
    (hn : ∀ n ≤ slotCap, Q.size rep.data.nat n ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : InputBound (Q := Q) rep width savedCap remainingCap slotCap input) :
    Q.size (rep.ty inputTy) input ≤ (6 * (savedCap + remainingCap) + 7) * width := by
  have hs := NativeUniform.state_size rep sizes lists width savedCap remainingCap hh input.2.2 bound.2.2
  have hf := bound.2.1
  have hi := hn input.1 bound.1
  have hp := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty, inputTy] at *
  grind only

theorem output_size (width savedCap remainingCap slotCap : Nat) (hh : header ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : InputBound (Q := Q) rep width savedCap remainingCap slotCap input) :
    Q.size (rep.ty stateTy) (value input) ≤ (12 * savedCap + 15) * width := by
  have h := NativeUniform.state_size rep sizes lists width (savedCap + 1) (savedCap + 1) hh (value input)
    (property rep width savedCap remainingCap slotCap hn0 hn1 input bound)
  nlinarith

end Signatures.Runtime.Schnorr.RawTape.NativeReset
