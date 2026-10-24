import Proofs.Runtime.BackendSchnorrRawUniformSize

/-! Read the selected challenge from the raw saved tape. The fold stores a
counter, found flag and field value; it never constructs a prefix or enumerates
the numeric position. Missing entries remain distinguishable from field zero. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeLookup

open BackendProgram

abbrev inputTy : Ty CryptoAtom := .pair .nat (.list Replay.Mixed.event)
abbrev outputTy : Ty CryptoAtom := .pair .bool scalar
abbrev accTy : Ty CryptoAtom := .pair .nat outputTy

def step {F : Type} (acc : Nat × Bool × F) (cell : TapeCell F) : Nat × Bool × F :=
  if acc.2.1 then acc
  else if cell.1 = 1 then
    if acc.1 = 0 then (0, true, cell.2.1) else (acc.1 - 1, false, acc.2.2)
  else acc

def read {F : Type} : Nat → List (TapeCell F) → Option F
  | _, [] => none
  | n, cell :: cells =>
      if cell.1 = 1 then if n = 0 then some cell.2.1 else read (n - 1) cells
      else read n cells

def answer {F : Type} (fallback : F) : Option F → Bool × F
  | none => (false, fallback)
  | some f => (true, f)

theorem fold_found {F : Type} (cells : List (TapeCell F)) (n : Nat) (f : F) :
    cells.foldl step (n, true, f) = (n, true, f) := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => simpa [step] using ih

theorem fold_answer {F : Type} (cells : List (TapeCell F)) (n : Nat) (fallback : F) :
    (cells.foldl step (n, false, fallback)).2 = answer fallback (read n cells) := by
  induction cells generalizing n with
  | nil => rfl
  | cons cell cells ih =>
      by_cases tag : cell.1 = 1 <;> by_cases zero : n = 0 <;>
        simp [step, read, tag, zero, fold_found, answer, ih]

theorem read_values {F : Type} [Zero F] (n : Nat) (cells : List (TapeCell F)) :
    read n cells = (values (.inr ()) cells)[n]? := by
  induction cells generalizing n with
  | nil => rfl
  | cons cell cells ih =>
      by_cases tag : cell.1 = 1 <;> cases n <;>
        simp [read, values, SeedTape.values, SeedTape.familyTag, decodeReply, tag, ih]

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)

def body : Expr CryptoOp [Replay.Mixed.event, accTy, inputTy] accTy :=
  .branch (.fst (.snd v1)) v1
    (.branch (.op .natEq (.pair (.fst v0) (.nat 1)))
      (.branch (.op .natEq (.pair (.fst v1) (.nat 0)))
        (.pair (.nat 0) (.pair (.bool true) (.fst (.snd v0))))
        (.pair (.op .natSub (.pair (.fst v1) (.nat 1)))
          (.pair (.bool false) (.snd (.snd v1))))) v1)

def expression : Expr CryptoOp [inputTy] outputTy :=
  .letE (.fold (.snd v0) (.pair (.fst v0) (.pair (.bool false) (.op .zero .unit))) body)
    (.snd v0)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem body_value (cost : PrimitiveCosts) (cell : TapeCell F) (acc : Nat × Bool × F)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    body.denote (arithmetic F G₁ G₂ K M cost) (cell, acc, input, ()) = step acc cell := by
  cases found : acc.2.1 <;> by_cases tag : cell.1 = 1 <;> by_cases zero : acc.1 = 0 <;>
    simp [body, Expr.denote, Var.get, arithmetic, step, found, tag, zero]

theorem expression_value (cost : PrimitiveCosts)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    expression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) =
      answer (0 : F) (values (.inr ()) input.2)[input.1]? := by
  change (input.2.foldl (fun acc cell => body.denote (arithmetic F G₁ G₂ K M cost)
    (cell, acc, input, ())) (input.1, false, (0 : F))).2 = _
  simp_rw [body_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  rw [fold_answer, read_values]

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def compiled : Q.Realizer (rep.ty inputTy) (rep.ty outputTy)
    (fun input => answer (0 : F) (values (.inr ()) input.2)[input.1]?) :=
  (Q.compose (NativeUniform.frame rep data inputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive expression)).castFunction
      (by funext input; exact expression_value cost input)

def code {iface : Interface (C := C) unifSpec} :
    Code Q unifSpec iface (rep.ty inputTy) (rep.ty outputTy) :=
  .atomic (compiled rep data cost primitive)

theorem source {iface : Interface (C := C) unifSpec} (slot : Nat) (cells : List (TapeCell F)) :
    (code rep data cost primitive (iface := iface)).denote (slot, cells) =
      pure (answer (0 : F) (values (.inr ()) cells)[slot]?) := rfl

def descriptionBound (sizes : DescriptionSize Q) (allowance : Nat) : Nat :=
  Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) expression +
    4 * allowance + 1

theorem description {iface : Interface (C := C) unifSpec} (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (code rep data cost primitive (iface := iface)).descriptionSize sizes ≤
      descriptionBound rep cost primitive sizes allowance := by
  have framed : sizes.localSize (NativeUniform.frame rep data inputTy) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have compiledSize := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
    laws dataLaws (fun op => sizes.localSize (primitive op)) (fun _ => le_rfl) expression
  have h := laws.compose_bound framed compiledSize
  simp only [code, Code.descriptionSize, compiled, DescriptionSize.castFunction, descriptionBound]
  omega

end Signatures.Runtime.Schnorr.RawTape.NativeLookup
