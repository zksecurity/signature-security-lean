import Signatures.Runtime.BackendSchnorrROMFork

/-! Native guarded extraction from the installed fork's list outputs. Empty
lists reject, singleton lists agree with the source extractor, and both failed
forks and failed extraction guards execute the original uniform fallback.
No default message or unrestricted representation adapter is needed. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeExtraction

open BackendProgram RawTape

abbrev inputTy : Ty CryptoAtom := .pair NativePass.outputTy NativePass.outputTy
abbrev resultTy : Ty CryptoAtom := .pair .bool scalar

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))

def guardExpression {Γ} (first second : Expr CryptoOp Γ cachePassOutput) : Expr CryptoOp Γ .bool :=
  .branch (.op .point₁Eq (.pair (.fst (.snd (.fst (.fst first)))) (.fst (.snd (.fst (.fst second))))))
    (.branch (.op .scalarEq (.pair (.snd (.fst first)) (.snd (.fst second)))) (.bool false) (.bool true))
    (.bool false)

def candidateExpression {Γ} (first second : Expr CryptoOp Γ cachePassOutput) : Expr CryptoOp Γ scalar :=
  .op .div (.pair
    (.op .sub (.pair (.snd (.snd (.fst (.fst first)))) (.snd (.snd (.fst (.fst second))))))
    (.op .sub (.pair (.snd (.fst first)) (.snd (.fst second)))))

def oneExpression {Γ} (first second : Expr CryptoOp Γ cachePassOutput) : Expr CryptoOp Γ resultTy :=
  .branch (guardExpression first second)
    (.pair (.bool true) (candidateExpression first second)) (.pair (.bool false) (.op .zero .unit))

def expression : Expr CryptoOp [inputTy] resultTy :=
  .fold (.fst v0) (.pair (.bool false) (.op .zero .unit))
    (.fold (.snd v2) (.pair (.bool false) (.op .zero .unit)) (oneExpression v2 v0))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

def oneValue (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) : Bool × F :=
  if first.1.1.2.1 = second.1.1.2.1 ∧ first.1.2 ≠ second.1.2 then
    (true, (first.1.1.2.2 - second.1.1.2.2) / (first.1.2 - second.1.2))
  else (false, 0)

def value (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) : Bool × F :=
  input.1.foldl (fun _ first => input.2.foldl (fun _ second => oneValue first second) (false, 0)) (false, 0)

theorem oneExpression_denote (cost : PrimitiveCosts) {Γ}
    (first second : Expr CryptoOp Γ cachePassOutput) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    (oneExpression first second).denote (arithmetic F G₁ G₂ K M cost) env =
      oneValue (first.denote (arithmetic F G₁ G₂ K M cost) env)
        (second.denote (arithmetic F G₁ G₂ K M cost) env) := by
  let p := first.denote (arithmetic F G₁ G₂ K M cost) env
  let q := second.denote (arithmetic F G₁ G₂ K M cost) env
  change (if (if decide (p.1.1.2.1 = q.1.1.2.1) then
      (if decide (p.1.2 = q.1.2) then false else true) else false) then
    (true, (p.1.1.2.2 - q.1.1.2.2) / (p.1.2 - q.1.2)) else (false, 0)) = oneValue p q
  by_cases hr : p.1.1.2.1 = q.1.1.2.1 <;> by_cases hc : p.1.2 = q.1.2 <;>
    simp [hr, hc, oneValue]

theorem expression_denote (cost : PrimitiveCosts)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    expression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = value input := by
  simp only [expression, Expr.denote, Var.get, oneExpression_denote]
  rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def checked : Code Q unifSpec iface (rep.ty inputTy) (rep.ty scalar) :=
  .seq (.atomic (NativeFork.chooseLocal rep data cost primitive expression))
    (.branch (.atomic (Q.identity (rep.ty scalar)))
      (.seq (.atomic (data.unit (rep.ty scalar))) sampler))

def code : Code Q unifSpec iface
    (StepClass.HasSum.sum rep.data.unit (rep.ty inputTy)) (rep.ty scalar) :=
  .branch sampler (checked rep data cost primitive sampler)

theorem checked_denote (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (checked rep data cost primitive sampler).denote input =
      if (value input).1 then pure (value input).2 else sampler.denote () := by
  simp only [checked, Code.denote, pure_bind]
  rw [expression_denote]
  by_cases h : (value input).1 = true <;> simp [h]

theorem code_denote (input : Unit ⊕ inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (code rep data cost primitive sampler).denote input =
      match input with
      | .inl _ => sampler.denote ()
      | .inr pair => if (value pair).1 then pure (value pair).2 else sampler.denote () := by
  cases input with
  | inl u => cases u; rfl
  | inr pair => exact checked_denote rep data cost primitive sampler pair

variable [SampleableType F] (sample : sampler.denote () = ($ᵗ F : ProbComp F))

include sample in
theorem source (result : Option (cachePassOutput.Value (cryptoBase F G₁ G₂ K M) ×
    cachePassOutput.Value (cryptoBase F G₁ G₂ K M))) :
    (code rep data cost primitive sampler).denote (NativeROMFork.output result) = extractFork result := by
  rw [code_denote]
  cases result with
  | none => exact sample
  | some pair =>
      simp only [NativeROMFork.output, NativeFork.view, Option.map_some, Prod.map, value,
        List.foldl_cons, List.foldl_nil, oneValue, extractFork, extractValues]
      split <;> simp_all

end Signatures.Runtime.Schnorr.ListROM.NativeExtraction
