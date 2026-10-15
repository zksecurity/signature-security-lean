import Signatures.Runtime.BackendSchnorrROMSelectionComponentBudget

/-! Complete cost of the actual native selector on the empty/singleton outputs
of a bounded pass. Verification, lookup, guard, fold and input framing are charged. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeSelection

open BackendProgram RawTape

private def expressionWith
    (body : Expr CryptoOp [cachePassOutput, indexResult, NativePass.outputTy] indexResult) :
    Expr CryptoOp [NativePass.outputTy] indexResult :=
  .fold (.var .here) (.pair (.bool false) (.nat 0)) body

def frameWidth (width managedCap liveCap : Nat) : Nat := (32 * (managedCap + liveCap) + 128) * width

def timeBudget (overhead : Nat → Nat)
    (width managedCap liveCap scaleTime addTime messageTime pointTime incrementTime comparisonTime : Nat) : Nat :=
  let W := frameWidth width managedCap liveCap
  oneTime overhead W liveCap scaleTime addTime messageTime pointTime incrementTime comparisonTime +
    256 * overhead (512 * W)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes lists mono

private theorem expressionWith_time
    (body : Expr CryptoOp [cachePassOutput, indexResult, NativePass.outputTy] indexResult)
    (xs : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M)) (width bodyTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size rep.data.nat 0 ≤ width)
    (hi : Q.size (rep.ty NativePass.outputTy) xs ≤ width) (hlen : xs.length ≤ 1)
    (ho : ∀ p ∈ xs, Q.size (rep.ty indexResult)
      (body.denote (arithmetic F G₁ G₂ K M cost) (p, (false, 0), xs, ())) ≤ width)
    (hc : ∀ p ∈ xs, (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      body).time (p, (false, 0), xs, ()) ≤ bodyTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (expressionWith body)).time (xs, ()) ≤ bodyTime + 128 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hnil := lists.nil_le (rep.ty cachePassOutput)
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  cases xs with
  | nil =>
      dsimp only [expressionWith, Expression.compileBound, Expression.variableBound,
        LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.identity,
        DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound, DataCostLaws.natBound,
        foldWork, foldFee, List.foldl_nil, Expr.denote, Var.get, id,
        LanguageRepresentation.env, LanguageRepresentation.ty] at *
      grind only
  | cons p ps =>
      have ht : ps = [] := by simpa using hlen
      subst ps
      have hout := ho p (by simp)
      have hbody := hc p (by simp)
      clear ho hc
      dsimp only [expressionWith, Expression.compileBound, Expression.variableBound,
        LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.identity,
        DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound, DataCostLaws.natBound,
        foldWork, foldFee, List.foldl_cons, List.foldl_nil, Expr.denote, Var.get, id,
        LanguageRepresentation.env, LanguageRepresentation.ty] at *
      grind only

include laws dataLaws in
theorem selector_cost
    (xs : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M))
    (width managedCap liveCap qH scaleTime addTime messageTime pointTime incrementTime comparisonTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ max liveCap qH + 1, Q.size rep.data.nat n ≤ width)
    (bound : ∀ p ∈ xs, NativePass.CompletedBound (Q := Q) rep width managedCap liveCap p)
    (hlen : xs.length ≤ 1)
    (ops : Operations rep cost primitive primitiveBound width liveCap qH
      scaleTime addTime messageTime pointTime incrementTime comparisonTime) :
    Q.cost (selector rep data cost primitive qH) xs ≤
      timeBudget overhead width managedCap liveCap scaleTime addTime messageTime pointTime incrementTime comparisonTime := by
  let W := frameWidth width managedCap liveCap
  let one := oneTime overhead W liveCap scaleTime addTime messageTime pointTime incrementTime comparisonTime
  have hw : 8 * width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hp (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (member : p ∈ xs) :=
    NativePass.completed_size rep sizes lists width managedCap liveCap hh p (bound p member)
  have hlist := lists.size_le_cap (rep.ty cachePassOutput) xs ((12 * (managedCap + liveCap) + 17) * width) 1 hp hlen
  change Q.size (rep.ty NativePass.outputTy) xs ≤ _ at hlist
  have hin : Q.size (rep.ty NativePass.outputTy) xs ≤ W := by
    dsimp only [W, frameWidth]
    nlinarith only [hlist, hh]
  have hzero := choice_size rep sizes width 0 hh hb (fun n h => hn n (by omega)) (false, 0) (by simp)
  have hprod := @sizes.prod_le
  have hbody : ∀ p ∈ xs, (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (oneExpression (Γ := [indexResult, NativePass.outputTy]) qH)).time (p, (false, 0), xs, ()) ≤ one := by
    intro p member
    have hroot : Q.size (rep.env [cachePassOutput, indexResult, NativePass.outputTy])
        (p, (false, 0), xs, ()) ≤ W := by
      have hp' := hp p member
      simp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
      dsimp only [W, frameWidth]
      grind only
    exact oneExpression_time rep data cost primitive sizes lists laws dataLaws primitiveBound mono
      (Γ := [indexResult, NativePass.outputTy]) p ((false, 0), xs, ()) width W managedCap liveCap qH
      scaleTime addTime messageTime pointTime incrementTime comparisonTime hh hu hb hn hw hroot (bound p member) ops
  have houtput : ∀ p ∈ xs, Q.size (rep.ty indexResult)
      ((oneExpression (Γ := [indexResult, NativePass.outputTy]) qH).denote (arithmetic F G₁ G₂ K M cost)
        (p, (false, 0), xs, ())) ≤ W := by
    intro p _
    rw [oneExpression_denote]
    exact (choice_size rep sizes width qH hh hb (fun n h => hn n (by omega)) _ (oneValue_index_le qH p)).trans (by omega)
  have he := expressionWith_time rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    (oneExpression qH) xs W one (by omega) (by omega) (fun b => (hb b).trans (by omega))
    ((hn 0 (by omega)).trans (by omega)) hin hlen houtput hbody
  have hc := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    (expression qH) (xs, ())).trans he
  have hout : Q.size (rep.ty indexResult)
      ((expression qH).denote (arithmetic F G₁ G₂ K M cost) (xs, ())) ≤ 32 * W := by
    rw [expression_denote]
    exact (choice_size rep sizes width qH hh hb (fun n h => hn n (by omega)) _ (value_index_le qH xs)).trans (by omega)
  have hf := NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono (expression qH) xs W
    (one + 128 * overhead (256 * W)) (by omega) (by omega) hin hout hc
  rw [selector, QuantitativeStepClass.Realizer.cost_castFunction]
  change Q.cost (Q.compose (NativeUniform.frame rep data NativePass.outputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (expression qH))) xs ≤ _
  have hfee := mono (show 256 * W ≤ 512 * W by omega)
  change _ ≤ one + 256 * overhead (512 * W)
  omega

end Signatures.Runtime.Schnorr.ListROM.NativeSelection
