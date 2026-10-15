import Signatures.Runtime.BackendSchnorrROMExtractionFoldCost
import Signatures.Runtime.BackendSchnorrROMForkBudget

/-! Complete local extraction cost on bounded fork outputs. Both nested folds
and the frame/selection adapters are derived from original primitive contracts. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeExtraction

open BackendProgram RawTape

def frameWidth (width managedCap liveCap : Nat) : Nat :=
  (128 * (managedCap + liveCap) + 512) * width

def localTime (overhead : Nat → Nat)
    (width managedCap liveCap pointTime scalarTime subTime divTime zeroTime : Nat) : Nat :=
  pointTime + scalarTime + 2 * subTime + divTime + 3 * zeroTime +
    2048 * overhead (512 * frameWidth width managedCap liveCap)

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

include sizes in
omit [Q.HasCategory] QP QS in
theorem value_scalar (width managedCap liveCap pointTime scalarTime subTime divTime zeroTime : Nat)
    (xs ys : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M))
    (hx : NativeROMFork.ValidOutput (Q := Q) rep width managedCap liveCap xs)
    (hy : NativeROMFork.ValidOutput (Q := Q) rep width managedCap liveCap ys)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (ops : Operations rep cost primitive primitiveBound width pointTime scalarTime subTime divTime zeroTime) :
    Q.size (rep.ty scalar) (value (xs, ys)).2 ≤ 3 * width := by
  cases xs with
  | nil => exact hz.trans (by omega)
  | cons first tail =>
      have ht : tail = [] := by simpa using hx.2
      subst tail
      cases ys with
      | nil => exact hz.trans (by omega)
      | cons second rest =>
          have hr : rest = [] := by simpa using hy.2
          subst rest
          exact oneValue_scalar rep cost primitive sizes primitiveBound width managedCap liveCap
            pointTime scalarTime subTime divTime zeroTime first second
            (hx.1 first (by simp)) (hy.1 second (by simp)) hz ops

include sizes lists laws dataLaws mono

theorem expression_cost
    (xs ys : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M))
    (width managedCap liveCap pointTime scalarTime subTime divTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hx : NativeROMFork.ValidOutput (Q := Q) rep width managedCap liveCap xs)
    (hy : NativeROMFork.ValidOutput (Q := Q) rep width managedCap liveCap ys)
    (ops : Operations rep cost primitive primitiveBound width pointTime scalarTime subTime divTime zeroTime) :
    Q.cost (NativeFork.chooseLocal rep data cost primitive expression) (xs, ys) ≤
      localTime overhead width managedCap liveCap pointTime scalarTime subTime divTime zeroTime := by
  let W := frameWidth width managedCap liveCap
  let one := oneTime overhead W pointTime scalarTime subTime divTime zeroTime
  have hw : 8 * width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hprod := @sizes.prod_le
  have hxs := NativeROMFork.output_size rep sizes lists width managedCap liveCap hh xs hx
  have hys := NativeROMFork.output_size rep sizes lists width managedCap liveCap hh ys hy
  have hp (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
      (h : NativePass.CompletedBound (Q := Q) rep width managedCap liveCap p) :=
    NativePass.completed_size rep sizes lists width managedCap liveCap hh p h
  have hzero : Q.size (rep.ty resultTy) (false, (0 : F)) ≤ 3 * width := by
    have h := sizes.prod_le rep.data.bool (rep.ty scalar) (false, (0 : F))
    have hf := hb false
    change Q.size (rep.ty resultTy) _ ≤ _ at h
    dsimp only at h
    omega
  have hi : Q.size (rep.ty inputTy) (xs, ys) ≤ W := by
    dsimp only [W, frameWidth, NativeROMFork.controllerWidth] at *
    simp only [LanguageRepresentation.ty] at *
    grind only
  have hroot (first) (hf : first ∈ xs) :
      Q.size (rep.env [cachePassOutput, resultTy, inputTy]) (first, (false, (0 : F)), (xs, ys), ()) ≤ W := by
    have hfirst := hp first (hx.1 first hf)
    dsimp only [W, frameWidth, NativeROMFork.controllerWidth] at *
    simp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have hbodyRoot (first second) (hf : first ∈ xs) (hs : second ∈ ys) :
      Q.size (rep.env (bodyTypes [resultTy, inputTy]))
        (second, (false, (0 : F)), first, (false, (0 : F)), (xs, ys), ()) ≤ W := by
    have hfirst := hp first (hx.1 first hf)
    have hsecond := hp second (hy.1 second hs)
    dsimp only [W, frameWidth, NativeROMFork.controllerWidth, bodyTypes] at *
    simp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have hbody (first second) (hf : first ∈ xs) (hs : second ∈ ys) :
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
        (body (Γ := [resultTy, inputTy]))).time
          (second, (false, 0), first, (false, 0), (xs, ys), ()) ≤ one :=
    body_time rep data cost primitive sizes laws dataLaws primitiveBound mono (Γ := [resultTy, inputTy]) first second (false, 0)
      ((false, 0), (xs, ys), ()) width W managedCap liveCap pointTime scalarTime subTime divTime zeroTime
      hh hu hb hz hw (hbodyRoot first second hf hs) (hx.1 first hf) (hy.1 second hs) ops
  have hbodySize (first second) (hf : first ∈ xs) (hs : second ∈ ys) :
      Q.size (rep.ty resultTy) ((body (Γ := [resultTy, inputTy])).denote (arithmetic F G₁ G₂ K M cost)
        (second, (false, 0), first, (false, 0), (xs, ys), ())) ≤ W := by
    simp only [body, oneExpression_denote, Expr.denote, Var.get]
    exact (oneValue_size rep cost primitive sizes primitiveBound width managedCap liveCap
      pointTime scalarTime subTime divTime zeroTime first second (hx.1 first hf) (hy.1 second hs) hh hb hz ops).trans (by omega)
  have hinnerValue (first : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) :
      (innerWith body).denote (arithmetic F G₁ G₂ K M cost) (first, (false, 0), (xs, ys), ()) =
        ys.foldl (fun _ second => oneValue first second) (false, 0) := by
    simp only [innerWith, Expr.denote, Var.get, body, oneExpression_denote]
    rfl
  have hinnerSize (first) (hf : first ∈ xs) :
      Q.size (rep.ty resultTy) ((innerWith body).denote (arithmetic F G₁ G₂ K M cost)
        (first, (false, 0), (xs, ys), ())) ≤ W := by
    rw [hinnerValue]
    cases ys with
    | nil => exact hzero.trans (by omega)
    | cons second rest =>
        have hr : rest = [] := by simpa using hy.2
        subst rest
        exact (oneValue_size rep cost primitive sizes primitiveBound width managedCap liveCap
          pointTime scalarTime subTime divTime zeroTime first second (hx.1 first hf)
          (hy.1 second (by simp)) hh hb hz ops).trans (by omega)
  have hinner (first) (hf : first ∈ xs) := innerWith_time rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    body first (false, 0) xs ys W one zeroTime (by omega) (by omega) (fun b => (hb b).trans (by omega))
    (by omega) (hroot first hf) hy.2 ops.zero (fun second hs => hbodySize first second hf hs)
    (fun second hs => hbody first second hf hs)
  have he := outerWith_time rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    (innerWith body) xs ys W (zeroTime + one + 128 * overhead (256 * W)) zeroTime
    (by omega) (by omega) (fun b => (hb b).trans (by omega)) (by omega) hi hx.2 ops.zero hinnerSize hinner
  have hout : Q.size (rep.ty resultTy) (expression.denote (arithmetic F G₁ G₂ K M cost) ((xs, ys), ())) ≤ W := by
    rw [expression_denote]
    have hs := value_scalar rep cost primitive sizes primitiveBound width managedCap liveCap
      pointTime scalarTime subTime divTime zeroTime xs ys hx hy hz ops
    have hbool := hb (value (xs, ys)).1
    have h := sizes.prod_le rep.data.bool (rep.ty scalar) (value (xs, ys))
    change Q.size (rep.ty resultTy) _ ≤ _ at h
    omega
  have hc := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    expression ((xs, ys), ())).trans he
  have framed := NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono expression (xs, ys) W _
    (by omega) (by omega) hi (hout.trans (by omega)) hc
  have selected := NativeFork.chooseLocal_cost rep data cost primitive sizes laws dataLaws mono expression
    (xs, ys) W _ (by omega) hi hout framed
  have hm := mono (show 256 * W ≤ 512 * W by omega)
  dsimp only [W] at hm
  exact selected.trans (by dsimp only [localTime, one, oneTime, W]; omega)

end Signatures.Runtime.Schnorr.ListROM.NativeExtraction
