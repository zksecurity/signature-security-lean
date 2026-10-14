import Signatures.Runtime.BackendIndexCost
import Signatures.Runtime.WeightedEvaluate

/-! Cost of the evaluator's actual row-selection expression. The positional
lookup scans all rows and retains the enclosing evaluator frame. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Evaluate

open BackendProgram LazyAGM.ReplySyntax

private def selectWith {indexTy value : Ty CryptoAtom}
    (lookup : Expr CryptoOp [.nat, (evalRowTy indexTy), .list (evalRowTy indexTy),
      evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)] (evalRowTy indexTy)) :
    Expr CryptoOp [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)] (evalRowTy indexTy) :=
  .letE v1 (.letE v3 (.letE (.fst v2) lookup))

variable {indexTy : Ty CryptoAtom}

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
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

include sizes mono

private theorem selectWith_time {value : Ty CryptoAtom}
    (lookup : Expr CryptoOp [.nat, (evalRowTy indexTy), .list (evalRowTy indexTy),
      evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)] (evalRowTy indexTy))
    (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ K M))
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (width lookupTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)])
      ((n, acc), rows, default, ()) ≤ width)
    (ho : Q.size (rep.ty (evalRowTy indexTy))
      (lookup.denote (arithmetic F G₁ G₂ K M cost) (n, default, rows, (n, acc), rows, default, ())) ≤ width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound lookup).time (n, default, rows, (n, acc), rows, default, ()) ≤ lookupTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (selectWith lookup)).time ((n, acc), rows, default, ()) ≤
        lookupTime + 32 * overhead (128 * width) := by
  have hp := @sizes.prod_le
  have hf := @sizes.fst_le
  have hs := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [selectWith, v1, v2, v3, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    Expr.denote, Var.get, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

theorem selectRow_time_bound {value : Ty CryptoAtom}
    (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ K M))
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (width cap comparisonTime subtractTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)])
      ((n, acc), rows, default, ()) ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ n + 1, Q.size rep.data.nat k ≤ width)
    (hd : Q.size (rep.ty (evalRowTy indexTy)) default ≤ width)
    (hr : ∀ row ∈ rows, Q.size (rep.ty (evalRowTy indexTy)) row ≤ width)
    (hc : rows.length ≤ cap)
    (hl : ∀ xs : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F), xs.length ≤ cap → (∀ x ∈ xs, x ∈ rows) →
      Q.size (rep.ty (.list (evalRowTy indexTy))) xs ≤ width)
    (he : ∀ k ≤ n, (primitiveBound CryptoOp.natEq).time (k, 0) ≤ comparisonTime)
    (hs : ∀ k ≤ n, (primitiveBound CryptoOp.natSub).time (k, 1) ≤ subtractTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (selectRow (value := value))).time ((n, acc), rows, default, ()) ≤
        cap * (comparisonTime + subtractTime + 257 * overhead (128 * width)) +
          96 * overhead (128 * width) := by
  let lookup := (index (cell := (evalRowTy indexTy)) CryptoOp.natEq CryptoOp.natSub).weakenTail
    [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)]
  have ht := IndexCompiler.index_time_bound_of_caps rep data (arithmetic F G₁ G₂ K M cost)
    primitive laws dataLaws primitiveBound sizes mono (cell := (evalRowTy indexTy))
    (Γ := [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)]) CryptoOp.natEq CryptoOp.natSub
    (fun _ _ => rfl) (fun _ _ => rfl) n default rows ((n, acc), rows, default, ())
    width comparisonTime subtractTime cap hh hu hi hb (fun k hk => hn k (by omega))
    (hn 1 (by omega)) hd hr hc hl he hs
  have ho : Q.size (rep.ty (evalRowTy indexTy))
      (lookup.denote (arithmetic F G₁ G₂ K M cost) (n, default, rows, (n, acc), rows, default, ())) ≤ width := by
    have hw := (index (cell := (evalRowTy indexTy)) CryptoOp.natEq CryptoOp.natSub).weakenTail_denote
      (Δ := [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)]) (arithmetic F G₁ G₂ K M cost)
      (n, default, rows, ()) ((n, acc), rows, default, ())
    simp only [Env.append] at hw
    rw [hw, index_denote _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)]
    cases hx : rows[n]? with
    | none => simpa using hd
    | some row => exact hr row (List.mem_of_getElem? hx)
  have h := selectWith_time rep data cost primitive laws dataLaws primitiveBound sizes mono
    lookup n acc rows default width
    (cap * (comparisonTime + subtractTime + 257 * overhead (128 * width)) +
      64 * overhead (128 * width)) hh hi ho ht
  change (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound (selectRow (value := value))).time ((n, acc), rows, default, ()) ≤ _ at h
  exact h.trans (by omega)

end Signatures.Runtime.WeightedAGM.Evaluate
