import Proofs.Runtime.AffineTable
import Proofs.Runtime.LookupExpr

/-! Charged pairing of independently sampled scalar tables and construction of the
bad branch's masked group bases. Both tables are sampled before this deterministic pass. -/

namespace Signatures.Runtime.AGM

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))
private def v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
private def v5 {a b c d e f Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: Γ) f :=
  .var (.there (.there (.there (.there (.there .here)))))

variable {indexTy : Ty CryptoAtom}

def pairTablesBody (eq : Expr CryptoOp [indexTy, indexTy] .bool) :
    Expr CryptoOp [.pair indexTy scalar, .list (affineCell indexTy), tableTy indexTy, tableTy indexTy]
      (.list (affineCell indexTy)) :=
  .letE v3 (.letE (.op .zero .unit) (.letE (.fst v2)
    (.letE ((lookupExpr eq).weakenTail
      [.pair indexTy scalar, .list (affineCell indexTy), tableTy indexTy, tableTy indexTy])
      (.cons (.pair v4 (.snd v0)) v5))))

def pairTablesFold (eq : Expr CryptoOp [indexTy, indexTy] .bool) :
    Expr CryptoOp [tableTy indexTy, tableTy indexTy] (.list (affineCell indexTy)) :=
  .fold v0 .nil (pairTablesBody eq)

def pairTables (eq : Expr CryptoOp [indexTy, indexTy] .bool) :
    Expr CryptoOp [tableTy indexTy, tableTy indexTy] (.list (affineCell indexTy)) :=
  .letE (pairTablesFold eq) reverseList

def maskedBases (eq : Expr CryptoOp [indexTy, indexTy] .bool) :
    Expr CryptoOp [point₁, point₁, tableTy indexTy, tableTy indexTy] (groupTable indexTy) :=
  .letE v3 (.letE v3
    (.letE ((pairTables eq).weakenTail [point₁, point₁, tableTy indexTy, tableTy indexTy])
      (.letE v4 (.letE v4
        (affineRows.weakenTail [tableTy indexTy, tableTy indexTy,
          point₁, point₁, tableTy indexTy, tableTy indexTy])))))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem pairTablesBody_run (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (p : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (acc : List ((indexTy.Value (cryptoBase F G₁ G₂ K M) × F) × F))
    (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (pairTablesBody eq).run (arithmetic F G₁ G₂ K M cost) (p, acc, a, b, ()) =
      let r := (lookupExpr (val := scalar) eq).run (arithmetic F G₁ G₂ K M cost) (p.1, (0 : F), b, ())
      ⟨(p, r.value.2) :: acc, r.steps + cost.field + 29⟩ := by
  have h := (lookupExpr (val := scalar) eq).weakenTail_run
    (Δ := [.pair indexTy scalar, .list (affineCell indexTy), tableTy indexTy, tableTy indexTy])
    (arithmetic F G₁ G₂ K M cost) (p.1, 0, b, ()) (p, acc, a, b, ())
  simp only [Env.append] at h
  dsimp [arithmetic, CryptoOp.price] at h ⊢
  simp only [pairTablesBody, Expr.run, v0, v2, v3, v4, v5, Var.get, Var.depth, h]
  apply congrArg (Run.mk _)
  omega

theorem pairTablesFold_value (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    ((pairTablesFold eq).run (arithmetic F G₁ G₂ K M cost) (a, b, ())).value =
      (a.map fun p => (p, (lookupValue p.1 (0 : F) b).2)).reverse := by
  change (foldRun (fun p acc => (pairTablesBody eq).run
    (arithmetic F G₁ G₂ K M cost) (p, acc, a, b, ())) a []).value = _
  rw [foldRun_value]
  simp_rw [pairTablesBody_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    lookupExpr_value _ _ heq]
  rw [foldl_cons_map, List.append_nil]

theorem pairTables_value (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    ((pairTables eq).run (arithmetic F G₁ G₂ K M cost) (a, b, ())).value =
      a.map fun p => (p, (lookupValue p.1 (0 : F) b).2) := by
  simp only [pairTables, Expr.run, pairTablesFold_value cost eq heq,
    Expr.run_value, reverseList_denote (cell := affineCell indexTy)
      (Γ := [tableTy indexTy, tableTy indexTy]), List.reverse_reverse]

theorem pairTablesFold_length (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    ((pairTablesFold eq).run (arithmetic F G₁ G₂ K M cost) (a, b, ())).value.length = a.length := by
  change (foldRun (fun p acc => (pairTablesBody eq).run
    (arithmetic F G₁ G₂ K M cost) (p, acc, a, b, ())) a []).value.length = _
  rw [foldRun_value]
  simp_rw [pairTablesBody_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  rw [foldl_cons_map, List.append_nil, List.length_reverse, List.length_map]

def pairTablesBound (cost : PrimitiveCosts) (na nb e : Nat) : Nat :=
  na * (nb * (e + 22) + cost.field + 48) + 9

theorem pairTables_steps_le (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (e : Nat) (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    ((pairTables eq).run (arithmetic F G₁ G₂ K M cost) (a, b, ())).steps ≤
      pairTablesBound cost a.length b.length e := by
  have hf := foldRun_steps_le
    (fun p acc => (pairTablesBody eq).run (arithmetic F G₁ G₂ K M cost) (p, acc, a, b, ()))
    (b.length * (e + 22) + cost.field + 38) (by
      intro p acc
      rw [pairTablesBody_run]
      dsimp only
      have h := lookupExpr_steps_le (val := scalar) (arithmetic F G₁ G₂ K M cost) eq e heq p.1 (0 : F) b
      omega) a []
  have hr := reverseList_steps_le (cell := affineCell indexTy)
    (Γ := [tableTy indexTy, tableTy indexTy]) (arithmetic F G₁ G₂ K M cost)
    ((pairTablesFold eq).run (arithmetic F G₁ G₂ K M cost) (a, b, ())).value (a, b, ())
  rw [pairTablesFold_length] at hr
  simp only [pairTables, Expr.run]
  change 1 + 1 + (foldRun _ a []).steps + 1 + _ + 1 ≤ _
  dsimp [pairTablesBound]
  nlinarith

theorem pairTables_native {I : Type} [Fintype I]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (encode : I → indexTy.Value (cryptoBase F G₁ G₂ K M)) (hinj : Function.Injective encode)
    (a b : I → F) :
    ((pairTables eq).run (arithmetic F G₁ G₂ K M cost)
      (canonicalKeys (fun i => (encode i, a i)), canonicalKeys (fun i => (encode i, b i)), ())).value =
      canonicalKeys (fun i => ((encode i, a i), b i)) := by
  rw [pairTables_value cost eq heq]
  simp only [canonicalKeys, List.map_ofFn, Function.comp_def]
  congr 1
  funext j
  rw [show (List.ofFn fun j => (encode ((Fintype.equivFin I).symm j), b ((Fintype.equivFin I).symm j))) =
    canonicalKeys (fun i => (encode i, b i)) from rfl, lookupValue_canonical encode hinj]

theorem maskedBases_run (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (g X : G₁) (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (maskedBases eq).run (arithmetic F G₁ G₂ K M cost) (g, X, a, b, ()) =
      let rows := (pairTables eq).run (arithmetic F G₁ G₂ K M cost) (a, b, ())
      let bases := (affineRows (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost) (g, X, rows.value, ())
      ⟨bases.value, rows.steps + bases.steps + 23⟩ := by
  have hp := (pairTables eq).weakenTail_run (Δ := [point₁, point₁, tableTy indexTy, tableTy indexTy])
    (arithmetic F G₁ G₂ K M cost) (a, b, ()) (g, X, a, b, ())
  have ha := (affineRows (indexTy := indexTy)).weakenTail_run
    (Δ := [tableTy indexTy, tableTy indexTy, point₁, point₁, tableTy indexTy, tableTy indexTy])
    (arithmetic F G₁ G₂ K M cost)
    (g, X, ((pairTables eq).run (arithmetic F G₁ G₂ K M cost) (a, b, ())).value, ())
    (a, b, g, X, a, b, ())
  simp only [Env.append] at hp ha
  simp only [maskedBases, Expr.run, v3, v4, Var.get, Var.depth, hp, ha]
  apply congrArg (Run.mk _)
  omega

def maskedBasesBound (cost : PrimitiveCosts) (na nb e : Nat) : Nat :=
  pairTablesBound cost na nb e + na * (2 * cost.scalar₁ + cost.group + 35) + 34

theorem pairTables_length (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    ((pairTables eq).run (arithmetic F G₁ G₂ K M cost) (a, b, ())).value.length = a.length := by
  simp only [pairTables, Expr.run, Expr.run_value,
    reverseList_denote (cell := affineCell indexTy) (Γ := [tableTy indexTy, tableTy indexTy]),
    List.length_reverse]
  simpa only [Expr.run_value] using pairTablesFold_length cost eq a b

theorem maskedBases_length (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (g X : G₁) (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    ((maskedBases eq).run (arithmetic F G₁ G₂ K M cost) (g, X, a, b, ())).value.length = a.length := by
  rw [maskedBases_run, affineRows_value, List.length_map]
  exact pairTables_length cost eq a b

theorem maskedBases_steps_le (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (e : Nat) (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (g X : G₁) (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    ((maskedBases eq).run (arithmetic F G₁ G₂ K M cost) (g, X, a, b, ())).steps ≤
      maskedBasesBound cost a.length b.length e := by
  have hp := pairTables_steps_le cost eq e heq a b
  have ha := affineRows_steps_le (indexTy := indexTy) (F := F) (G₂ := G₂) (K := K) (M := M) cost g X
    ((pairTables eq).run (arithmetic F G₁ G₂ K M cost) (a, b, ())).value
  have hl := pairTables_length cost eq a b
  rw [hl] at ha
  rw [maskedBases_run]
  exact (Nat.add_le_add_right (Nat.add_le_add hp ha) 23).trans (by
    dsimp [maskedBasesBound]
    omega)

theorem maskedBases_native {I : Type} [Fintype I]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (encode : I → indexTy.Value (cryptoBase F G₁ G₂ K M)) (hinj : Function.Injective encode)
    (a b : I → F) (g X : G₁) :
    ((maskedBases eq).run (arithmetic F G₁ G₂ K M cost)
      (g, X, canonicalKeys (fun i => (encode i, a i)), canonicalKeys (fun i => (encode i, b i)), ())).value =
      canonicalKeys (fun i => (encode i, a i • X + b i • g)) := by
  rw [maskedBases_run]
  change (affineRows.run (arithmetic F G₁ G₂ K M cost) (g, X,
    ((pairTables eq).run (arithmetic F G₁ G₂ K M cost)
      (canonicalKeys (fun i => (encode i, a i)), canonicalKeys (fun i => (encode i, b i)), ())).value, ())).value = _
  rw [pairTables_native cost eq heq encode hinj, affineRows_native]

end Signatures.Runtime.AGM
