import Proofs.Runtime.GroupWeightedSum

/-! Compiled affine group bases for the bad AGM branch. Inputs pair the two sampled
scalar tables in canonical order; pairing is charged separately by the caller. -/

namespace Signatures.Runtime.AGM

abbrev affineCell (indexTy : Ty CryptoAtom) : Ty CryptoAtom := .pair (.pair indexTy scalar) scalar
abbrev groupTable (indexTy : Ty CryptoAtom) : Ty CryptoAtom := .list (.pair indexTy point₁)

variable {indexTy : Ty CryptoAtom}

def affineBody : Expr CryptoOp
    [affineCell indexTy, groupTable indexTy, point₁, point₁, .list (affineCell indexTy)]
    (groupTable indexTy) :=
  .cons (.pair (.fst (.fst (.var .here)))
    (.op .add₁ (.pair
      (.op .scale₁ (.pair (.snd (.fst (.var .here))) (.var (.there (.there (.there .here))))))
      (.op .scale₁ (.pair (.snd (.var .here)) (.var (.there (.there .here))))))))
    (.var (.there .here))

def affineFold : Expr CryptoOp [point₁, point₁, .list (affineCell indexTy)] (groupTable indexTy) :=
  .fold (.var (.there (.there .here))) .nil affineBody

def affineRows : Expr CryptoOp [point₁, point₁, .list (affineCell indexTy)] (groupTable indexTy) :=
  .letE affineFold reverseList

theorem foldl_cons_map {A B : Type} (f : A → B) (xs : List A) (acc : List B) :
    xs.foldl (fun acc x => f x :: acc) acc = (xs.map f).reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem affineBody_run (cost : PrimitiveCosts)
    (p : (indexTy.Value (cryptoBase F G₁ G₂ K M) × F) × F)
    (acc : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (g X : G₁)
    (xs : List ((indexTy.Value (cryptoBase F G₁ G₂ K M) × F) × F)) :
    affineBody.run (arithmetic F G₁ G₂ K M cost) (p, acc, g, X, xs, ()) =
      ⟨(p.1.1, p.1.2 • X + p.2 • g) :: acc, 2 * cost.scalar₁ + cost.group + 25⟩ := by
  simp only [affineBody, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price]
  congr 1
  omega

theorem affineFold_value (cost : PrimitiveCosts) (g X : G₁)
    (xs : List ((indexTy.Value (cryptoBase F G₁ G₂ K M) × F) × F)) :
    ((affineFold (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost) (g, X, xs, ())).value =
      (xs.map fun p => (p.1.1, p.1.2 • X + p.2 • g)).reverse := by
  change (foldRun (fun p acc => affineBody.run (arithmetic F G₁ G₂ K M cost)
    (p, acc, g, X, xs, ())) xs []).value = _
  rw [foldRun_value]
  simp_rw [affineBody_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  simpa only [List.append_nil] using foldl_cons_map
    (fun p : (indexTy.Value (cryptoBase F G₁ G₂ K M) × F) × F =>
      (p.1.1, p.1.2 • X + p.2 • g)) xs []

theorem affineRows_value (cost : PrimitiveCosts) (g X : G₁)
    (xs : List ((indexTy.Value (cryptoBase F G₁ G₂ K M) × F) × F)) :
    ((affineRows (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost) (g, X, xs, ())).value =
      xs.map fun p => (p.1.1, p.1.2 • X + p.2 • g) := by
  simp only [affineRows, Expr.run]
  rw [affineFold_value]
  simp only [Expr.run_value, reverseList_denote (cell := .pair indexTy point₁)
    (Γ := [point₁, point₁, .list (affineCell indexTy)]), List.reverse_reverse]

theorem affineFold_steps_le (cost : PrimitiveCosts) (g X : G₁)
    (xs : List ((indexTy.Value (cryptoBase F G₁ G₂ K M) × F) × F)) :
    ((affineFold (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost) (g, X, xs, ())).steps ≤
      xs.length * (2 * cost.scalar₁ + cost.group + 28) + 6 := by
  have h := foldRun_steps_le
    (fun p acc => affineBody.run (arithmetic F G₁ G₂ K M cost) (p, acc, g, X, xs, ()))
    (2 * cost.scalar₁ + cost.group + 25) (by
      intro p acc
      rw [affineBody_run]) xs []
  change 3 + 1 + (foldRun
    (fun p acc => affineBody.run (arithmetic F G₁ G₂ K M cost) (p, acc, g, X, xs, ())) xs []).steps + 1 ≤ _
  nlinarith

theorem affineRows_steps_le (cost : PrimitiveCosts) (g X : G₁)
    (xs : List ((indexTy.Value (cryptoBase F G₁ G₂ K M) × F) × F)) :
    ((affineRows (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost) (g, X, xs, ())).steps ≤
      xs.length * (2 * cost.scalar₁ + cost.group + 35) + 11 := by
  have hf := affineFold_steps_le (indexTy := indexTy) (F := F) (G₂ := G₂) (K := K) (M := M) cost g X xs
  have hv := affineFold_value (indexTy := indexTy) (F := F) (G₂ := G₂) (K := K) (M := M) cost g X xs
  have hr := reverseList_steps_le (cell := .pair indexTy point₁)
    (Γ := [point₁, point₁, .list (affineCell indexTy)]) (arithmetic F G₁ G₂ K M cost)
    (xs.map fun p => (p.1.1, p.1.2 • X + p.2 • g)).reverse (g, X, xs, ())
  simp only [List.length_reverse, List.length_map] at hr
  simp only [affineRows, Expr.run, hv]
  nlinarith

theorem affineRows_native {ι : Type} [Fintype ι]
    (cost : PrimitiveCosts) (encode : ι → indexTy.Value (cryptoBase F G₁ G₂ K M))
    (a b : ι → F) (g X : G₁) :
    ((affineRows (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost)
      (g, X, canonicalKeys (fun i => ((encode i, a i), b i)), ())).value =
      canonicalKeys (fun i => (encode i, a i • X + b i • g)) := by
  rw [affineRows_value]
  simp only [canonicalKeys, List.map_ofFn, Function.comp_def]

end Signatures.Runtime.AGM
