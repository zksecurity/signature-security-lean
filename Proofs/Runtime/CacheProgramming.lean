import Proofs.Runtime.CacheRefinement

/-! Pure first-entry-preserving cache programming with an implemented comparison
instruction. This inserts a supplied value and performs no random sampling. -/

namespace Signatures.Runtime.CacheProgramming

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  {key val : Ty Atom}

def withLookup (scan : Expr Op [key, val, .list (.pair key val)] (.pair .bool val)) :
    Expr Op [key, val, .list (.pair key val)] (.list (.pair key val)) :=
  .letE scan
    (.branch (.fst (.var .here)) (.var (.there (.there (.there .here))))
      (.cons (.pair (.var (.there .here)) (.var (.there (.there .here))))
        (.var (.there (.there (.there .here))))))

def expression (eq : Op (.pair key key) .bool) :
    Expr Op [key, val, .list (.pair key val)] (.list (.pair key val)) :=
  withLookup (lookup eq)

def value {K V : Type} [DecidableEq K] (k : K) (v : V) (xs : List (K × V)) : List (K × V) :=
  match cacheMap xs k with
  | some _ => xs
  | none => (k, v) :: xs

theorem denote (P : Primitives base Op) (eq : Op (.pair key key) .bool)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (k : key.Value base) (v : val.Value base) (xs : List (key.Value base × val.Value base)) :
    (expression eq).denote P (k, v, xs, ()) = value k v xs := by
  have hl := lookup_correct P eq heq k v xs
  rw [Expr.run_value, lookupValue_cacheMap] at hl
  dsimp only [expression, withLookup, Expr.denote, Var.get]
  rw [hl]
  unfold value
  cases cacheMap xs k <;> rfl

theorem length {K V : Type} [DecidableEq K] (k : K) (v : V) (xs : List (K × V)) :
    (value k v xs).length ≤ xs.length + 1 := by
  unfold value
  split <;> simp

theorem preserves {K V : Type} [DecidableEq K] (k : K) (v : V) (xs : List (K × V))
    (q : K) (old : V) (hit : cacheMap xs q = some old) :
    cacheMap (value k v xs) q = some old := by
  unfold value
  split
  · exact hit
  · rename_i miss
    have hne : k ≠ q := by intro h; subst q; simp [miss] at hit
    simpa [cacheMap, hne] using hit

end Signatures.Runtime.CacheProgramming
