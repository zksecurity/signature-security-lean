import Signatures.Runtime.CacheProgramming
import Signatures.Runtime.BackendCacheCost
import Signatures.Runtime.BackendExpressionSize

/-! Native time, storage, and code bounds for programming a supplied cache value.
The comparison instruction is implemented in the same backend; all traversal,
branching, insertion and retained lookup environments are charged here. -/

open PFunctor

namespace Signatures.Runtime.CacheProgramming

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) → Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty Atom} → (instr : Op a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  {key val : Ty Atom}

def frameWidth (width cap : Nat) : Nat := (4 * cap + 16) * width

def programmingTime (overhead : Nat → Nat) (width cap comparisonTime : Nat) : Nat :=
  cap * (comparisonTime + 257 * overhead (128 * frameWidth width cap)) +
    160 * overhead (128 * frameWidth width cap)

include sizes lists mono

private theorem withLookup_time
    (scan : Expr Op [key, val, .list (.pair key val)] (.pair .bool val))
    (env : Env base [key, val, .list (.pair key val)]) (width scanTime : Nat)
    (hh : header ≤ width)
    (hi : Q.size (rep.env [key, val, .list (.pair key val)]) env ≤ width)
    (hv : Q.size (rep.ty (.pair .bool val)) (scan.denote P env) ≤ width)
    (ht : (Expression.compileBound rep data P primitive laws dataLaws primitiveBound scan).time env ≤ scanTime) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound (withLookup scan)).time env ≤
      scanTime + 128 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hleft := sizes.sum_le
    (rep.env [.pair .bool val, key, val, .list (.pair key val)])
    (rep.env [.pair .bool val, key, val, .list (.pair key val)]) (.inl (scan.denote P env, env))
  have hright := sizes.sum_le
    (rep.env [.pair .bool val, key, val, .list (.pair key val)])
    (rep.env [.pair .bool val, key, val, .list (.pair key val)]) (.inr (scan.denote P env, env))
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  by_cases hfound : (scan.denote P env).1 = true <;>
    dsimp only [withLookup, Expression.compileBound, Expression.variableBound,
      LocalBound.castFunction, LocalBound.compose, LocalBound.pair, LocalBound.fst,
      LocalBound.snd, LocalBound.identity, LocalBound.elim, DataCostLaws.selectBound,
      DataCostLaws.consBound, Expr.denote, Var.get, id, Function.comp_def,
      LanguageRepresentation.ty, LanguageRepresentation.env, Sum.elim] at * <;>
    simp only [hfound, ite_true] <;> grind only

/-- Charge insertion and retained lookup output independently of how the scan's
comparison is implemented. This also supports inlined structured comparisons. -/
theorem withLookup_time_bound
    (scan : Expr Op [key, val, .list (.pair key val)] (.pair .bool val))
    (env : Env base [key, val, .list (.pair key val)]) (width scanTime : Nat)
    (hh : header ≤ width)
    (hi : Q.size (rep.env [key, val, .list (.pair key val)]) env ≤ width)
    (hv : Q.size (rep.ty (.pair .bool val)) (scan.denote P env) ≤ width)
    (ht : (Expression.compileBound rep data P primitive laws dataLaws primitiveBound scan).time env ≤ scanTime) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound (withLookup scan)).time env ≤
      scanTime + 128 * overhead (128 * width) :=
  withLookup_time rep data P primitive sizes lists laws dataLaws primitiveBound mono scan env width scanTime hh hi hv ht

omit sizes lists mono [C.HasOption] [C.HasSum] [Q.HasCategory] QP QS in
theorem property [DecidableEq (key.Value base)]
    (width cap : Nat) (k : key.Value base) (v : val.Value base)
    (xs : List (key.Value base × val.Value base))
    (hi : CacheCompiler.Input (Q := Q) rep width cap (k, v, xs, ())) :
    CacheCompiler.Entries (Q := Q) rep width (value k v xs) ∧ (value k v xs).length ≤ cap + 1 := by
  refine ⟨?_, (length k v xs).trans (Nat.add_le_add_right hi.2.2.2 1)⟩
  unfold value
  split
  · exact hi.2.2.1
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hi.1, hi.2.1⟩
    · exact hi.2.2.1 p hp

theorem expression_time (eq : Op (.pair key key) .bool) [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (width cap comparisonTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (k : key.Value base) (v : val.Value base) (xs : List (key.Value base × val.Value base))
    (hi : CacheCompiler.Input (Q := Q) rep width cap (k, v, xs, ()))
    (he : ∀ p ∈ xs, (primitiveBound eq).time (p.1, k) ≤ comparisonTime) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound (expression eq)).time
      (k, v, xs, ()) ≤ programmingTime overhead width cap comparisonTime := by
  let W := frameWidth width cap
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hin := CacheCompiler.input_size rep sizes lists width cap hh hu (k, v, xs, ()) hi
  have hv := CacheCompiler.lookup_value_size rep P eq heq width cap (k, v, xs, ()) hi
  have hp := sizes.prod_le rep.data.bool (rep.ty val) ((lookup eq).denote P (k, v, xs, ()))
  have hl := LookupCompiler.lookup_time_bound_of_caps rep data P primitive laws dataLaws primitiveBound
    sizes mono eq k v xs W comparisonTime cap (hh.trans hw) (hu.trans hw)
    (fun b => (hb b).trans hw) (hi.1.trans hw) (hi.2.1.trans hw)
    (fun p hp => ⟨(hi.2.2.1 p hp).1.trans hw, (hi.2.2.1 p hp).2.trans hw⟩) hi.2.2.2
    (by
      intro ys hn hy
      have hs := CacheCompiler.list_size rep sizes lists ys width cap hh
        (fun p hp => hi.2.2.1 p (hy p hp)) hn
      exact hs.trans (by dsimp [W, frameWidth]; nlinarith)) he
  have ht := withLookup_time rep data P primitive sizes lists laws dataLaws primitiveBound mono
    (lookup eq) (k, v, xs, ()) W _ (hh.trans hw)
    (hin.trans (by dsimp [W, frameWidth]; nlinarith))
    (by
      have hb' := hb ((lookup eq).denote P (k, v, xs, ())).1
      change Q.size (StepClass.HasProd.prod rep.data.bool (rep.ty val)) _ ≤ _
      dsimp only [W, frameWidth]
      nlinarith) hl
  exact ht.trans (by dsimp only [programmingTime, W] at *; omega)

include laws dataLaws in
theorem cost (eq : Op (.pair key key) .bool) [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (width cap comparisonTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (k : key.Value base) (v : val.Value base) (xs : List (key.Value base × val.Value base))
    (hi : CacheCompiler.Input (Q := Q) rep width cap (k, v, xs, ()))
    (he : ∀ p ∈ xs, (primitiveBound eq).time (p.1, k) ≤ comparisonTime) :
    Q.cost (Expression.compile rep data P primitive (expression eq)) (k, v, xs, ()) ≤
      programmingTime overhead width cap comparisonTime :=
  (Expression.cost_compile_le rep data P primitive laws dataLaws primitiveBound (expression eq) (k, v, xs, ())).trans
    (expression_time rep data P primitive sizes lists laws dataLaws primitiveBound mono
      eq heq width cap comparisonTime hh hu hb k v xs hi he)

omit sizes lists mono [C.HasOption] in
theorem description (eq : Op (.pair key key) .bool) (descriptionSize : DescriptionSize Q) (allowance : Nat)
    (dlaws : LocalDescriptionLaws descriptionSize allowance)
    (dataDescription : DataDescriptionLaws descriptionSize rep.data data allowance) :
    descriptionSize.localSize (Expression.compile rep data P primitive (expression (val := val) eq)) ≤
      descriptionSize.localSize (primitive eq) + 200 * allowance := by
  have h := Expression.compile_size rep data P primitive descriptionSize allowance dlaws dataDescription
    (fun op => descriptionSize.localSize (primitive op)) (fun _ => le_rfl) (expression (val := val) eq)
  refine h.trans ?_
  simp only [expression, withLookup, lookup, lookupBody, Expression.descriptionBound, Expression.variableDescription]
  omega

end Signatures.Runtime.CacheProgramming
