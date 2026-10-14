import Signatures.Runtime.BackendWeightedTermsSize
import Signatures.Runtime.BackendExpressionCost

/-! Compiled term-generation costs derived from primitive and structural
contracts. The reserve in `space` pays for retained recursion frames; generated
lists, tuple projections, constructors, and literal loading are also charged.
There is no assumed cost for a complete term generator. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Terms

open Weights BackendProgram

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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

include sizes lists mono

theorem oopsFrom_native_time (d n start : Nat) (p : F) (mt : F × K)
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width space indexTime mulTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hk : Q.size (rep.ty key) mt.2 ≤ width)
    (hj : ∀ j : Fin (d + 1), Q.size (rep.ty (boundedNat d)) j ≤ width)
    (hn : ∀ k ≤ start + n, Q.size rep.data.nat k ≤ width)
    (hspace : Q.size (rep.env Γ) env + 6 * n * width ≤ space)
    (hi : ∀ k ≤ start + n, (primitiveBound (.finOfNat d)).time k ≤ indexTime)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound (oopsFrom d n start)).time (p, mt, env) ≤
        n * (indexTime + mulTime + 64 * overhead (128 * (space + width))) +
          4 * overhead (128 * (space + width)) := by
  induction n generalizing start p Γ with
  | zero =>
      have hp := @sizes.prod_le
      have hz := lists.nil_le (rep.ty (termTy (oopsKey d)))
      have hfp := hf p
      have hfm := hf mt.1
      have hfee : ∀ k ≤ 128 * (space + width), overhead k ≤ overhead (128 * (space + width)) :=
        fun _ h => mono h
      simp only [oopsFrom, Expression.compileBound, LocalBound.compose,
        DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote,
        List.cons_append, List.nil_append, List.append, LanguageRepresentation.ty, LanguageRepresentation.env] at *
      grind only
  | succ n ih =>
      have hprod := @sizes.prod_le
      have hcons := @lists.cons_le
      have hfp := hf p
      have hfm := hf mt.1
      have hnext := hf (p * mt.1)
      have henv : Q.size (rep.env ([scalar, oopsMessage] ++ Γ)) (p, mt, env) +
          6 * n * width ≤ space := by
        simp only [oopsMessage, List.cons_append, List.nil_append, List.append, LanguageRepresentation.ty, LanguageRepresentation.env] at *
        grind only
      have hrec := ih (start + 1) (p * mt.1) (Γ := [scalar, oopsMessage] ++ Γ)
        (p, mt, env) (by intro k hk; exact hn k (by omega)) henv
        (by intro k hk; exact hi k (by omega))
      have htail := oopsFrom_output_size rep sizes lists cost d n (start + 1) (p * mt.1) mt
        (Γ := [scalar, oopsMessage] ++ Γ) (p, mt, env) width hh hf hk hj
      have hindex := hi start (by omega)
      have hmul := hm p mt.1
      have htag := hj ⟨start % (d + 1), Nat.mod_lt _ (Nat.zero_lt_succ d)⟩
      have hnat := hn start (by omega)
      have hfee : ∀ k ≤ 128 * (space + width), overhead k ≤ overhead (128 * (space + width)) :=
        fun _ h => mono h
      have hstep :
          (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
            dataLaws primitiveBound (oopsFrom d (n + 1) start (Γ := Γ))).time (p, mt, env) ≤
          (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
            dataLaws primitiveBound (oopsFrom d n (start + 1) (Γ := [scalar, oopsMessage] ++ Γ))).time
              (p * mt.1, mt, p, mt, env) + indexTime + mulTime +
                64 * overhead (128 * (space + width)) := by
        simp only [oopsFrom, Expression.compileBound, Expression.variableBound,
          LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
          DataCostLaws.unitBound, DataCostLaws.natBound, DataCostLaws.consBound,
          Expr.denote, Var.get, arithmetic, List.cons_append, List.nil_append, List.append, LanguageRepresentation.ty, LanguageRepresentation.env] at *
        grind only
      nlinarith

theorem proximityFrom_native_time (ell n start : Nat)
    (ms : (proximityTupleMessage n).Value (cryptoBase F G₁ G₂ K M))
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width space indexTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hv : Q.size (rep.ty (tupleTy scalar n)) ms.1 ≤ width)
    (hk : Q.size (rep.ty key) ms.2 ≤ width)
    (hj : ∀ j : Fin (ell + 1), Q.size (rep.ty (boundedNat ell)) j ≤ width)
    (hn : ∀ k ≤ start + n, Q.size rep.data.nat k ≤ width)
    (hspace : Q.size (rep.env Γ) env + 6 * n * width ≤ space)
    (hi : ∀ k ≤ start + n, (primitiveBound (.finOfNat ell)).time k ≤ indexTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound (proximityFrom ell n start)).time (ms, env) ≤
        n * (indexTime + 64 * overhead (128 * (space + width))) +
          4 * overhead (128 * (space + width)) := by
  induction n generalizing start Γ with
  | zero =>
      have hp := @sizes.prod_le
      have hz := lists.nil_le (rep.ty (termTy (proximityKey ell)))
      have hfee : ∀ k ≤ 128 * (space + width), overhead k ≤ overhead (128 * (space + width)) :=
        fun _ h => mono h
      simp only [proximityFrom, Expression.compileBound, LocalBound.compose,
        DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote,
        List.cons_append, List.nil_append, List.append, LanguageRepresentation.ty, LanguageRepresentation.env] at *
      grind only
  | succ n ih =>
      have hprod := @sizes.prod_le
      have hsnd := @sizes.snd_le
      have hcons := @lists.cons_le
      have hhead := hf ms.1.1
      have hvector : Q.size (rep.ty (tupleTy scalar n)) ms.1.2 ≤ width :=
        (sizes.snd_le (rep.ty scalar) (rep.ty (tupleTy scalar n)) ms.1).trans hv
      have henv : Q.size (rep.env ([proximityTupleMessage (n + 1)] ++ Γ)) (ms, env) +
          6 * n * width ≤ space := by
        simp only [proximityTupleMessage, List.cons_append, List.nil_append, List.append, LanguageRepresentation.ty, LanguageRepresentation.env] at *
        grind only
      have hrec := ih (start + 1) (ms.1.2, ms.2)
        (Γ := [proximityTupleMessage (n + 1)] ++ Γ) (ms, env) hvector hk
        (by intro k hk; exact hn k (by omega)) henv
        (by intro k hk; exact hi k (by omega))
      have htail := proximityFrom_output_size rep sizes lists cost ell n (start + 1) (ms.1.2, ms.2)
        (Γ := [proximityTupleMessage (n + 1)] ++ Γ) (ms, env) width hh hf hk hj
      have hindex := hi start (by omega)
      have htag := hj ⟨start % (ell + 1), Nat.mod_lt _ (Nat.zero_lt_succ ell)⟩
      have hnat := hn start (by omega)
      have hfee : ∀ k ≤ 128 * (space + width), overhead k ≤ overhead (128 * (space + width)) :=
        fun _ h => mono h
      have hstep :
          (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
            dataLaws primitiveBound (proximityFrom ell (n + 1) start (Γ := Γ))).time (ms, env) ≤
          (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
            dataLaws primitiveBound (proximityFrom ell n (start + 1)
              (Γ := [proximityTupleMessage (n + 1)] ++ Γ))).time
              ((ms.1.2, ms.2), ms, env) + indexTime + 64 * overhead (128 * (space + width)) := by
        simp only [proximityFrom, Expression.compileBound, Expression.variableBound,
          LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
          DataCostLaws.unitBound, DataCostLaws.natBound, DataCostLaws.consBound,
          Expr.denote, Var.get, arithmetic, List.cons_append, List.nil_append, List.append, LanguageRepresentation.ty, LanguageRepresentation.env] at *
        grind only
      nlinarith

end Signatures.Runtime.WeightedAGM.Terms
