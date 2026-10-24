import Proofs.Runtime.BackendWeightedTerms

/-! Native term generation inside a retained caller context. The width includes
the entire retained environment, so nested use charges the transcript, accumulator
and caller data as well as the generator's own recursion frames. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Terms

open Weights BackendProgram

theorem oopsFrom_weakenTail (d n start : Nat) {Γ : List (Ty CryptoAtom)}
    (Δ : List (Ty CryptoAtom)) :
    (oopsFrom d n start (Γ := Γ)).weakenTail Δ =
      oopsFrom d n start (Γ := Γ ++ Δ) := by
  induction n generalizing start Γ with
  | zero => rfl
  | succ n ih =>
      simp only [oopsFrom, Expr.weakenTail, Var.weakenTail, ih]

theorem proximityFrom_weakenTail (ell n start : Nat) {Γ : List (Ty CryptoAtom)}
    (Δ : List (Ty CryptoAtom)) :
    (proximityFrom ell n start (Γ := Γ)).weakenTail Δ =
      proximityFrom ell n start (Γ := Γ ++ Δ) := by
  induction n generalizing start Γ with
  | zero => rfl
  | succ n ih =>
      simp only [proximityFrom, Expr.weakenTail, Var.weakenTail, ih]

theorem oops_weakenTail (d : Nat) (Γ : List (Ty CryptoAtom)) :
    (oops d).weakenTail Γ =
      .letE (.op .one .unit) (oopsFrom d (d + 1) 0 (Γ := Γ)) := by
  simp only [oops, Expr.weakenTail, oopsFrom_weakenTail, List.nil_append]

theorem proximity_weakenTail (ell : Nat) (Γ : List (Ty CryptoAtom)) :
    (proximity ell).weakenTail Γ =
      .cons (.pair (.pair (.op (.finZero ell) .unit) (.snd (.var .here))) (.op .one .unit))
        (proximityFrom ell ell 1 (Γ := Γ)) := by
  simp only [proximity, Expr.weakenTail, Var.weakenTail, proximityFrom_weakenTail, List.nil_append]

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

theorem oops_weakenTail_time (d : Nat) (mt : F × K)
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width indexTime mulTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hk : Q.size (rep.ty key) mt.2 ≤ width)
    (hj : ∀ j : Fin (d + 1), Q.size (rep.ty (boundedNat d)) j ≤ width)
    (hn : ∀ k ≤ d + 1, Q.size rep.data.nat k ≤ width)
    (hi : ∀ k ≤ d + 1, (primitiveBound (.finOfNat d)).time k ≤ indexTime)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (h1 : (primitiveBound .one).time () ≤ oneTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound ((oops d).weakenTail Γ)).time (mt, env) ≤
        oopsNativeTime overhead width d indexTime mulTime oneTime := by
  have hrec := oopsFrom_native_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    d (d + 1) 0 1 mt env width (termSpace width (d + 1)) indexTime mulTime
    hh hu hf hk hj (by simpa using hn)
    (by dsimp [termSpace]; nlinarith) (by simpa using hi) hm
  have hout := oopsFrom_output_size rep sizes lists cost d (d + 1) 0 1 mt env width hh hf hk hj
  change _ ≤ termSpace width (d + 1) at hout
  have hwidth : width ≤ termSpace width (d + 1) := by dsimp [termSpace]; nlinarith
  have hp := @sizes.prod_le
  have hscalar := hf 1
  have hmessage := hf mt.1
  have hone : (arithmetic F G₁ G₂ K M cost).execute .one () = (1 : F) := rfl
  have hfee : ∀ k ≤ 128 * (termSpace width (d + 1) + width),
      overhead k ≤ termFee overhead width (d + 1) := fun _ h => mono h
  have hstep :
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
        primitiveBound ((oops d).weakenTail Γ)).time (mt, env) ≤
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
        primitiveBound (oopsFrom d (d + 1) 0 (Γ := Γ))).time (1, mt, env) +
          oneTime + 64 * termFee overhead width (d + 1) := by
    clear hrec
    rw [oops_weakenTail]
    simp only [Expression.compileBound, LocalBound.compose, LocalBound.pair,
      LocalBound.identity, DataCostLaws.unitBound, Expr.denote, hone,
      LanguageRepresentation.ty, LanguageRepresentation.env, termFee,
      List.cons_append, List.nil_append, List.append] at *
    grind only
  dsimp only [oopsNativeTime, termFee] at *
  nlinarith

theorem proximity_weakenTail_time (ell : Nat)
    (ms : (proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M))
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width indexTime zeroTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hv : Q.size (rep.ty (tupleTy scalar ell)) ms.1 ≤ width)
    (hk : Q.size (rep.ty key) ms.2 ≤ width)
    (hj : ∀ j : Fin (ell + 1), Q.size (rep.ty (boundedNat ell)) j ≤ width)
    (hn : ∀ k ≤ ell + 1, Q.size rep.data.nat k ≤ width)
    (hi : ∀ k ≤ ell + 1, (primitiveBound (.finOfNat ell)).time k ≤ indexTime)
    (h0 : (primitiveBound (.finZero ell)).time () ≤ zeroTime)
    (h1 : (primitiveBound .one).time () ≤ oneTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound ((proximity ell).weakenTail Γ)).time (ms, env) ≤
        proximityNativeTime overhead width ell indexTime zeroTime oneTime := by
  have hrec := proximityFrom_native_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    ell ell 1 ms env width (termSpace width ell) indexTime
    hh hu hf hv hk hj (by intro k hk; exact hn k (by omega))
    (by dsimp [termSpace]; nlinarith) (by intro k hk; exact hi k (by omega))
  have hout := proximity_output_size rep sizes lists cost ell ms width hh hf hk hj
  have hvalue := (proximity ell).weakenTail_denote (arithmetic F G₁ G₂ K M cost) (ms, ()) env
  change ((proximity ell).weakenTail Γ).denote _ (ms, env) = _ at hvalue
  rw [← hvalue, proximity_weakenTail] at hout
  have htail := proximityFrom_output_size rep sizes lists cost ell ell 1 ms env width hh hf hk hj
  have hlength : (6 * (ell + 1) + 1) * width = termSpace width ell + 6 * width := by
    dsimp [termSpace]
    ring
  rw [hlength] at hout
  change _ ≤ termSpace width ell at htail
  have hwidth : width ≤ termSpace width ell := by dsimp [termSpace]; nlinarith
  have hp := @sizes.prod_le
  have hc := @lists.cons_le
  have hscalar := hf 1
  have htag := hj 0
  have hone : (arithmetic F G₁ G₂ K M cost).execute .one () = (1 : F) := rfl
  have hzero : (arithmetic F G₁ G₂ K M cost).execute (.finZero ell) () = (0 : Fin (ell + 1)) := rfl
  have hfee : ∀ k ≤ 128 * (termSpace width ell + width),
      overhead k ≤ termFee overhead width ell := fun _ h => mono h
  have hstep :
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
        primitiveBound ((proximity ell).weakenTail Γ)).time (ms, env) ≤
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
        primitiveBound (proximityFrom ell ell 1 (Γ := Γ))).time (ms, env) +
          zeroTime + oneTime + 64 * termFee overhead width ell := by
    clear hrec hvalue
    rw [proximity_weakenTail]
    simp only [Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
      DataCostLaws.unitBound, DataCostLaws.consBound, Expr.denote, Var.get, hone, hzero] at hout ⊢
    generalize hrows : (proximityFrom ell ell 1 (Γ := Γ)).denote
      (arithmetic F G₁ G₂ K M cost) (ms, env) = rows at htail hout ⊢
    dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, termFee,
      List.cons_append, List.nil_append, List.append] at *
    grind only
  dsimp only [proximityNativeTime, termFee] at *
  nlinarith

end Signatures.Runtime.WeightedAGM.Terms
