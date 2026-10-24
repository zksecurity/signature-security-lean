import Proofs.Runtime.BackendWeightedExpandRows
import Proofs.Runtime.BackendTokenRows

/-! Compose chronological coefficient matching, weighted expansion, and reversal.
The generator premise is local to the shared composition theorem; the OOPS and
Proximity endpoints derive it from their primitive and retained-context bounds. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Coefficients

open Terms BackendProgram

private def signedWith {indexTy messageTy : Ty CryptoAtom}
    (prepare : Expr CryptoOp [.list (AGM.tokenTy messageTy), .list scalar] (.list (rowTy messageTy)))
    (expand : Expr CryptoOp [.list (rowTy messageTy), .list (AGM.tokenTy messageTy), .list scalar]
      (.list (termTy indexTy))) :
    Expr CryptoOp [.list (AGM.tokenTy messageTy), .list scalar] (.list (termTy indexTy)) :=
  .letE prepare expand

def coefficientWidth (width tokenCap coeffCap termCap : Nat) : Nat :=
  (8 * (tokenCap * termCap) + 8 * tokenCap + 8 * coeffCap + 64) * width

def coefficientTime (overhead : Nat → Nat)
    (width tokenCap coeffCap termCap termTime mulTime comparisonTime subtractTime addTime zeroTime : Nat) : Nat :=
  let W := coefficientWidth width tokenCap coeffCap termCap
  TokenCompiler.rowsTime overhead width tokenCap coeffCap comparisonTime subtractTime addTime zeroTime +
    expandRowsTime overhead W tokenCap termCap termTime mulTime + 64 * overhead (128 * W)

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

include sizes mono

private theorem signedWith_time {indexTy messageTy : Ty CryptoAtom}
    (prepare : Expr CryptoOp [.list (AGM.tokenTy messageTy), .list scalar] (.list (rowTy messageTy)))
    (expand : Expr CryptoOp [.list (rowTy messageTy), .list (AGM.tokenTy messageTy), .list scalar]
      (.list (termTy indexTy)))
    (tr : List (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (rows : List ((messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F))
    (width preparationTime expansionTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [.list (AGM.tokenTy messageTy), .list scalar]) (tr, coeff, ()) ≤ width)
    (hv : prepare.denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()) = rows)
    (hr : Q.size (rep.ty (.list (rowTy messageTy))) rows ≤ width)
    (ho : Q.size (rep.ty (.list (termTy indexTy)))
      (expand.denote (arithmetic F G₁ G₂ K M cost) (rows, tr, coeff, ())) ≤ width)
    (hp : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound prepare).time (tr, coeff, ()) ≤ preparationTime)
    (he : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound expand).time (rows, tr, coeff, ()) ≤ expansionTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (signedWith prepare expand)).time (tr, coeff, ()) ≤
        preparationTime + expansionTime + 64 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [signedWith, Expression.compileBound, LocalBound.compose, LocalBound.pair,
    LocalBound.identity, Expr.denote, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  simp only [hv] at *
  grind only

include lists in
theorem signedTerms_time {indexTy messageTy : Ty CryptoAtom}
    (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy)))
    (tr : List (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (width tokenCap coeffCap termCap termTime mulTime comparisonTime subtractTime addTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ tokenCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy messageTy)) p ≤ width)
    (htc : tr.length ≤ tokenCap) (hcc : coeff.length ≤ coeffCap)
    (ht : ∀ p ∈ tr, ∀ t ∈ terms.denote (arithmetic F G₁ G₂ K M cost) (p.1, ()),
      Q.size (rep.ty (termTy indexTy)) t ≤ width)
    (hlen : ∀ m, (terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())).length = termCap)
    (hgen : ∀ p ∈ tr, ∀ (Δ : List (Ty CryptoAtom)) (tail : Env (cryptoBase F G₁ G₂ K M) Δ),
      Q.size (rep.env Δ) tail ≤ expandRowsWidth (coefficientWidth width tokenCap coeffCap termCap) tokenCap termCap →
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
        primitiveBound (terms.weakenTail Δ)).time (p.1, tail) ≤ termTime)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (hEq : ∀ n ≤ tokenCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ tokenCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hAdd : ∀ n ≤ tokenCap, (primitiveBound .natAdd).time (n, 1) ≤ addTime)
    (hZero : (primitiveBound .zero).time () ≤ zeroTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (signedTerms terms)).time (tr, coeff, ()) ≤
        coefficientTime overhead width tokenCap coeffCap termCap termTime mulTime
          comparisonTime subtractTime addTime zeroTime := by
  let W := coefficientWidth width tokenCap coeffCap termCap
  let rows := tr.reverse.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff coeff n))
  have hw3 : 3 * width ≤ W := by
    dsimp only [W, coefficientWidth]
    exact Nat.mul_le_mul_right width (by omega)
  have hw : width ≤ W := by omega
  have hprod := @sizes.prod_le
  have htr := lists.size_le_cap (rep.ty (AGM.tokenTy messageTy)) tr width tokenCap hk htc
  have hc := lists.size_le_cap (rep.ty scalar) coeff width coeffCap (fun f _ => hf f) hcc
  have htHeader := Nat.mul_le_mul_left tokenCap hh
  have hcHeader := Nat.mul_le_mul_left coeffCap hh
  have hi : Q.size (rep.env [.list (AGM.tokenTy messageTy), .list scalar]) (tr, coeff, ()) ≤ W := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, W, coefficientWidth] at *
    clear hgen hlen ht hf hn hEq hSub hAdd hm
    grind only
  have hvalue : (AGM.tokenRows (dataTy := messageTy)).denote (arithmetic F G₁ G₂ K M cost)
      (tr, coeff, ()) = rows := by
    rw [← Expr.run_value, AGM.tokenRows_value]
  have hmem row (hit : row ∈ rows) : row.1 ∈ tr := by
    obtain ⟨n, hn', rfl⟩ := List.mem_mapIdx.mp hit
    exact List.mem_reverse.mp (List.getElem_mem hn')
  have hrow row (hit : row ∈ rows) : Q.size (rep.ty (rowTy messageTy)) row ≤ 3 * width := by
    have hp := sizes.prod_le (rep.ty (AGM.tokenTy messageTy)) (rep.ty scalar) row
    have htoken := hk row.1 (hmem row hit)
    have hscalar := hf row.2
    exact hp.trans (by omega)
  have hrowCount : rows.length ≤ tokenCap := by
    simpa only [rows, List.length_mapIdx, List.length_reverse] using htc
  have hrows := lists.size_le_cap (rep.ty (rowTy messageTy)) rows (3 * width) tokenCap hrow hrowCount
  have hrowsSize : Q.size (rep.ty (.list (rowTy messageTy))) rows ≤ W := by
    change Q.size (rep.ty (.list (rowTy messageTy))) rows ≤ _ at hrows
    have hsmall : tokenCap * (3 * width + header) + header ≤ (4 * tokenCap + 1) * width := by
      nlinarith
    exact hrows.trans (hsmall.trans (Nat.mul_le_mul_right width (by omega)))
  have hout := signedTerms_output_size rep sizes lists cost terms tr coeff tokenCap termCap width width
    htc hlen (fun p hp t ht' => (sizes.fst_le (rep.ty indexTy) (rep.ty scalar) t).trans (ht p hp t ht')) hf
  have hsmall : tokenCap * termCap * (width + width + 2 * header) + header ≤
      (4 * (tokenCap * termCap) + 1) * width := by
    calc
      _ ≤ tokenCap * termCap * (4 * width) + width :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) hh
      _ = _ := by ring
  have houtSize := hout.trans (hsmall.trans (show (4 * (tokenCap * termCap) + 1) * width ≤ W from
    Nat.mul_le_mul_right width (by omega)))
  change Q.size (rep.ty (.list (termTy indexTy)))
    ((expandRows terms (Γ := [.list (AGM.tokenTy messageTy), .list scalar])).denote
      (arithmetic F G₁ G₂ K M cost) ((AGM.tokenRows (dataTy := messageTy)).denote
        (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()), tr, coeff, ())) ≤ W at houtSize
  rw [hvalue] at houtSize
  have hprepare := TokenCompiler.rows_time_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    tr coeff (Γ := []) () width tokenCap coeffCap comparisonTime subtractTime addTime zeroTime
    hh hu hu hb hn hf hk htc hcc hEq hSub hAdd hZero
  have hclosed : (AGM.tokenRows (dataTy := messageTy)).weakenTail [] = AGM.tokenRows := rfl
  rw [hclosed] at hprepare
  have hexpand := expandRows_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    terms rows (Γ := [.list (AGM.tokenTy messageTy), .list scalar]) (tr, coeff, ())
    W tokenCap termCap termTime mulTime (hh.trans hw) (hu.trans hw) hi
    (fun row hit => (hrow row hit).trans hw3) hrowCount (fun f => (hf f).trans hw)
    (fun row hit t ht' => (ht row.1 (hmem row hit) t ht').trans hw)
    (fun row _ => (hlen row.1.1).le)
    (fun row hit Δ tail hs => hgen row.1 (hmem row hit) Δ tail hs) hm
  have htime := signedWith_time rep data cost primitive laws dataLaws primitiveBound sizes mono
    AGM.tokenRows (expandRows terms) tr coeff rows W
    (TokenCompiler.rowsTime overhead width tokenCap coeffCap comparisonTime subtractTime addTime zeroTime)
    (expandRowsTime overhead W tokenCap termCap termTime mulTime)
    (hh.trans hw) hi hvalue hrowsSize houtSize hprepare hexpand
  exact htime

end Signatures.Runtime.WeightedAGM.Coefficients
