import Signatures.Runtime.BackendLazyAGMEvaluate
import Signatures.Runtime.BackendDataSize

/-! Encoded frames used by the native coefficient evaluator. Row and private
cache capacities are independent; all retained lists contribute to the bound. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

def evaluationWidth (width rowCap cacheCap : Nat) : Nat :=
  (4 * rowCap + 8 * cacheCap + 64) * width

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

omit lists in
theorem evaluationRow_key_size (row : (M × G₁) × F) :
    Q.size (rep.ty message) row.1.1 ≤ Q.size (rep.ty evalRowTy) row := by
  exact (sizes.fst_le (rep.ty message) (rep.ty point₁) row.1).trans
    (sizes.fst_le (rep.ty (AGM.tokenTy message)) (rep.ty scalar) row)

omit sizes lists [C.HasSum] [C.HasOption] in
theorem evaluationSelected_size (rows : List ((M × G₁) × F)) (default : (M × G₁) × F)
    (n width : Nat) (hr : ∀ row ∈ rows, Q.size (rep.ty evalRowTy) row ≤ width)
    (hd : Q.size (rep.ty evalRowTy) default ≤ width) :
    Q.size (rep.ty evalRowTy) ((rows[n]?).getD default) ≤ width := by
  cases hx : rows[n]? with
  | none => exact hd
  | some row => exact hr row (List.mem_of_getElem? hx)

omit sizes [C.HasSum] [C.HasOption] in
theorem evaluationRows_size
    (rows : List ((M × G₁) × F)) (width cap : Nat) (hh : header ≤ width)
    (hr : ∀ row ∈ rows, Q.size (rep.ty evalRowTy) row ≤ width)
    (hn : rows.length ≤ cap) :
    Q.size (rep.ty (.list evalRowTy)) rows ≤ (2 * cap + 1) * width := by
  have h := lists.size_le_cap (rep.ty evalRowTy) rows width cap hr hn
  change Q.size (rep.ty (.list evalRowTy)) rows ≤ _ at h
  nlinarith [Nat.mul_le_mul_left cap hh]

theorem evaluationFrame_size {value : Ty CryptoAtom}
    (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ M M))
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F)
    (width rowCap cacheCap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hn : Q.size rep.data.nat n ≤ width)
    (ha : Q.size (rep.ty value) acc ≤ width)
    (hr : ∀ row ∈ rows, Q.size (rep.ty evalRowTy) row ≤ width)
    (hl : rows.length ≤ rowCap) (hd : Q.size (rep.ty evalRowTy) default ≤ width) :
    Q.size (rep.env [evalStateTy value, .list evalRowTy, evalRowTy])
      ((n, acc), rows, default, ()) ≤ evaluationWidth width rowCap cacheCap := by
  have hs := evaluationRows_size rep lists rows width rowCap hh hr hl
  have hp := @sizes.prod_le
  dsimp only [evaluationWidth, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

theorem evaluationUpdateFrame_size {value : Ty CryptoAtom}
    (n : Nat) (answer acc : value.Value (cryptoBase F G₁ G₂ M M))
    (row : (M × G₁) × F) (rows : List ((M × G₁) × F)) (default : (M × G₁) × F)
    (width rowCap cacheCap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hn : Q.size rep.data.nat n ≤ width)
    (ha : Q.size (rep.ty value) acc ≤ width) (hv : Q.size (rep.ty value) answer ≤ width)
    (hx : Q.size (rep.ty evalRowTy) row ≤ width)
    (hr : ∀ row ∈ rows, Q.size (rep.ty evalRowTy) row ≤ width)
    (hl : rows.length ≤ rowCap) (hd : Q.size (rep.ty evalRowTy) default ≤ width) :
    Q.size (rep.env [value, evalRowTy, evalStateTy value, .list evalRowTy, evalRowTy])
      (answer, row, (n, acc), rows, default, ()) ≤ evaluationWidth width rowCap cacheCap := by
  have hs := evaluationRows_size rep lists rows width rowCap hh hr hl
  have hp := @sizes.prod_le
  dsimp only [evaluationWidth, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

theorem evaluationCache_size {value : Ty CryptoAtom}
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (width rowCap cacheCap : Nat) (hh : header ≤ width)
    (he : CacheCompiler.Entries (Q := Q) rep (key := message) (val := value) width cache)
    (hn : cache.length ≤ cacheCap) :
    Q.size (rep.ty (cacheTy value)) cache ≤ evaluationWidth width rowCap cacheCap := by
  have h := CacheCompiler.list_size rep sizes lists (key := message) (val := value)
    cache width cacheCap hh he hn
  exact h.trans (by dsimp [evaluationWidth]; nlinarith)

end Signatures.Runtime.LazyAGM
