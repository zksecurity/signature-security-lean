import Proofs.Runtime.BackendLazyAGMReply
import Proofs.Runtime.BackendDataSize

/-! Bounds for local argument/result frames of lazy AGM replies. The cache
retains the entire original environment; its size is included explicitly. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

/-- A conservative cap for the cache and every surrounding local frame. -/
def replyWidth (width cap : Nat) : Nat := CacheCompiler.frameWidth (5 * width) cap

include sizes

theorem replyFrame_size {value config : Ty CryptoAtom}
    (input : M × (storeTy value config).Value (cryptoBase F G₁ G₂ M M))
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hm : Q.size (rep.ty message) input.1 ≤ width)
    (hs : Q.size (rep.ty (storeTy value config)) input.2 ≤ width) :
    Q.size (rep.env [message, storeTy value config]) (input.1, input.2, ()) ≤ 5 * width := by
  have hprod := @sizes.prod_le
  dsimp only [LanguageRepresentation.env] at *
  grind only

variable [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (cost : PrimitiveCosts)

theorem cacheArgs_size {value config : Ty CryptoAtom}
    (fallback : Expr CryptoOp [message, storeTy value config] value)
    (env : Env (cryptoBase F G₁ G₂ M M) [message, storeTy value config])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [message, storeTy value config]) env ≤ width)
    (hf : Q.size (rep.ty value) (fallback.denote (arithmetic F G₁ G₂ M M cost) env) ≤ width) :
    Q.size (rep.env [message, value, cacheTy value])
      ((cacheArgs fallback).denote (arithmetic F G₁ G₂ M M cost) env) ≤ 7 * width := by
  obtain ⟨m, ⟨cfg, cache, tr⟩, u⟩ := env
  cases u
  rw [cacheArgs_denote]
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, storeTy] at *
  grind only

include lists in
theorem replyResult_size {value config : Ty CryptoAtom}
    (signing : Bool) (response : Expr CryptoOp [value, config] point₁)
    (env : Env (cryptoBase F G₁ G₂ M M) [cacheResultTy value, message, storeTy value config])
    (width : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [cacheResultTy value, message, storeTy value config]) env ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width) :
    Q.size (rep.ty (.pair point₁ (storeTy value config)))
      ((replyResult signing response).denote (arithmetic F G₁ G₂ M M cost) env) ≤ 16 * width := by
  obtain ⟨⟨r, nextCache⟩, m, ⟨cfg, cache, tr⟩, u⟩ := env
  cases u
  rw [replyResult_denote]
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  cases signing <;>
    dsimp only [record, LanguageRepresentation.env, LanguageRepresentation.ty,
      storeTy, cacheResultTy, cacheTy, transcriptTy, Bool.false_eq_true, ite_true, ite_false] at * <;>
    grind only

end Signatures.Runtime.LazyAGM
