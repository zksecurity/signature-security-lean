import Signatures.Runtime.BackendWeightedReply
import Signatures.Runtime.BackendDataSize

/-! Bounds for local argument/result frames of lazy AGM replies. The cache
retains the entire original environment; its size is included explicitly. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Reply

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

variable {indexTy messageTy : Ty CryptoAtom}

include sizes

theorem replyFrame_size {value config : Ty CryptoAtom} (signing : Bool)
    (input : (requestTy indexTy messageTy signing).Value (cryptoBase F G₁ G₂ K M) × (storeTy indexTy messageTy value config).Value (cryptoBase F G₁ G₂ K M))
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hm : Q.size (rep.ty (requestTy indexTy messageTy signing)) input.1 ≤ width)
    (hs : Q.size (rep.ty (storeTy indexTy messageTy value config)) input.2 ≤ width) :
    Q.size (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]) (input.1, input.2, ()) ≤ 5 * width := by
  have hprod := @sizes.prod_le
  dsimp only [LanguageRepresentation.env] at *
  grind only

variable [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  (cost : PrimitiveCosts)

theorem cacheArgs_size {value config : Ty CryptoAtom} (signing : Bool)
    (env : Env (cryptoBase F G₁ G₂ K M)
      [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config])
    (width : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [requestTy indexTy messageTy signing,
      storeTy indexTy messageTy value config]) env ≤ width) :
    Q.size (rep.ty (.pair (requestTy indexTy messageTy signing) (cacheTy indexTy value)))
      ((cacheArgs signing).denote (arithmetic F G₁ G₂ K M cost) env) ≤ 3 * width := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  dsimp only [cacheArgs, LazyAGM.ReplySyntax.v0, LazyAGM.ReplySyntax.v1,
    Expr.denote, Var.get, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

include lists in
theorem replyResult_size {value config : Ty CryptoAtom}
    (signing : Bool) (response : Expr CryptoOp [value, config] point₁)
    (env : Env (cryptoBase F G₁ G₂ K M) [cacheResultTy indexTy value, requestTy indexTy messageTy signing, storeTy indexTy messageTy value config])
    (width : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [cacheResultTy indexTy value, requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]) env ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width) :
    Q.size (rep.ty (.pair point₁ (storeTy indexTy messageTy value config)))
      ((replyResult signing response).denote (arithmetic F G₁ G₂ K M cost) env) ≤ 16 * width := by
  obtain ⟨⟨r, nextCache⟩, m, ⟨cfg, cache, tr⟩, u⟩ := env
  cases u
  rw [replyResult_denote]
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  cases signing <;>
    dsimp only [record, requestTag, LanguageRepresentation.env, LanguageRepresentation.ty,
      storeTy, cacheResultTy, cacheTy, transcriptTy, Bool.false_eq_true, ite_true, ite_false] at * <;>
    grind only

end Signatures.Runtime.WeightedAGM.Reply
