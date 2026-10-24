import Proofs.Runtime.BackendIndexCost
import Proofs.Runtime.BackendReverseCost
import Proofs.Runtime.AttachTable

/-! Native accounting for attaching positional coefficients to encountered
keys. The compiled lookup retains the entire enclosing fold frame; the list
scan and the growing row accumulator are both charged. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.AttachCompiler

open AGM

universe v w

private abbrev bodyContext (key : Ty CryptoAtom) (Γ : List (Ty CryptoAtom)) :=
  [key, attachState key, scalar, .list key, .list scalar] ++ Γ

-- Keeping the lookup as a syntax argument lets the surrounding accounting
-- compose with its derived certificate without unfolding its internal fold.
private def bodyWith {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (lookup : Expr CryptoOp ([.nat, scalar, .list scalar] ++ bodyContext key Γ) scalar) :
    Expr CryptoOp (bodyContext key Γ) (attachState key) :=
  .letE (.var (.there (.there (.there (.there .here)))))
    (.letE (.var (.there (.there (.there .here))))
      (.letE (.fst (.var (.there (.there (.there .here)))))
        (.letE lookup
          (.pair (.op .natAdd (.pair (.var (.there .here)) (.nat 1)))
            (.cons (.pair (.var (.there (.there (.there (.there .here))))) (.var .here))
              (.snd (.var (.there (.there (.there (.there (.there .here))))))))))))

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

private theorem bodyWith_time_bound {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (lookup : Expr CryptoOp ([.nat, scalar, .list scalar] ++ bodyContext key Γ) scalar)
    (i : key.Value (cryptoBase F G₁ G₂ K M))
    (acc : Nat × List (key.Value (cryptoBase F G₁ G₂ K M) × F))
    (default : F) (keys : List (key.Value (cryptoBase F G₁ G₂ K M))) (values : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width lookupTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env (bodyContext key Γ)) (i, acc, default, keys, values, env) ≤ width)
    (h1 : Q.size rep.data.nat 1 ≤ width)
    (hn : Q.size rep.data.nat (acc.1 + 1) ≤ width)
    (hv : Q.size (rep.ty scalar)
      (lookup.denote (arithmetic F G₁ G₂ K M cost) (acc.1, default, values, i, acc, default, keys, values, env)) ≤ width)
    (hl : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound lookup).time (acc.1, default, values, i, acc, default, keys, values, env) ≤ lookupTime)
    (ha : (primitiveBound CryptoOp.natAdd).time (acc.1, 1) ≤ addTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (bodyWith lookup)).time (i, acc, default, keys, values, env) ≤
        lookupTime + addTime + 256 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  have hadd : (arithmetic F G₁ G₂ K M cost).execute CryptoOp.natAdd (acc.1, 1) = acc.1 + 1 := rfl
  dsimp only [bodyWith, bodyContext, attachState, tableTy, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    LocalBound.identity, DataCostLaws.natBound, DataCostLaws.unitBound, DataCostLaws.consBound,
    LanguageRepresentation.env, LanguageRepresentation.ty, List.cons_append, List.nil_append, List.append,
    Expr.denote, Var.get] at *
  simp only [hadd] at *
  grind only

/-- One actual attach-body execution, including the full coefficient scan.
The width bounds the enclosing frame and every coefficient sublist. -/
theorem body_time_bound {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (i : key.Value (cryptoBase F G₁ G₂ K M))
    (acc : Nat × List (key.Value (cryptoBase F G₁ G₂ K M) × F))
    (default : F) (keys : List (key.Value (cryptoBase F G₁ G₂ K M))) (values : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width comparisonTime subtractTime addTime cap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env (bodyContext key Γ)) (i, acc, default, keys, values, env) ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ acc.1 + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hc : values.length ≤ cap)
    (hl : ∀ xs : List F, xs.length ≤ cap → (∀ x ∈ xs, x ∈ values) →
      Q.size (rep.ty (.list scalar)) xs ≤ width)
    (he : ∀ n ≤ acc.1, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ comparisonTime)
    (hs : ∀ n ≤ acc.1, (primitiveBound CryptoOp.natSub).time (n, 1) ≤ subtractTime)
    (ha : (primitiveBound CryptoOp.natAdd).time (acc.1, 1) ≤ addTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound ((attachBody (indexTy := key)).weakenTail Γ)).time
      (i, acc, default, keys, values, env) ≤
        cap * (comparisonTime + subtractTime + 257 * overhead (128 * width)) +
          addTime + 320 * overhead (128 * width) := by
  have hlookup := IndexCompiler.index_time_bound_of_caps rep data
    (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono
    (cell := scalar) (Γ := bodyContext key Γ) CryptoOp.natEq CryptoOp.natSub
    (fun _ _ => rfl) (fun _ _ => rfl) acc.1 default values
    (i, acc, default, keys, values, env) width comparisonTime subtractTime cap hh hu hi hb
    (fun n hn' => hn n (by omega)) (hn 1 (by omega)) (hf default) (fun f _ => hf f) hc hl he hs
  have h := bodyWith_time_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    ((index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail (bodyContext key Γ))
    i acc default keys values env width
    (cap * (comparisonTime + subtractTime + 257 * overhead (128 * width)) +
      64 * overhead (128 * width)) addTime hh hu hi (hn 1 (by omega)) (hn _ le_rfl)
    (hf _) hlookup ha
  change (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound ((attachBody (indexTy := key)).weakenTail Γ)).time
    (i, acc, default, keys, values, env) ≤ _ at h
  exact h.trans (by omega)

end Signatures.Runtime.BackendProgram.AttachCompiler
