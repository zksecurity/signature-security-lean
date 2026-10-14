import Signatures.Runtime.ReplayCacheRefinement
import Signatures.Runtime.Sampling

/-! First-order verification and selection of a forgery's live-hash ordinal.
The live cache is stored newest-first; reversing it is an explicit charged fold. -/

namespace Signatures.Runtime.Schnorr

open OracleComp

abbrev indexResult : Ty CryptoAtom := .pair .bool .nat

private def indexState : Expr CryptoOp
    [hashKey, hashKey, .pair hashKey scalar, indexResult, hashKey, hashCache] indexResult :=
  .var (.there (.there (.there .here)))

def liveIndexBody : Expr CryptoOp [.pair hashKey scalar, indexResult, hashKey, hashCache] indexResult :=
  .branch (.fst (.var (.there .here))) (.var (.there .here))
    (.letE (.var (.there (.there .here)))
      (.letE (.fst (.var (.there .here)))
        (.branch (hashEq.weakenTail [.pair hashKey scalar, indexResult, hashKey, hashCache])
          (.pair (.bool true) (.snd indexState))
          (.pair (.bool false) (.op .natAdd (.pair (.snd indexState) (.nat 1)))))))

def liveIndexFold : Expr CryptoOp [hashKey, hashCache] indexResult :=
  .fold (.var (.there .here)) (.pair (.bool false) (.nat 0)) liveIndexBody

def liveIndex : Expr CryptoOp [hashKey, hashCache] indexResult :=
  .letE (.letE (.var (.there .here)) reverseList)
    (.letE (.var (.there .here)) (liveIndexFold.weakenTail [hashKey, hashCache]))

def findStep {K V : Type} [DecidableEq K] (key : K) (s : Bool × Nat) (x : K × V) : Bool × Nat :=
  if s.1 then s else if x.1 = key then (true, s.2) else (false, s.2 + 1)

private theorem findStep_found {K V : Type} [DecidableEq K]
    (key : K) (xs : List (K × V)) (n : Nat) :
    xs.foldl (findStep key) (true, n) = (true, n) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [findStep] using ih

theorem findStep_fold {K V : Type} [DecidableEq K] (key : K) (xs : List (K × V)) (n : Nat) :
    xs.foldl (findStep key) (false, n) =
      (xs.any (fun x => decide (x.1 = key)), n + xs.findIdx (fun x => decide (x.1 = key))) := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    by_cases h : x.1 = key
    · simp [findStep, h, findStep_found, List.findIdx_cons]
    · simpa [findStep, h, List.findIdx_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (n + 1)

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem liveIndexBody_denote (cost : PrimitiveCosts) (x : (M × G₁) × F)
    (s : Bool × Nat) (key : M × G₁) (xs : List ((M × G₁) × F)) :
    liveIndexBody.denote (arithmetic F G₁ G₂ K M cost) (x, s, key, xs, ()) = findStep key s x := by
  have he := hashEq.weakenTail_denote
    (Δ := [.pair hashKey scalar, indexResult, hashKey, hashCache])
    (arithmetic F G₁ G₂ K M cost) (x.1, key, ()) (x, s, key, xs, ())
  simp only [Env.append] at he
  simp only [liveIndexBody, Expr.denote, Var.get, indexState, he,
    hashEq_value (F := F) (G₂ := G₂) (K := K), findStep, decide_eq_true_eq]
  rfl

theorem liveIndexFold_denote (cost : PrimitiveCosts) (key : M × G₁) (xs : List ((M × G₁) × F)) :
    liveIndexFold.denote (arithmetic F G₁ G₂ K M cost) (key, xs, ()) =
      (xs.any (fun x => decide (x.1 = key)), xs.findIdx (fun x => decide (x.1 = key))) := by
  change xs.foldl (fun s x => liveIndexBody.denote (arithmetic F G₁ G₂ K M cost)
    (x, s, key, xs, ())) (false, 0) = _
  simp_rw [liveIndexBody_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  simpa using findStep_fold key xs 0

theorem liveIndex_denote (cost : PrimitiveCosts) (key : M × G₁) (xs : List ((M × G₁) × F)) :
    liveIndex.denote (arithmetic F G₁ G₂ K M cost) (key, xs, ()) =
      (xs.reverse.any (fun x => decide (x.1 = key)),
        xs.reverse.findIdx (fun x => decide (x.1 = key))) := by
  have he := liveIndexFold.weakenTail_denote (Δ := [hashKey, hashCache])
    (arithmetic F G₁ G₂ K M cost) (key, xs.reverse, ()) (key, xs, ())
  simp only [Env.append] at he
  simp only [liveIndex, Expr.denote, Var.get]
  rw [reverseList_denote, he, liveIndexFold_denote]

theorem liveIndexBody_steps (cost : PrimitiveCosts) (x : (M × G₁) × F)
    (s : Bool × Nat) (key : M × G₁) (xs : List ((M × G₁) × F)) :
    (liveIndexBody.run (arithmetic F G₁ G₂ K M cost) (x, s, key, xs, ())).steps ≤
      cost.messageEq + cost.point₁Eq + cost.natOp + 60 := by
  have he := hashEq.weakenTail_run
    (Δ := [.pair hashKey scalar, indexResult, hashKey, hashCache])
    (arithmetic F G₁ G₂ K M cost) (x.1, key, ()) (x, s, key, xs, ())
  simp only [Env.append] at he
  have hb := hashEq_steps_le (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost x.1 key
  by_cases hf : s.1 = true <;>
    by_cases hh : (hashEq.run (arithmetic F G₁ G₂ K M cost) (x.1, key, ())).value = true <;>
    simp only [liveIndexBody, Expr.run, Var.get, Var.depth, indexState, he, hf, hh,
      Bool.false_eq_true, ite_true, ite_false] <;>
    simp only [arithmetic, CryptoOp.price] at hb ⊢ <;> omega

theorem liveIndexFold_steps (cost : PrimitiveCosts) (key : M × G₁) (xs : List ((M × G₁) × F)) :
    (liveIndexFold.run (arithmetic F G₁ G₂ K M cost) (key, xs, ())).steps ≤
      xs.length * (cost.messageEq + cost.point₁Eq + cost.natOp + 63) + 7 := by
  have h := foldRun_steps_le
    (fun x s => liveIndexBody.run (arithmetic F G₁ G₂ K M cost) (x, s, key, xs, ()))
    (cost.messageEq + cost.point₁Eq + cost.natOp + 60)
    (fun x s => liveIndexBody_steps cost x s key xs) xs (false, 0)
  dsimp [liveIndexFold, Expr.run, Var.get, Var.depth]
  nlinarith

theorem liveIndex_steps (cost : PrimitiveCosts) (key : M × G₁) (xs : List ((M × G₁) × F)) :
    (liveIndex.run (arithmetic F G₁ G₂ K M cost) (key, xs, ())).steps ≤
      xs.length * (cost.messageEq + cost.point₁Eq + cost.natOp + 70) + 18 := by
  have hr := reverseList_steps_le (cell := .pair hashKey scalar) (Γ := [hashKey, hashCache])
    (arithmetic F G₁ G₂ K M cost) xs (key, xs, ())
  have hf := liveIndexFold_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost key xs.reverse
  have he := liveIndexFold.weakenTail_run (Δ := [hashKey, hashCache])
    (arithmetic F G₁ G₂ K M cost) (key, xs.reverse, ()) (key, xs, ())
  simp only [Env.append] at he
  have hv : ((reverseList (cell := .pair hashKey scalar) (Γ := [hashKey, hashCache])).run
      (arithmetic F G₁ G₂ K M cost) (xs, key, xs, ())).value = xs.reverse := by
    rw [Expr.run_value, reverseList_denote]
  simp only [liveIndex, Expr.run, Var.get, Var.depth, hv, he]
  simp only [List.length_reverse] at hf
  nlinarith

/-- Check `z*g = R + c*pk` using the live challenge returned by the pass. -/
def verifyObserved : Expr CryptoOp [forgery, scalar, point₁, point₁] .bool :=
  .op .point₁Eq (.pair
    (.op .scale₁ (.pair (.snd (.snd (.var .here))) (.var (.there (.there .here)))))
    (.op .add₁ (.pair (.fst (.snd (.var .here)))
      (.op .scale₁ (.pair (.var (.there .here)) (.var (.there (.there (.there .here)))))))))

theorem verifyObserved_run (cost : PrimitiveCosts) (msg : M) (R g pk : G₁) (z c : F) :
    verifyObserved.run (arithmetic F G₁ G₂ K M cost) ((msg, R, z), c, g, pk, ()) =
      ⟨decide (z • g = R + c • pk), 2 * cost.scalar₁ + cost.group + cost.point₁Eq + 23⟩ := by
  simp [verifyObserved, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price]
  omega

def guardIndex : Expr CryptoOp [indexResult, .nat] indexResult :=
  .branch (.fst (.var .here))
    (.branch (.op .natLt (.pair (.snd (.var .here))
      (.op .natAdd (.pair (.var (.there .here)) (.nat 1)))))
      (.var .here) (.pair (.bool false) (.nat 0)))
    (.pair (.bool false) (.nat 0))

def guarded (result : Bool × Nat) (qH : Nat) : Bool × Nat :=
  if result.1 = true ∧ result.2 < qH + 1 then result else (false, 0)

theorem guardIndex_run (cost : PrimitiveCosts) (result : Bool × Nat) (qH : Nat) :
    guardIndex.run (arithmetic F G₁ G₂ K M cost) (result, qH, ()) =
      ⟨guarded result qH,
        if result.1 then if result.2 < qH + 1 then 2 * cost.natOp + 15
          else 2 * cost.natOp + 17 else 6⟩ := by
  rcases result with ⟨found, n⟩
  cases found <;> by_cases h : n < qH + 1 <;>
    simp [guardIndex, guarded, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, h] <;> omega

variable {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}

/-- Verify first, then locate the target and check the public hash-query budget. -/
def selectCode : Program CryptoOp Cmd [observedForgery, cacheStore, .nat] indexResult :=
  .bind (.call (.ret verifyObserved)
    (.cons (.fst (.var .here)) (.cons (.snd (.var .here))
      (.cons (.fst (.fst (.var (.there .here))))
        (.cons (.snd (.fst (.var (.there .here)))) .nil)))))
    (.branch (.var .here)
      (.bind (.call (.ret liveIndex)
        (.cons (.pair (.fst (.fst (.var (.there .here))))
          (.fst (.snd (.fst (.var (.there .here))))))
          (.cons (.snd (.snd (.var (.there (.there .here))))) .nil)))
        (.call (.ret guardIndex)
          (.cons (.var .here) (.cons (.var (.there (.there (.there (.there .here))))) .nil))))
      (.ret (.pair (.bool false) (.nat 0))))

theorem selectCode_run {m : Type → Type} [Monad m] [LawfulMonad m]
    (cost : PrimitiveCosts) (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd m)
    (msg : M) (R g pk : G₁) (z c : F) (managed live : List ((M × G₁) × F)) (qH : Nat) :
    selectCode.run (arithmetic F G₁ G₂ K M cost) H
        (((msg, R, z), c), ((g, pk), managed, live), qH, ()) =
      let v := verifyObserved.run (arithmetic F G₁ G₂ K M cost) ((msg, R, z), c, g, pk, ())
      if v.value then
        let i := liveIndex.run (arithmetic F G₁ G₂ K M cost) ((msg, R), live, ())
        let checked := guardIndex.run (arithmetic F G₁ G₂ K M cost) (i.value, qH, ())
        pure ⟨checked.value, v.steps + i.steps + checked.steps + 57⟩
      else pure ⟨(false, 0), v.steps + 27⟩ := by
  unfold selectCode
  generalize verifyObserved = verify
  generalize liveIndex = find
  generalize guardIndex = guard
  dsimp [Program.run, Args.run, Expr.run, Var.get, Var.depth]
  by_cases hv : (verify.run (arithmetic F G₁ G₂ K M cost) ((msg, R, z), c, g, pk, ())).value = true <;>
    simp only [hv, pure_bind, Bool.false_eq_true, ite_true, ite_false] <;>
    apply congrArg pure <;> apply congrArg (Run.mk _) <;> omega

def selectionBound (cost : PrimitiveCosts) (liveLength : Nat) : Nat :=
  liveLength * (cost.messageEq + cost.point₁Eq + cost.natOp + 70) +
    2 * cost.scalar₁ + cost.group + cost.point₁Eq + 2 * cost.natOp + 115

theorem selectCode_bound {I : Type} {spec : OracleSpec I}
    (cost : PrimitiveCosts) (H : Handler (cryptoBase F G₁ G₂ K M) Cmd spec)
    (msg : M) (R g pk : G₁) (z c : F) (managed live : List ((M × G₁) × F)) (qH : Nat)
    (out : Run (Bool × Nat))
    (hout : out ∈ support (selectCode.run (arithmetic F G₁ G₂ K M cost) H
      (((msg, R, z), c), ((g, pk), managed, live), qH, ()))) :
    out.steps ≤ selectionBound cost live.length := by
  rw [selectCode_run, verifyObserved_run] at hout
  have hi := liveIndex_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost (msg, R) live
  by_cases hv : z • g = R + c • pk
  · simp only [hv, decide_true, ite_true] at hout
    rw [guardIndex_run] at hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst out
    dsimp [selectionBound]
    split <;> (try split) <;> omega
  · simp only [hv, decide_false, Bool.false_eq_true, ite_false, support_pure,
      Set.mem_singleton_iff] at hout
    subst out
    dsimp [selectionBound]
    omega

def selectValue (g pk : G₁) (forged : M × G₁ × F) (c : F)
    (live : List ((M × G₁) × F)) (qH : Nat) : Bool × Nat :=
  if forged.2.2 • g = forged.2.1 + c • pk then
    guarded (live.reverse.any (fun x => decide (x.1 = (forged.1, forged.2.1))),
      live.reverse.findIdx (fun x => decide (x.1 = (forged.1, forged.2.1)))) qH
  else (false, 0)

theorem selectCode_erase {m : Type → Type} [Monad m] [LawfulMonad m]
    (cost : PrimitiveCosts) (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd m)
    (msg : M) (R g pk : G₁) (z c : F) (managed live : List ((M × G₁) × F)) (qH : Nat) :
    Run.value <$> selectCode.run (arithmetic F G₁ G₂ K M cost) H
        (((msg, R, z), c), ((g, pk), managed, live), qH, ()) =
      pure (selectValue g pk (msg, R, z) c live qH) := by
  rw [selectCode_run, verifyObserved_run]
  by_cases hv : z • g = R + c • pk
  · simp only [hv, decide_true, ite_true]
    rw [guardIndex_run]
    simp only [map_pure, Expr.run_value,
      liveIndex_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M), selectValue,
      hv, ite_true]
  · simp [hv, selectValue]

/-- Proof-side decoding of the machine's checked natural-number index. The corresponding
comparison is executed by `guardIndex`, not delegated to this decoder. -/
def asIndex (qH : Nat) (result : Bool × Nat) : Option (Fin (qH + 1)) :=
  if h : result.1 = true ∧ result.2 < qH + 1 then some ⟨result.2, h.2⟩ else none

theorem asIndex_guarded (qH : Nat) (result : Bool × Nat) :
    asIndex qH (guarded result qH) = asIndex qH result := by
  unfold guarded
  split
  · rfl
  · rename_i h
    simp only [asIndex, h, dite_false, Bool.false_eq_true, false_and]

def passTrace (g pk : G₁) (forged : M × G₁ × F) (c : F)
    (managed live : List ((M × G₁) × F)) : FiatShamir.Fork.Trace G₁ F F M where
  forgery := forged
  advCache := managedState managed
  roCache := (liveState live).1
  queryLog := (liveState live).2
  verified := decide (forged.2.2 • g = forged.2.1 + c • pk)

omit [DecidableEq F] in
/-- Selection matches VCVio's statement: an accepting forgery whose target occurs in
the chronological live log, at an ordinal below `qH + 1`. -/
theorem selectValue_forkPoint (g pk : G₁) (forged : M × G₁ × F) (c : F)
    (managed live : List ((M × G₁) × F)) (qH : Nat) :
    asIndex qH (selectValue g pk forged c live qH) =
      FiatShamir.Fork.forkPoint G₁ F F M qH (passTrace g pk forged c managed live) := by
  have hmem : (live.reverse.any (fun x => decide (x.1 = (forged.1, forged.2.1)))) = true ↔
      (forged.1, forged.2.1) ∈ live.reverse.map Prod.fst := by
    simp [List.any_eq_true, List.mem_map]
  unfold selectValue FiatShamir.Fork.forkPoint
  dsimp only [passTrace, liveState, FiatShamir.Fork.Trace.target]
  by_cases hv : forged.2.2 • g = forged.2.1 + c • pk
  · simp only [hv, ite_true, decide_true]
    rw [asIndex_guarded]
    simp only [asIndex, List.findIdx_map, Function.comp_def]
    have heq : (fun x : (M × G₁) × F => x.1 == (forged.1, forged.2.1)) =
        (fun x => decide (x.1 = (forged.1, forged.2.1))) := by
      funext x
      apply Bool.eq_iff_iff.mpr
      simp
    simp only [heq]
    by_cases hm : (live.reverse.any (fun x => decide (x.1 = (forged.1, forged.2.1)))) = true
    · simp only [hm, hmem.mp hm, ite_true, true_and]
    · have hn := mt hmem.mpr hm
      simp only [hm, hn, ite_false, Bool.false_eq_true, false_and, dite_false]
  · simp [asIndex, hv]

end Signatures.Runtime.Schnorr
