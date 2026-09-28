import Signatures.Runtime.ExtractionCore
import Signatures.Runtime.AGMOracle

/-! AGM extraction from the actual reversed simulator transcript and a first-order adversary
output. Coefficient attachment, chronological reversal, field sums, and division all execute
inside the same charged expression language. -/

namespace Signatures.Runtime.AGM

abbrev outputTy (messageTy : Ty CryptoAtom) : Ty CryptoAtom :=
  .pair messageTy (.pair scalar (.pair (.list scalar) (.list scalar)))

def outputView {F G₁ G₂ K M : Type} {messageTy : Ty CryptoAtom}
    (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    Model.LazyAGM.Output F (messageTy.Value (cryptoBase F G₁ G₂ K M)) :=
  ⟨out.1, out.2.1, out.2.2.1, out.2.2.2⟩

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
private def v5 {a b c d e f Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: Γ) f :=
  .var (.there (.there (.there (.there (.there .here)))))

variable {indexTy messageTy : Ty CryptoAtom}

def signingData : Expr CryptoOp [outputTy messageTy, transcriptTy indexTy messageTy]
    (denominatorData messageTy) :=
  .pair (.fst v0)
    (.letE (.snd (.snd (.snd v0))) (.letE (.snd v2)
      ((tokenRows (dataTy := messageTy)).weakenTail
        [outputTy messageTy, transcriptTy indexTy messageTy])))

def hashData : Expr CryptoOp [outputTy messageTy, transcriptTy indexTy messageTy]
    (tokenRowsTy indexTy) :=
  .letE (.fst (.snd (.snd v0))) (.letE (.fst v2)
    ((tokenRows (dataTy := indexTy)).weakenTail
      [outputTy messageTy, transcriptTy indexTy messageTy]))

def goodExtract (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [outputTy messageTy, transcriptTy indexTy messageTy, tableTy indexTy] scalar :=
  .letE (signingData.weakenTail [tableTy indexTy])
    (.letE (.letE v2 (.letE v2 (hashData.weakenTail
      [denominatorData messageTy, outputTy messageTy, transcriptTy indexTy messageTy, tableTy indexTy])))
      (.letE (.fst (.snd v2)) (.letE v5 ((goodCore eq weight).weakenTail
        [outputTy messageTy, transcriptTy indexTy messageTy, tableTy indexTy]))))

def badExtract (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp
      [outputTy messageTy, transcriptTy indexTy messageTy, tableTy indexTy, tableTy indexTy] scalar :=
  .letE (signingData.weakenTail [tableTy indexTy, tableTy indexTy])
    (.letE v4 (.letE v4 ((badCore weight).weakenTail
      [outputTy messageTy, transcriptTy indexTy messageTy, tableTy indexTy, tableTy indexTy])))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem signingData_run (cost : PrimitiveCosts)
    (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    (signingData (indexTy := indexTy) (messageTy := messageTy)).run (arithmetic F G₁ G₂ K M cost) (out, tr, ()) =
      let r := (tokenRows (dataTy := messageTy)).run
        (arithmetic F G₁ G₂ K M cost) (tr.2, out.2.2.2, ())
      ⟨(out.1, r.value), r.steps + 13⟩ := by
  have h := (tokenRows (dataTy := messageTy)).weakenTail_run
    (Δ := [outputTy messageTy, transcriptTy indexTy messageTy])
    (arithmetic F G₁ G₂ K M cost) (tr.2, out.2.2.2, ()) (out, tr, ())
  simp only [Env.append] at h
  dsimp [arithmetic, CryptoOp.price] at h ⊢
  simp only [signingData, Expr.run, v0, v2, Var.get, Var.depth, h]
  apply congrArg (Run.mk _)
  omega

theorem hashData_run (cost : PrimitiveCosts)
    (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    (hashData (indexTy := indexTy) (messageTy := messageTy)).run (arithmetic F G₁ G₂ K M cost) (out, tr, ()) =
      let r := (tokenRows (dataTy := indexTy)).run
        (arithmetic F G₁ G₂ K M cost) (tr.1, out.2.2.1, ())
      ⟨r.value, r.steps + 10⟩ := by
  have h := (tokenRows (dataTy := indexTy)).weakenTail_run
    (Δ := [outputTy messageTy, transcriptTy indexTy messageTy])
    (arithmetic F G₁ G₂ K M cost) (tr.1, out.2.2.1, ()) (out, tr, ())
  simp only [Env.append] at h
  dsimp [arithmetic, CryptoOp.price] at h ⊢
  simp only [hashData, Expr.run, v0, v2, Var.get, Var.depth, h]
  apply congrArg (Run.mk _)
  omega

theorem goodExtract_run (cost : PrimitiveCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (rho : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) :
    (goodExtract eq weight).run (arithmetic F G₁ G₂ K M cost) (out, tr, rho, ()) =
      let h := (hashData (indexTy := indexTy) (messageTy := messageTy)).run (arithmetic F G₁ G₂ K M cost) (out, tr, ())
      let s := (signingData (indexTy := indexTy) (messageTy := messageTy)).run (arithmetic F G₁ G₂ K M cost) (out, tr, ())
      let r := (goodCore eq weight).run (arithmetic F G₁ G₂ K M cost)
        (rho, out.2.1, h.value, s.value, ())
      ⟨r.value, h.steps + s.steps + r.steps + 23⟩ := by
  have hs := (signingData (indexTy := indexTy) (messageTy := messageTy)).weakenTail_run
    (Δ := [tableTy indexTy]) (arithmetic F G₁ G₂ K M cost) (out, tr, ()) (rho, ())
  let s := (signingData (indexTy := indexTy) (messageTy := messageTy)).run (arithmetic F G₁ G₂ K M cost) (out, tr, ())
  let h := (hashData (indexTy := indexTy) (messageTy := messageTy)).run (arithmetic F G₁ G₂ K M cost) (out, tr, ())
  have hh := (hashData (indexTy := indexTy) (messageTy := messageTy)).weakenTail_run
    (Δ := [denominatorData messageTy, outputTy messageTy, transcriptTy indexTy messageTy, tableTy indexTy])
    (arithmetic F G₁ G₂ K M cost) (out, tr, ()) (s.value, out, tr, rho, ())
  have hr := (goodCore eq weight).weakenTail_run
    (Δ := [outputTy messageTy, transcriptTy indexTy messageTy, tableTy indexTy])
    (arithmetic F G₁ G₂ K M cost) (rho, out.2.1, h.value, s.value, ()) (out, tr, rho, ())
  simp only [Env.append] at hs hh hr
  dsimp [s, h, arithmetic, CryptoOp.price] at hs hh hr ⊢
  simp only [goodExtract, Expr.run, v2, v5, Var.get, Var.depth, hs, hh, hr]
  apply congrArg (Run.mk _)
  omega

theorem badExtract_run (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (a b : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) :
    (badExtract weight).run (arithmetic F G₁ G₂ K M cost) (out, tr, a, b, ()) =
      let s := (signingData (indexTy := indexTy) (messageTy := messageTy)).run (arithmetic F G₁ G₂ K M cost) (out, tr, ())
      let r := (badCore weight).run (arithmetic F G₁ G₂ K M cost) (a, b, s.value, ())
      ⟨r.value, s.steps + r.steps + 13⟩ := by
  have hs := (signingData (indexTy := indexTy) (messageTy := messageTy)).weakenTail_run
    (Δ := [tableTy indexTy, tableTy indexTy]) (arithmetic F G₁ G₂ K M cost) (out, tr, ()) (a, b, ())
  have hr := (badCore weight).weakenTail_run
    (Δ := [outputTy messageTy, transcriptTy indexTy messageTy, tableTy indexTy, tableTy indexTy])
    (arithmetic F G₁ G₂ K M cost)
    (a, b, ((signingData (indexTy := indexTy) (messageTy := messageTy)).run (arithmetic F G₁ G₂ K M cost) (out, tr, ())).value, ())
    (out, tr, a, b, ())
  simp only [Env.append] at hs hr
  dsimp [arithmetic, CryptoOp.price] at hs hr ⊢
  simp only [badExtract, Expr.run, v4, Var.get, Var.depth, hs, hr]
  apply congrArg (Run.mk _)
  omega

def goodExtractBound (cost : PrimitiveCosts) (n h s gamma xi e w : Nat) : Nat :=
  tokenRowsBound cost h gamma + tokenRowsBound cost s xi + goodCoreBound cost n h s e w + 46

def badExtractBound (cost : PrimitiveCosts) (na nb s xi w : Nat) : Nat :=
  tokenRowsBound cost s xi + badCoreBound cost na nb s w + 26

theorem goodExtractBound_mono (cost : PrimitiveCosts) (n e w : Nat)
    {h s gamma xi h' s' gamma' xi' : Nat}
    (hh : h ≤ h') (hs : s ≤ s') (hg : gamma ≤ gamma') (hx : xi ≤ xi') :
    goodExtractBound cost n h s gamma xi e w ≤ goodExtractBound cost n h' s' gamma' xi' e w := by
  dsimp [goodExtractBound, tokenRowsBound, goodCoreBound, baseCoefficientBound, denominatorWeightBound]
  gcongr

theorem badExtractBound_mono (cost : PrimitiveCosts) (na nb w : Nat)
    {s xi s' xi' : Nat} (hs : s ≤ s') (hx : xi ≤ xi') :
    badExtractBound cost na nb s xi w ≤ badExtractBound cost na nb s' xi' w := by
  dsimp [badExtractBound, tokenRowsBound, badCoreBound, denominatorWeightBound]
  gcongr

theorem goodExtract_value (cost : PrimitiveCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (rho : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) :
    ((goodExtract eq weight).run (arithmetic F G₁ G₂ K M cost) (out, tr, rho, ())).value =
      ((goodCore eq weight).run (arithmetic F G₁ G₂ K M cost)
        (rho, out.2.1, tr.1.reverse.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.2.2.1 n)),
          (out.1, tr.2.reverse.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.2.2.2 n))), ())).value := by
  rw [goodExtract_run]
  simp only [hashData_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    signingData_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    tokenRows_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]

theorem badExtract_value (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (a b : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) :
    ((badExtract weight).run (arithmetic F G₁ G₂ K M cost) (out, tr, a, b, ())).value =
      ((badCore weight).run (arithmetic F G₁ G₂ K M cost)
        (a, b, (out.1, tr.2.reverse.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.2.2.2 n))), ())).value := by
  rw [badExtract_run]
  simp only [signingData_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    tokenRows_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]

theorem goodExtract_steps_le (cost : PrimitiveCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (e w : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ w)
    (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (rho : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) :
    ((goodExtract eq weight).run (arithmetic F G₁ G₂ K M cost) (out, tr, rho, ())).steps ≤
      goodExtractBound cost rho.length tr.1.length tr.2.length out.2.2.1.length out.2.2.2.length e w := by
  have hh := tokenRows_steps_le (dataTy := indexTy) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost tr.1 out.2.2.1
  have hs := tokenRows_steps_le (dataTy := messageTy) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost tr.2 out.2.2.2
  have hc := goodCore_steps_le (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost eq weight e w heq hw rho out.2.1
    (tr.1.reverse.mapIdx fun n p => (p, Model.LazyAGM.tokenCoeff out.2.2.1 n))
    (out.1, tr.2.reverse.mapIdx fun n p => (p, Model.LazyAGM.tokenCoeff out.2.2.2 n))
  simp only [List.length_mapIdx, List.length_reverse] at hc
  rw [goodExtract_run]
  simp only [hashData_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    signingData_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    tokenRows_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  refine (Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add_right hh 10) (Nat.add_le_add_right hs 13)) hc) 23).trans ?_
  dsimp only [goodExtractBound]
  omega

theorem badExtract_steps_le (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : Nat)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ w)
    (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (a b : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) :
    ((badExtract weight).run (arithmetic F G₁ G₂ K M cost) (out, tr, a, b, ())).steps ≤
      badExtractBound cost a.length b.length tr.2.length out.2.2.2.length w := by
  have hs := tokenRows_steps_le (dataTy := messageTy) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost tr.2 out.2.2.2
  have hc := badCore_steps_le (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost weight w hw a b
    (out.1, tr.2.reverse.mapIdx fun n p => (p, Model.LazyAGM.tokenCoeff out.2.2.2 n))
  simp only [List.length_mapIdx, List.length_reverse] at hc
  rw [badExtract_run]
  simp only [signingData_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    tokenRows_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  refine (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right hs 13) hc) 13).trans ?_
  dsimp only [badExtractBound]
  omega

end Signatures.Runtime.AGM
