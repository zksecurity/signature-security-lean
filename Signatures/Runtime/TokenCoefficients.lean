import Signatures.Runtime.AttachTable
import Signatures.Model.LazyAGM

/-! Attach adversary coefficients to the chronological explicit-query transcript. Simulator
logs are stored backwards; reversal and indexed coefficient lookup are executed and charged.
Missing coefficients are zero and surplus coefficients do not create transcript entries. -/

namespace Signatures.Runtime.AGM

abbrev tokenTy (dataTy : Ty CryptoAtom) : Ty CryptoAtom := .pair dataTy point₁
abbrev tokenRowsTy (dataTy : Ty CryptoAtom) : Ty CryptoAtom := tableTy (tokenTy dataTy)

variable {dataTy : Ty CryptoAtom}

def tokenRows : Expr CryptoOp [.list (tokenTy dataTy), .list scalar] (tokenRowsTy dataTy) :=
  .letE (.var (.there .here))
    (.letE (.letE (.var (.there .here)) reverseList)
      (.letE (.op .zero .unit)
        ((attachTable (indexTy := tokenTy dataTy)).weakenTail
          [.list (tokenTy dataTy), .list scalar])))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem tokenRows_run (cost : PrimitiveCosts)
    (tr : List (dataTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) :
    (tokenRows (dataTy := dataTy)).run (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()) =
      let rev := (reverseList (cell := tokenTy dataTy)
        (Γ := [.list scalar, .list (tokenTy dataTy), .list scalar])).run
          (arithmetic F G₁ G₂ K M cost) (tr, coeff, tr, coeff, ())
      let rows := (attachTable (indexTy := tokenTy dataTy)).run
        (arithmetic F G₁ G₂ K M cost) (0, tr.reverse, coeff, ())
      ⟨rows.value, rev.steps + rows.steps + cost.field + 10⟩ := by
  have ha := (attachTable (indexTy := tokenTy dataTy)).weakenTail_run
    (Δ := [.list (tokenTy dataTy), .list scalar]) (arithmetic F G₁ G₂ K M cost)
    (0, tr.reverse, coeff, ()) (tr, coeff, ())
  have hr : ((reverseList (cell := tokenTy dataTy)
      (Γ := [.list scalar, .list (tokenTy dataTy), .list scalar])).run
      (arithmetic F G₁ G₂ K M cost) (tr, coeff, tr, coeff, ())).value = tr.reverse := by
    rw [Expr.run_value, reverseList_denote]
  simp only [Env.append] at ha
  dsimp [arithmetic, CryptoOp.price] at ha hr ⊢
  simp only [tokenRows, Expr.run, Var.get, Var.depth, hr, ha]
  congr 1
  omega

theorem tokenRows_value (cost : PrimitiveCosts)
    (tr : List (dataTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) :
    ((tokenRows (dataTy := dataTy)).run (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())).value =
      tr.reverse.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff coeff n)) := by
  rw [tokenRows_run]
  exact attachTable_value (indexTy := tokenTy dataTy)
    (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost 0 tr.reverse coeff

def tokenRowsBound (cost : PrimitiveCosts) (n c : Nat) : Nat :=
  n * (c * (2 * cost.natOp + 26) + cost.natOp + 70) + cost.field + 29

theorem tokenRows_steps_le (cost : PrimitiveCosts)
    (tr : List (dataTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) :
    ((tokenRows (dataTy := dataTy)).run (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())).steps ≤
      tokenRowsBound cost tr.length coeff.length := by
  rw [tokenRows_run]
  have ha := attachTable_steps_le (indexTy := tokenTy dataTy)
    (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost 0 tr.reverse coeff
  have hr := reverseList_steps_le (cell := tokenTy dataTy)
    (Γ := [.list scalar, .list (tokenTy dataTy), .list scalar])
    (arithmetic F G₁ G₂ K M cost) tr (coeff, tr, coeff, ())
  simp only [List.length_reverse] at ha
  dsimp [tokenRowsBound]
  nlinarith

theorem tokenRows_length (cost : PrimitiveCosts)
    (tr : List (dataTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) :
    ((tokenRows (dataTy := dataTy)).run (arithmetic F G₁ G₂ K M cost)
      (tr, coeff, ())).value.length = tr.length := by
  rw [tokenRows_value, List.length_mapIdx, List.length_reverse]

end Signatures.Runtime.AGM
