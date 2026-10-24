import Proofs.Runtime.SchnorrRawTape
import Proofs.Schnorr.LazyROM

/-! The finite-list raw tape implements the complete named lazy Schnorr
reduction by computation equality, including extraction. This connects the
representation to the source security theorem; backend costs remain separate. -/

open OracleComp OracleSpec DiffieHellman

namespace Signatures.Runtime.Schnorr.RawTape

variable {F A : Type} [Zero F] [SampleableType F] [DecidableEq F]

def fork (main : OracleComp (Spec F) A) (qH : Nat)
    (select : A → Option (Fin (qH + 1))) : OracleComp (Spec F) (Option (A × A)) := do
  let first ← (simulateQ oracle main).run {}
  match select first.1 with
  | none => pure none
  | some slot =>
      let answer ← liftComp ($ᵗ F) (Spec F)
      if (values (.inr ()) first.2.saved)[slot.val]? = some answer then pure none
      else
        let second ← (simulateQ oracle main).run' (restart slot.val answer first.2)
        if select second = some slot then pure (some (first.1, second)) else pure none

/-- Complete controller equality on the raw interface, preserving the precise
ordering of caller and simulator draws within each original private family. -/
theorem fork_eq_lazy (main : OracleComp (Spec F) A) (qH : Nat)
    (select : A → Option (Fin (qH + 1))) :
    fork main qH select = _root_.Schnorr.LazyROM.fork main qH select := by
  simp only [fork, run_log main [], List.nil_append, bind_map_left,
    _root_.Schnorr.LazyROM.fork, SeededLazyFork.recordedFork]
  apply bind_congr
  intro first
  cases selected : select first.1 with
  | none => simp [SeededLazyFork.afterFirst, selected]
  | some slot =>
      simp only [SeededLazyFork.afterFirst, selected]
      apply bind_congr
      intro answer
      have encoded := congrFun (toSeed_encode first.2) (.inr ())
      change values (.inr ()) (encodeLog first.2) = _ at encoded
      rw [encoded]
      split
      · rfl
      · rw [run'_seeded, restart_seed, toSeed_encode]

variable {G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [SampleableType G] [DecidableEq G] [DecidableEq M]

/-- The named reduction with finite lists replacing the abstract seed lookup. -/
def dlogReduction (g : G) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (qH : Nat) : DLogAdversary F G := fun _ pk =>
  simulateQ _root_.Schnorr.LazyROM.sample
    (fork (_root_.Schnorr.LazyROM.main g pk adv) qH (FiatShamir.Fork.forkPoint G F F M qH) >>=
      FiatShamir.nmaForkExtractBranch (M := M) (_root_.Schnorr.sigma F G g))

theorem dlogReduction_eq_lazy (g : G)
    (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) (qH : Nat) :
    dlogReduction g adv qH = _root_.Schnorr.LazyROM.dlogReduction g adv qH := by
  funext generator pk
  simp only [dlogReduction, fork_eq_lazy, _root_.Schnorr.LazyROM.dlogReduction]

/-- The original security bound now applies to the exact finite-list reduction,
without a supplied private-family cover or restricted attacker language. -/
theorem security [Fintype F] (g : G)
    (generates : Function.Bijective (fun x : F => x • g))
    (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) (qS qH : Nat)
    (queries : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH) :
    let eps := 𝒟[_root_.Schnorr.ROM.game g adv] {true} -
      (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹
    eps * (eps / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[dlogExperiment g (dlogReduction g adv qH)] {true} := by
  rw [dlogReduction_eq_lazy]
  exact _root_.Schnorr.LazyROM.security g generates adv qS qH queries

end Signatures.Runtime.Schnorr.RawTape
