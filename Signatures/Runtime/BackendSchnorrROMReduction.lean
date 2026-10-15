import Signatures.Runtime.BackendSchnorrROMSolver

/-! The finite-cache/tape solver as a general DLog algorithm. It uses its
generator input, so one implementation realizes it at every input. At the
scheme generator its computation equals the named lazy Schnorr reduction. -/

open OracleComp OracleSpec DiffieHellman

namespace Signatures.Runtime.Schnorr.ListROM.NativeSolver

open NativeInterface

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

noncomputable def reduction (attacker : G₁ → OracleComp (sourceSpec F G₁ M) (M × G₁ × F))
    (qH : Nat) : DLogAdversary F G₁ :=
  fun g pk => simulateQ _root_.Schnorr.LazyROM.sample
    (RawTape.fork ((ListROM.pass (G₂ := G₂) (K := K) (attacker pk)).run ((g, pk), [], []))
      qH (selectPass PrimitiveCosts.unit qH) >>= fun result => liftRandom (extractFork result))

theorem reduction_at_generator [SampleableType G₁] (g : G₁)
    (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) (qH : Nat) (pk : G₁) :
    reduction (G₂ := G₂) (K := K) adv.main qH g pk =
      _root_.Schnorr.LazyROM.dlogReduction g adv qH g pk :=
  congrFun (congrFun (dlogReduction_eq_lazy (G₂ := G₂) (K := K) g adv qH) g) pk

theorem reduction_experiment [SampleableType G₁] (g : G₁)
    (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) (qH : Nat) :
    dlogExperiment g (reduction (G₂ := G₂) (K := K) adv.main qH) =
      dlogExperiment g (_root_.Schnorr.LazyROM.dlogReduction g adv qH) := by
  unfold dlogExperiment
  apply bind_congr
  intro x
  rw [reduction_at_generator]

end Signatures.Runtime.Schnorr.ListROM.NativeSolver
