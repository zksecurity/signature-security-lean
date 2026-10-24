import Proofs.Runtime.SchnorrROMListPass
import Proofs.Runtime.SchnorrRawForkMap
import Proofs.Runtime.SchnorrReduction

/-! The general Schnorr ROM reduction with finite cache and tape outputs.
The proof-only map to VCVio's cache functions commutes with the fork; the
implemented pass stores lists of encountered entries. Exact computation
correspondence also covers the final extractor and fallback sampling. -/

open OracleComp OracleSpec DiffieHellman

namespace Signatures.Runtime.Schnorr.ListROM

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

def main (g pk : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) :
    OracleComp (RawTape.Spec F) (cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) :=
  (pass (adv.main pk)).run ((g, pk), [], [])

/-- Changing the output representation preserves the whole fork and extraction
computation, including rejection and fallback paths. -/
theorem fork_extract (g pk : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (qH : Nat) :
    (RawTape.fork (main (G₂ := G₂) (K := K) g pk adv) qH (selectPass PrimitiveCosts.unit qH) >>=
      fun p => liftRandom (extractFork p)) =
    (RawTape.fork (_root_.Schnorr.LazyROM.main g pk adv) qH (FiatShamir.Fork.forkPoint G₁ F F M qH) >>=
      FiatShamir.nmaForkExtractBranch (M := M) (_root_.Schnorr.sigma F G₁ g)) := by
  rw [← pass_trace (G₂ := G₂) (K := K) g pk adv, RawTape.fork_map]
  have hs : (FiatShamir.Fork.forkPoint G₁ F F M qH ∘ cacheTrace (G₂ := G₂) (K := K)) =
      selectPass PrimitiveCosts.unit qH := by
    funext p
    exact (selectPass_trace PrimitiveCosts.unit qH p).symm
  rw [hs, bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro result hr
  cases result with
  | none => rfl
  | some pair =>
      obtain ⟨hf, hs⟩ := RawTape.fork_outputs _ _ _ pair.1 pair.2 hr
      exact extractFork_trace g pair.1 pair.2
        (pass_valid (adv.main pk) g pk [] [] pair.1 hf).2
        (pass_valid (adv.main pk) g pk [] [] pair.2 hs).2

noncomputable def dlogReduction (g : G₁)
    (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) (qH : Nat) : DLogAdversary F G₁ :=
  fun _ pk => simulateQ _root_.Schnorr.LazyROM.sample
    (RawTape.fork (main (G₂ := G₂) (K := K) g pk adv) qH (selectPass PrimitiveCosts.unit qH) >>=
      fun p => liftRandom (extractFork p))

theorem dlogReduction_eq_raw (g : G₁)
    (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) (qH : Nat) :
    dlogReduction (G₂ := G₂) (K := K) g adv qH = RawTape.dlogReduction g adv qH := by
  funext generator pk
  exact congrArg (simulateQ _root_.Schnorr.LazyROM.sample)
    (fork_extract (G₂ := G₂) (K := K) g pk adv qH)

theorem dlogReduction_eq_lazy (g : G₁)
    (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) (qH : Nat) :
    dlogReduction (G₂ := G₂) (K := K) g adv qH = _root_.Schnorr.LazyROM.dlogReduction g adv qH :=
  (dlogReduction_eq_raw g adv qH).trans (RawTape.dlogReduction_eq_lazy g adv qH)

/-- The original concrete probability loss applies to the finite-cache,
finite-tape reduction. Backend efficiency is a separate implementation theorem. -/
theorem security [Fintype F] (g : G₁)
    (generates : Function.Bijective (fun x : F => x • g))
    (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) (qS qH : Nat)
    (queries : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH) :
    let eps := 𝒟[_root_.Schnorr.ROM.game g adv] {true} -
      (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹
    eps * (eps / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[dlogExperiment g (dlogReduction (G₂ := G₂) (K := K) g adv qH)] {true} := by
  rw [dlogReduction_eq_raw]
  exact RawTape.security g generates adv qS qH queries

end Signatures.Runtime.Schnorr.ListROM
