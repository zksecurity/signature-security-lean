import Signatures.Runtime.SchnorrROMListPass
import Signatures.Runtime.SchnorrNonzeroListPass

/-! One finite-list pass shape for every ROM signing simulator: an arbitrary
CMA handler followed by the final LIVE hash. The full-field and nonzero-nonce
passes are this shape at their respective handlers, definitionally. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.ListROM

abbrev Handler (F G₁ G₂ K M : Type) [Field F] [AddCommGroup G₁] [Module F G₁] :=
  QueryImpl (FiatShamir.cmaOracleSpec M G₁ F F)
    (StateT (cacheStore.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (expandedSpec F)))

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

def passWith (handler : Handler F G₁ G₂ K M) (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F)) :
    StateT (cacheStore.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (expandedSpec F)) ((M × G₁ × F) × F) := do
  let forged ← simulateQ handler main
  let c ← finalHash (forged.1, forged.2.1)
  pure (forged, c)

theorem pass_eq_passWith (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F)) :
    pass (G₂ := G₂) (K := K) main = passWith handler main := rfl

theorem nonzero_pass_eq_passWith [SampleableType Fˣ] (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F)) :
    NonzeroListROM.pass (G₂ := G₂) (K := K) main = passWith NonzeroListROM.handler main := rfl

theorem nonzero_handler_shared [SampleableType Fˣ] (i : Nat ⊕ (M × G₁)) :
    NonzeroListROM.handler (F := F) (G₂ := G₂) (K := K) (.inl i) = handler (F := F) (G₂ := G₂) (K := K) (.inl i) := rfl

end Signatures.Runtime.Schnorr.ListROM
