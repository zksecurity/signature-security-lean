import Signatures.Runtime.Caliper.SchnorrROMSigningCore
import Signatures.Runtime.SchnorrROMSharedState

/-! Exact correspondence with the deterministic suffix of the original
shared-tape signing oracle. Its managed and LIVE caches remain distinct. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing
open OracleComp OracleSpec
variable {F G G₂ K M : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem Cache.update_original (key : M × G) (challenge : F) (managed : Table M F G) :
    Cache.update (key, challenge, managed, ()) =
      (cacheProgram (val := scalar) Schnorr.hashEq).denote (arithmetic F G G₂ K M PrimitiveCosts.unit)
        (key, challenge, managed, ()) := by
  symm
  simpa only [Expr.run_value, Cache.update] using cacheProgram_value (val := scalar)
    (arithmetic F G G₂ K M PrimitiveCosts.unit) Schnorr.hashEq
    (Schnorr.hashEq_value (F := F) (G₂ := G₂) (K := K) PrimitiveCosts.unit) key challenge managed

theorem Core.value_original (input : Input M F G) : Core.value input =
    ((input.1.2 • input.2.1 - input.1.1 • input.2.2.1, input.1.2), (input.2.1, input.2.2.1),
      (cacheProgram (val := scalar) Schnorr.hashEq).denote (arithmetic F G G₂ K M PrimitiveCosts.unit)
        ((input.2.2.2.1, input.1.2 • input.2.1 - input.1.1 • input.2.2.1), input.1.1, input.2.2.2.2, ())) := by
  unfold Core.value Arithmetic.commitment
  rw [Cache.update_original (G₂ := G₂) (K := K)]

variable [SampleableType F]

/-- Signing's source program draws twice through one tape, then applies exactly
the deterministic function implemented by `Core.implementation`. LIVE is passed
through unchanged; that preservation will be executed by the handler wrapper. -/
theorem signing_run (msg : M) (saved : Schnorr.ListROM.Shared.Store F G M) :
    (Schnorr.ListROM.Shared.interpret (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (.inr msg))).run saved = (do
      let first ← Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (F := F) (.inr ())) saved.2
      let second ← Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (F := F) (.inr ())) first.2
      let computed := Core.value ((first.1, second.1), saved.1.1.1, saved.1.1.2, msg, saved.1.2.1)
      pure (computed.1, (computed.2.1, computed.2.2, saved.1.2.2), second.2)) := by
  rw [Schnorr.ListROM.Shared.signing_run]
  apply bind_congr
  intro first
  apply bind_congr
  intro second
  rw [Core.value_original (G₂ := G₂) (K := K)]
  rfl

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing
