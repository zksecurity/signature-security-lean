import Proofs.Runtime.Caliper.SchnorrROMTerminalBounds

/-! The terminal source retains the original forgery and the joint oracle store.
Cutoff has a separate result and performs no random-oracle operation. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Terminal
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
section Layout
variable {w : Nat} {M F G P : Type} (config : Signing.Enumerated.Configuration w M F G)

def observed (value : Output config) : Option ((M × G × F) × F) × Schnorr.ListROM.Shared.Store F G M :=
  (Sum.elim (fun _ => none) (fun result => some (result.1.val, result.2.val)) value.1, value.2.val)

variable [Zero F] [DecidableEq M] [DecidableEq G]
theorem source_cutoff (next : P) (saved : config.handler.store.Value) :
    observed config <$> source config (.inr next, saved) = pure (none, saved.val) := by
  simp only [source, map_pure, observed, Sum.elim_inl]

theorem preserves_config (value : Input config (P := P)) (answer : Output config)
    (reached : answer ∈ support (source config value)) : answer.2.val.1.1 = value.2.val.1.1 := by
  rcases value with ⟨forge | next, saved⟩
  · simp only [source, successSource, support_map, Set.mem_image] at reached
    obtain ⟨hashed, supported, rfl⟩ := reached
    exact ForgeryHash.preserves_config config (forge, saved) hashed supported
  · simp only [source, support_pure, Set.mem_singleton_iff] at reached
    subst answer
    rfl
end Layout

section Original
variable {w : Nat} {M F G G₂ K P : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G] [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K]
    (config : Signing.Enumerated.Configuration w M F G)

theorem source_returned (forge : (ForgeryHash.forgery config).Value) (saved : config.handler.store.Value)
    (valid : ForgeryHash.ready config (forge, saved)) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> source config (P := P) (.inl forge, saved) =
      (fun hashed => (some (forge.val, hashed.1), hashed.2)) <$>
        (Schnorr.ListROM.Shared.interpret
          (Schnorr.ListROM.finalHash (G₂ := G₂) (K := K) (ForgeryHash.key config forge))).run saved.val := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have same := ForgeryHash.source_original (G₂ := G₂) (K := K) config (forge, saved) valid
  have mapped := congrArg (Functor.map (fun result : ((M × G × F) × F) × Schnorr.ListROM.Shared.Store F G M =>
    (some result.1, result.2))) same
  simpa only [source, successSource, Functor.map_map, observed, Sum.elim_inr, ForgeryHash.observed] using mapped

end Original
end Signatures.Runtime.CaliperBackend.SchnorrROM.Terminal
