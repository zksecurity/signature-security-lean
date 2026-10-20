import Signatures.Runtime.Caliper.SchnorrROMHashCache

/-! The constructed hash cache implements lazy lookup over the original public
replay oracle. The joint result includes the updated cache and both tapes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.HashCache
open Caliper BoundedSource OracleComp OracleSpec SchnorrROMTape
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

theorem source_value (value : (model config).cache.input.Value × (Read.tapes config.handler.sampler.tape).Value) :
    (fun answer => (answer.1.val, answer.2.val)) <$> source config value =
      match cacheMap value.1.val.2.2.1 value.1.val.1 with
      | some challenge => pure ((challenge, value.1.val.2.2.1), value.2.val)
      | none => (fun fresh => ((fresh.1.val, (value.1.val.1, fresh.1.val) :: value.1.val.2.2.1), fresh.2.val)) <$>
          EnumeratedReplay.drawSource config.sampler value.2 := by
  have erased := congrArg
    (fun computation : ProbComp ((F × List ((M × G) × F)) × (Read.tapes config.handler.sampler.tape).Value) =>
      (fun answer => (answer.1, answer.2.val)) <$> computation)
    (StatefulCacheRead.denote_value (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
      (model config) (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)
      (EnumeratedReplay.drawSource config.sampler) value)
  have looked : (lookupExpr (val := scalar) Signing.Cache.comparison).denote (Signing.Cache.primitives F G M) value.1.val =
      lookupValue value.1.val.1 value.1.val.2.1 value.1.val.2.2.1 := by
    simpa only [Expr.run_value] using lookupExpr_value (val := scalar) (Signing.Cache.primitives F G M) Signing.Cache.comparison
      (Signing.Cache.comparison_correct F G M) value.1.val.1 value.1.val.2.1 value.1.val.2.2.1
  rw [looked, lookupValue_cacheMap] at erased
  have joint := (PFunctor.FreeM.comp_map
    (fun answer : (F × List ((M × G) × F)) × (Read.tapes config.handler.sampler.tape).Value => (answer.1, answer.2.val))
    (fun answer : (CacheRead.output (model config).cache).Value × (Read.tapes config.handler.sampler.tape).Value =>
      (answer.1.val, answer.2)) (source config value)).trans erased
  refine joint.trans ?_
  cases found : cacheMap value.1.val.2.2.1 value.1.val.1 <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, map_pure]
  exact (PFunctor.FreeM.comp_map _ _ _).symm

theorem source_original (value : (model config).cache.input.Value × (Read.tapes config.handler.sampler.tape).Value)
    (valid : ready config value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun answer => (answer.1.val, answer.2.val)) <$> source config value =
      match cacheMap value.1.val.2.2.1 value.1.val.1 with
      | some challenge => pure ((challenge, value.1.val.2.2.1), value.2.val)
      | none => (fun fresh => ((fresh.1, (value.1.val.1, fresh.1) :: value.1.val.2.2.1), fresh.2)) <$>
          (Caller.scalarResult <$> simulateQ _root_.Schnorr.LazyROM.sample
            ((Schnorr.RawTape.oracle (.inr ())).run ⟨value.2.val.1, value.2.val.2⟩)) := by
  rw [source_value]
  split
  · rfl
  · exact (PFunctor.FreeM.comp_map
      (fun fresh : F × Schnorr.ListROM.Shared.Tape F => ((fresh.1, (value.1.val.1, fresh.1) :: value.1.val.2.2.1), fresh.2))
      (fun fresh : config.handler.sampler.tape.scalar.Value × (Read.tapes config.handler.sampler.tape).Value =>
        (fresh.1.val, fresh.2.val)) (EnumeratedReplay.drawSource config.sampler value.2)).trans
        (congrArg (Functor.map (fun fresh : F × Schnorr.ListROM.Shared.Tape F =>
          ((fresh.1, (value.1.val.1, fresh.1) :: value.1.val.2.2.1), fresh.2)))
          (EnumeratedReplay.draw_source config.sampler value.2 valid))

end Signatures.Runtime.CaliperBackend.SchnorrROM.HashCache
