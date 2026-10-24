import Proofs.Runtime.Caliper.SchnorrROMHashRoute

/-! Complete managed/LIVE hashing. A managed hit bypasses LIVE and replay;
a miss reads LIVE and inserts the returned scalar into the managed table. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Hash
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def cacheCode := StatefulCacheRead.code (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
  (Fresh.port config.handler.sampler.tape) (model config) (Signing.Cache.primitives F G M)
  Signing.Cache.comparison (Signing.Cache.comparison_correct F G M) (HashMiss.code config)
def cacheSource := StatefulCacheRead.denote (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
  (model config) (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M) (HashMiss.source config)
def cacheReady := StatefulCacheRead.readyOnMiss (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
  (model config) (Signing.Cache.primitives F G M) Signing.Cache.comparison (HashMiss.ready config)

theorem cache_refines : Interactive.RefinesOn (cacheReady config) (Fresh.port config.handler.sampler.tape) .unit
    (model config).input (model config).output (cacheSource config) (cacheCode config) :=
  StatefulCacheRead.refines_on_miss (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
    (Fresh.port config.handler.sampler.tape) (model config) (Signing.Cache.primitives F G M)
    Signing.Cache.comparison (Signing.Cache.comparison_correct F G M) (HashMiss.refines config)

def code : Interactive.Code w := .seq (.compute (prepare config).code)
  (.seq (cacheCode config) (.compute (finish config).code))
def source (value : (input config).Value) : ProbComp (output config).Value :=
  finishValue config <$> cacheSource config (prepareValue config value)

theorem refines : Interactive.RefinesOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config).representation (output config).representation (source config) (code config) := by
  have suffix := (cache_refines config).seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (finish config)).on (fun _ => True))
    (by intros; trivial)
  have compiled := ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (prepare config)).on (ready config)).seq
    suffix (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact selected_ready config value valid)
  convert compiled using 1
  · funext value
    simp only [source, pure_bind, bind_pure_comp]
  · rfl

end Signatures.Runtime.CaliperBackend.SchnorrROM.Hash
