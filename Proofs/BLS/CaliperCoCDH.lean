import Signatures.BLS.CaliperCoCDHParameters

/-! Membership of the original lazy Coron reduction in the fixed public
Caliper solver class follows from its constructed implementation. -/
namespace BLS.CaliperCoCDH
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
variable {F G K M : Type} [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [AddCommGroup K] [Module F K] [DecidableEq M]
    {queries : QueryAllowance} {generator : G} {keyGenerator : K}
    (P : Parameters F G K M queries generator keyGenerator) (A : Adversary P)
    (generates : Function.Surjective (fun scalar : F => scalar • generator))

include generates in
theorem reduction_within :
    P.within P.solverTime (CoCDH.coronReductionLazyPK (F := F) queries.sign (ROM.cacheForgeryPK A.source)) := by
  exact CoronFull.coCDH_within P.service P.key P.layout P.input_eq P.challengeFits
    P.defaultScalar P.routines P.sampler P.arithmetic A.caller (Adversary.bounds P A)
    queries.total P.fallback A.invariant A.correspondence A.inputView P.cacheRoom P.logRoom P.addresses
    P.scalarKeyFits P.keyScale ⟨generator, P.generatorValid⟩ ⟨keyGenerator, P.keyGeneratorValid⟩ generates
    A.source (fun pk => by rw [A.inputView]; exact A.source_eq pk)

end BLS.CaliperCoCDH
