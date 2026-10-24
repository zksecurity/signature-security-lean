import Proofs.Runtime.Caliper.SchnorrAGMReadPack
import Proofs.Runtime.Caliper.SchnorrAGMReadFinish

/-! Complete executed Schnorr AGM read: pack the arguments, preserve metadata
outside the cache's scratch footprint, then restore the complete output state.
Only local scalar sampling and addition implementations are supplied. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS) (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (slotsFit : slots < 2 ^ w)
    (port : Interactive.Port w spec)

def retained (sampler : Interactive.Code w) : Interactive.Code w :=
  Interactive.retain (Cache.code layout zeroValid add addBuffers slotsFit port sampler)
    (Interactive.savedBuffer port (Cache.code layout zeroValid add addBuffers slotsFit port sampler))
    (Cache.model layout).input.encoding.words (Cache.model layout).output.encoding.words layout.metadata.representation.encoding.words

def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (pack layout zeroValid).code)
    (.seq (retained layout zeroValid add addBuffers slotsFit port sampler) (.compute (finish layout).code))

def source (sampler : OracleComp spec layout.scalar.Value) (value : (input layout).Value) :
    OracleComp spec (output layout).Value :=
  (fun result => returnValue layout (result, inputMetadata layout value)) <$>
    Cache.source layout sampler (packValue layout zeroValid value).1

theorem retained_refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit (packed layout) (returned layout)
      (fun value => (fun result => (result, value.2)) <$> Cache.source layout sampleSource value.1)
      (retained layout zeroValid add addBuffers slotsFit port sampler) :=
  (Cache.refines layout zeroValid add addBuffers slotsFit port sampleCorrect).retain (by decide)
    layout.metadata.representation layout.wordFits (packed layout).fits (returned layout).fits

theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit (input layout).representation (output layout).representation
      (source layout zeroValid sampleSource) (code layout zeroValid add addBuffers slotsFit port sampler) := by
  have combined := (Interactive.Refines.compute port .unit (pack layout zeroValid)).seq
    ((retained_refines layout zeroValid add addBuffers slotsFit port sampleCorrect).seq
      (Interactive.Refines.compute port .unit (finish layout)))
  convert combined using 1
  · funext value
    simp only [pure_bind, bind_pure_comp, Functor.map_map, source]
    rfl
  · rfl

theorem cache_buffers (sampler : Interactive.Code w) {sampleSlots : Nat}
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    ((Cache.code layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound ≤
      max 9 (Fresh.nameBudget slots sampleSlots + 1) := by
  have cached := StatefulCacheRead.buffers (base := cryptoBase F G Unit M M)
    (key := Signatures.Runtime.SchnorrAGM.Native.cacheKeyTy) (val := Signatures.Runtime.SchnorrAGM.Native.entryTy)
    port (Cache.model layout) (Cache.primitives F G M) Cache.comparison (Cache.comparison_correct F G M)
    (Fresh.code layout zeroValid add addBuffers slotsFit port sampler)
  have fresh := (Fresh.names layout zeroValid add addBuffers slotsFit port sampler addNames sampleNames).buffers
  exact cached.trans (by omega)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
