import Signatures.Runtime.Caliper.BLSSetupLayout

/-! Actual local setup code for both BLS branches. The good branch selects its
runtime public key; the bad branch computes its key using an individual scale
routine. Both build the complete empty store with charged instructions. -/

namespace Signatures.Runtime.CaliperBackend.BLSSetup
open Caliper BoundedSource

variable {w : Nat} {M F G K : Type} (layout : Layouts w M F G K)

def good : Implementation .unit layout.challenge layout.goodOutput
    (fun value => (value.2.2, value.1, [], [], [])) :=
  (goodPrefix layout).then (BLSInitialization.implementation layout.scheme.good layout.key layout.goodFits)

theorem good_buffers : (good layout).program.code.memBound ≤ 3 :=
  max_le (goodPrefix_buffers layout)
    ((BLSInitialization.implementation_buffers layout.scheme.good layout.key layout.goodFits).trans (by decide))

theorem good_reserved (remaining : Nat) (cacheRoom : remaining ≤ layout.scheme.cache.capacityPred + 1)
    (logRoom : remaining ≤ layout.scheme.capacityPred + 1) (value : layout.challenge.Value) :
    BLSReply.Reserved layout.scheme.good remaining (value.val.1, [], [], []) :=
  BLSInitialization.reserved layout.scheme.good remaining cacheRoom logRoom ⟨value.val.1, value.property.1⟩

variable [SMul F K]
    (scale : Implementation .unit layout.scaleArgs layout.key (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)

def signingKey : Implementation .unit layout.sampled layout.key (fun value => value.1 • value.2.2.1) :=
  (arguments layout).then scale

include scaleBuffers in
theorem signingKey_buffers : (signingKey layout scale).program.code.memBound ≤ max 3 slots :=
  max_le_max (arguments_buffers layout) scaleBuffers

def badPrefix : Implementation .unit layout.sampled layout.badPrefix
    (fun value => (value.1 • value.2.2.1, value.1, value.2.1)) :=
  (signingKey layout scale).pair (config layout) (by decide) layout.scheme.cache.wordFits
    (layout.nameFits _ (signingKey_buffers layout scale scaleBuffers) (by have := layout.scheme.cache.wordFits; have := reserve; omega))
    (layout.nameFits _ (config_buffers layout) (by have := layout.scheme.cache.wordFits; omega))
    (layout.fits_of_le (by have := layout.sizes; omega))
    (layout.fits_of_le (by have := layout.sizes; omega)) _

def badLocal : Implementation .unit layout.sampled layout.badOutput
    (fun value => (value.1 • value.2.2.1, (value.1, value.2.1), [], [], [])) :=
  (badPrefix layout scale scaleBuffers reserve).then
    (BLSInitialization.implementation layout.scheme.bad layout.key layout.badFits)

theorem badPrefix_buffers : (badPrefix layout scale scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 1 := by
  have bounded : (badPrefix layout scale scaleBuffers reserve).program.code.memBound ≤ max 2 (max (max 3 slots) 3) + 1 :=
    Implementation.pair_buffers (signingKey layout scale) (config layout) layout.scheme.cache.wordFits
    _ _ _ _ _ (signingKey_buffers layout scale scaleBuffers) (config_buffers layout)
  exact bounded.trans (by omega)

theorem badLocal_buffers : (badLocal layout scale scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 1 :=
  max_le (badPrefix_buffers layout scale scaleBuffers reserve)
    ((BLSInitialization.implementation_buffers layout.scheme.bad layout.key layout.badFits).trans (by omega))

omit [SMul F K] in
theorem bad_reserved (remaining : Nat) (cacheRoom : remaining ≤ layout.scheme.cache.capacityPred + 1)
    (logRoom : remaining ≤ layout.scheme.capacityPred + 1) (value : layout.sampled.Value) :
    BLSReply.Reserved layout.scheme.bad remaining ((value.val.1, value.val.2.1), [], [], []) :=
  BLSInitialization.reserved layout.scheme.bad remaining cacheRoom logRoom
    ⟨(value.val.1, value.val.2.1), value.property.1, value.property.2.1⟩

end Signatures.Runtime.CaliperBackend.BLSSetup
