import Proofs.Runtime.Caliper.WeightedGood
import Proofs.Runtime.Caliper.WeightedBad
import Proofs.Runtime.Caliper.BLSPrivateAccumulateLayout
import Proofs.Runtime.Caliper.BLSResponseLayout

/-! One set of encodings for the two weighted reductions. Only the private cache
payload and configuration differ. Caller packets, scalar outputs, public keys,
DLog challenges and sampling ports agree definitionally. -/
namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource

structure SharedRows (w : Nat) (K M G F : Type) where
  accumulation : BLSPrivateAccumulate.Layouts w K F
  message : Layout w M
  point : Layout w G
  goodWeightedFits : 16 * (message.representation.encoding.words + accumulation.good.width) < 2 ^ w
  badWeightedFits : 16 * (message.representation.encoding.words + accumulation.bad.width) < 2 ^ w
  goodRowsFits : 16 * (message.representation.encoding.words + accumulation.good.width + point.representation.encoding.words) < 2 ^ w
  badRowsFits : 16 * (message.representation.encoding.words + accumulation.bad.width + point.representation.encoding.words) < 2 ^ w
  responseFits : 16 * (accumulation.cache.value.representation.encoding.words + point.representation.encoding.words) < 2 ^ w

namespace SharedRows
variable {w : Nat} {K M G F : Type} (rows : SharedRows w K M G F)
def good : WeightedToken.Layouts w K M G F F :=
  ⟨⟨rows.accumulation.good, rows.message, rows.goodWeightedFits⟩, rows.point, rows.goodRowsFits⟩
def bad : WeightedToken.Layouts w K M G F (F × F) :=
  ⟨⟨rows.accumulation.bad, rows.message, rows.badWeightedFits⟩, rows.point, rows.badRowsFits⟩
def response : BLSResponse.Layouts w F G :=
  ⟨rows.accumulation.cache.value, rows.point, rows.accumulation.cache.wordFits, rows.responseFits⟩
end SharedRows

structure ExtractionBounds {w : Nat} {K M G F R : Type}
    (rows : WeightedToken.Layouts w K M G F R) (signs xi terms hashes gamma : Nat) where
  termCount : terms < 2 ^ w
  termStorage : 1 + terms * (WeightedRows.term rows.accumulation).representation.encoding.words + rows.state.representation.encoding.words < 2 ^ w
  signCount : signs + 2 ≤ 2 ^ w
  xiCount : xi < 2 ^ w
  signingStorage : 16 * (4 + (signs + 1) * (rows.token.representation.encoding.words + rows.accumulation.coefficient.representation.encoding.words) +
    (xi + 1) * rows.accumulation.coefficient.representation.encoding.words + rows.state.representation.encoding.words) < 2 ^ w
  hashCount : hashes + 2 ≤ 2 ^ w
  gammaCount : gamma < 2 ^ w
  extractionStorage : 16 * (
    (WeightedExtraction.Layouts.mk rows signs xi terms termCount termStorage signCount xiCount signingStorage).width +
    WeightedExtractor.hashWidth (WeightedExtraction.Layouts.mk rows signs xi terms termCount termStorage signCount xiCount signingStorage) hashes gamma) < 2 ^ w

namespace ExtractionBounds
variable {w : Nat} {K M G F R : Type} {rows : WeightedToken.Layouts w K M G F R}
    {signs xi terms hashes gamma : Nat} (bounds : ExtractionBounds rows signs xi terms hashes gamma)
def extraction : WeightedExtractor.Layouts w K M G F R :=
  ⟨⟨rows, signs, xi, terms, bounds.termCount, bounds.termStorage, bounds.signCount, bounds.xiCount, bounds.signingStorage⟩,
    hashes, gamma, bounds.hashCount, bounds.gammaCount, bounds.extractionStorage⟩
end ExtractionBounds

structure SharedScheme (w : Nat) (K M G F : Type) [Zero F] where
  rows : SharedRows w K M G F
  signs : Nat
  xi : Nat
  terms : Nat
  hashes : Nat
  gamma : Nat
  goodBounds : ExtractionBounds rows.good signs xi terms hashes gamma
  badBounds : ExtractionBounds rows.bad signs xi terms hashes gamma
  zeroValid : rows.accumulation.cache.value.valid 0
  hashPositive : 0 < hashes
  signPositive : 0 < signs
  goodServiceFits : 32 * WeightedCallerFinish.serviceWidth goodBounds.extraction rows.response.points < 2 ^ w
  badServiceFits : 32 * WeightedCallerFinish.serviceWidth badBounds.extraction rows.response.config < 2 ^ w

namespace SharedScheme
variable {w : Nat} {K M G F : Type} [Zero F] (scheme : SharedScheme w K M G F)
def zero : scheme.rows.accumulation.cache.value.Value := ⟨0, scheme.zeroValid⟩
def pairZero : scheme.rows.accumulation.bad.cache.value.Value := ⟨(0, 0), scheme.zeroValid, scheme.zeroValid⟩
abbrev goodService := WeightedCallerFinish.service scheme.goodBounds.extraction scheme.rows.response.points
  scheme.zero scheme.zero scheme.hashPositive scheme.signPositive scheme.goodServiceFits
abbrev badService := WeightedCallerFinish.service scheme.badBounds.extraction scheme.rows.response.config
  scheme.pairZero scheme.pairZero scheme.hashPositive scheme.signPositive scheme.badServiceFits
end SharedScheme

structure SharedLayouts (w : Nat) (K M G F PK A : Type) [Zero F] where
  scheme : SharedScheme w K M G F
  key : Layout w PK
  state : Representation w A
  randomBound : Nat
  randomFits : randomBound + 1 ≤ 2 ^ w
  goodCallerFits : 8 * (1 + state.encoding.words +
    (WeightedCallerPackets.request scheme.goodService randomBound randomFits).encoding.words +
    (WeightedCallerPackets.reply scheme.goodService randomBound randomFits).encoding.words +
    scheme.goodBounds.extraction.forgery.representation.encoding.words + scheme.goodService.store.representation.encoding.words) < 2 ^ w
  badCallerFits : 8 * (1 + state.encoding.words +
    (WeightedCallerPackets.request scheme.badService randomBound randomFits).encoding.words +
    (WeightedCallerPackets.reply scheme.badService randomBound randomFits).encoding.words +
    scheme.badBounds.extraction.forgery.representation.encoding.words + scheme.badService.store.representation.encoding.words) < 2 ^ w
  goodSetupFits : 16 * (scheme.goodService.store.representation.encoding.words +
    scheme.rows.response.points.representation.encoding.words + 2 * key.representation.encoding.words) < 2 ^ w
  badSetupFits : 16 * (scheme.badService.store.representation.encoding.words +
    scheme.rows.response.config.representation.encoding.words + 2 * key.representation.encoding.words) < 2 ^ w
  samplingFits : 16 * (scheme.rows.accumulation.cache.value.representation.encoding.words +
    scheme.rows.response.points.representation.encoding.words + 2 * key.representation.encoding.words) < 2 ^ w

namespace SharedLayouts
variable {w : Nat} {K M G F PK A : Type} [Zero F] (layout : SharedLayouts w K M G F PK A)
def good : WeightedCallerExtraction.Layouts w K M G F F (G × G) A where
  extraction := layout.scheme.goodBounds.extraction
  config := layout.scheme.rows.response.points
  zero := layout.scheme.zero
  default := layout.scheme.zero
  hashPositive := layout.scheme.hashPositive
  signPositive := layout.scheme.signPositive
  serviceFits := layout.scheme.goodServiceFits
  randomBound := layout.randomBound
  randomFits := layout.randomFits
  state := layout.state
  callerFits := layout.goodCallerFits
def bad : WeightedCallerExtraction.Layouts w K M G F (F × F) (F × (G × G)) A where
  extraction := layout.scheme.badBounds.extraction
  config := layout.scheme.rows.response.config
  zero := layout.scheme.pairZero
  default := layout.scheme.pairZero
  hashPositive := layout.scheme.hashPositive
  signPositive := layout.scheme.signPositive
  serviceFits := layout.scheme.badServiceFits
  randomBound := layout.randomBound
  randomFits := layout.randomFits
  state := layout.state
  callerFits := layout.badCallerFits
def goodSetup : WeightedSetup.Layouts layout.good.service PK := ⟨layout.key, layout.goodSetupFits⟩
def badSetup : WeightedSetup.Layouts layout.bad.service PK := ⟨layout.key, layout.badSetupFits⟩
def preparation : WeightedBadSetup.Layouts w F G PK :=
  ⟨layout.scheme.rows.accumulation.cache.value, layout.scheme.rows.response.points,
    layout.key, layout.scheme.rows.accumulation.cache.wordFits, layout.samplingFits⟩
abbrev port := layout.good.port

theorem same_challenge : layout.preparation.challenge = layout.goodSetup.challenge := rfl
theorem prepared_challenge : layout.preparation.output = layout.badSetup.challenge := rfl
theorem same_output : layout.bad.extraction.scalar = layout.good.extraction.scalar := rfl
theorem same_forgery : layout.bad.forgery = layout.good.forgery := rfl
theorem same_port : layout.bad.port = layout.port := rfl
end SharedLayouts
end Signatures.Runtime.CaliperBackend.WeightedFull
