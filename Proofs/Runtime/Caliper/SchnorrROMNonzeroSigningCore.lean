import Proofs.Runtime.Caliper.SchnorrROMNonzeroSigningRoutes
import Proofs.Runtime.Caliper.SchnorrROMHandler
import Proofs.Runtime.Caliper.EncodedEquality

/-! The deterministic nonzero signing suffix after the three private draws.
On `(a, ((c, z), g, pk, msg, managed))` it computes `R = z • g - c • pk`,
tests `R` against the executed zero point `g - g` with `EncodedEquality`,
and in the guarded branch either keeps `(R, z)` or repairs to `(a • g, z + a)`.
The reply and frame are then routed into the managed-cache programmer.
Projections, the shared-input pairs, the test, the dispatch and all retained
copies are executed and charged. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

/-! ### Source functions -/

section Values
variable [Zero F] [SMul F G] [Sub G] [Add F]

/-- Prepend the commitment `R = z • g - c • pk`. -/
def commitValue (u : F × Signing.Input M F G) : G × F × Signing.Input M F G :=
  (Signing.Arithmetic.commitment u.2, u)

variable [DecidableEq G] in
/-- Whether the commitment equals the (executed) zero point `g - g`. -/
def zeroTest (v : G × F × Signing.Input M F G) : Bool := decide (v.1 = v.2.2.2.1 - v.2.2.2.1)

variable [DecidableEq G] in
/-- The returned signature: the repair `(a • g, z + a)` exactly when `R` is zero. -/
def repaired (v : G × F × Signing.Input M F G) : G × F :=
  if zeroTest v = true then (v.2.1 • v.2.2.2.1, v.2.2.1.2 + v.2.1) else (v.1, v.2.2.1.2)

variable [DecidableEq M] [DecidableEq G] in
/-- The complete deterministic suffix. -/
def value (u : F × Signing.Input M F G) : Signing.Output M F G :=
  Signing.Cache.value (assemble (repaired (commitValue u), commitValue u))

end Values

/-! ### Executed implementation -/

section Fits
theorem identity_buffers {A : Type} (layout : Layout w A) :
    (Implementation.identity (cost := .unit) layout (width_pos config.sampler.wordFits)).program.code.memBound = 0 := rfl

theorem nzInput_fits : sw config + config.handler.core.input.representation.encoding.words < 2 ^ w :=
  fits config (by rw [input_words]; omega)
theorem frame_fits : pw config + (nzInput config).representation.encoding.words < 2 ^ w :=
  fits config (by rw [nzInput_words]; omega)
theorem framed_fits : (pw config + sw config) + (frame config).representation.encoding.words < 2 ^ w :=
  fits config (by rw [frame_words]; omega)
theorem nzInput_duplicate : (nzInput config).representation.encoding.words + (nzInput config).representation.encoding.words < 2 ^ w :=
  fits config (by rw [nzInput_words]; omega)
theorem nzInput_middle : pw config + (nzInput config).representation.encoding.words < 2 ^ w := frame_fits config
theorem frame_duplicate : (frame config).representation.encoding.words + (frame config).representation.encoding.words < 2 ^ w :=
  fits config (by rw [frame_words]; omega)
theorem frame_middle_point : pw config + (frame config).representation.encoding.words < 2 ^ w :=
  fits config (by rw [frame_words]; omega)
theorem frame_middle_reply : (pw config + sw config) + (frame config).representation.encoding.words < 2 ^ w := framed_fits config
theorem sw_eq : sw config = 1 := rfl
theorem frame_tag : 1 + (frame config).representation.encoding.words < 2 ^ w :=
  fits config (by rw [frame_words, sw_eq]; omega)
theorem points_fits : pw config + pw config < 2 ^ w := fits config (by omega)
theorem reply_fits : pw config + sw config < 2 ^ w := fits config (by omega)

theorem projGG_buffers : (projGG config).program.code.memBound ≤ 2 := route_buffers config _ _ _ _ _ _ _ _
theorem projAG_buffers : (projAG config).program.code.memBound ≤ 2 := route_buffers config _ _ _ _ _ _ _ _
theorem projZA_buffers : (projZA config).program.code.memBound ≤ 2 := route_buffers config _ _ _ _ _ _ _ _
theorem projRZ_buffers : (projRZ config).program.code.memBound ≤ 2 := route_buffers config _ _ _ _ _ _ _ _
theorem routeWork_buffers [DecidableEq M] [DecidableEq G] : (routeWork config).program.code.memBound ≤ 2 :=
  route_buffers config _ _ _ _ _ _ _ _
end Fits

section Code
variable [SMul F G] [Sub G] [Add F] (ops : Handler.Operations config) (arith : Arithmetic config)

/-- The shared buffer-name bound of the local primitives. -/
def slots : Nat := max ops.slots arith.slots

theorem slots_reserve : slots config ops arith + 3 < 2 ^ w := by
  have := ops.reserve; have := arith.reserve
  unfold slots; omega

theorem nameFits {A B : Type} {i : Layout w A} {o : Layout w B} {f : A → B}
    (body : Implementation .unit i o f) (bound : body.program.code.memBound ≤ max 6 (slots config ops arith + 3)) :
    body.program.savedBuffer < 2 ^ w := by
  have := slots_reserve config ops arith
  have := config.sampler.wordFits
  change max 2 body.program.code.memBound < _
  omega

section Commit
variable [Zero F]

/-- `(a, input) ↦ input`. -/
def signingInput : Implementation .unit (nzInput config) config.handler.core.input Prod.snd :=
  Implementation.second (by decide) config.handler.core.scalar config.handler.core.input config.sampler.wordFits
    (nzInput_fits config)

/-- `R = z • g - c • pk`, computed by the full-field signing arithmetic. -/
def commitment : Implementation .unit (nzInput config) config.handler.core.point
    (fun u => Signing.Arithmetic.commitment u.2) :=
  (signingInput config).then (Signing.Arithmetic.point config.handler.core trivial ops.scale ops.sub
    ops.scaleNames.buffers ops.reserve)

theorem commitment_buffers : (commitment config ops).program.code.memBound ≤ max 3 (slots config ops arith) + 1 := by
  have := Signing.Arithmetic.point_buffers config.handler.core trivial ops.scale ops.sub
    ops.scaleNames.buffers ops.subNames.buffers ops.reserve
  have : (signingInput config).program.code.memBound ≤ 2 :=
    Implementation.second_buffers (cost := .unit) (by decide) config.handler.core.scalar config.handler.core.input
      config.sampler.wordFits (nzInput_fits config)
  change max _ _ ≤ _
  unfold slots; omega

/-- Executed `(R, u)`: the commitment paired with a charged copy of the input. -/
def commit : Implementation .unit (nzInput config) (frame config) commitValue :=
  (commitment config ops).pair (Implementation.identity (nzInput config) (width_pos config.sampler.wordFits)) (by decide)
    config.sampler.wordFits (nameFits config ops arith _ ((commitment_buffers config ops arith).trans (by omega)))
    (nameFits config ops arith _ ((le_of_eq (identity_buffers config _)).trans (Nat.zero_le _)))
    (nzInput_duplicate config) (nzInput_middle config) (frame_fits config)

theorem commit_buffers : (commit config ops arith).program.code.memBound ≤ max 3 (slots config ops arith) + 2 :=
  (Implementation.pair_buffers _ _ _ _ _ _ _ _ (commitment_buffers config ops arith) (le_of_eq (identity_buffers config _))).trans
    (by omega)

end Commit

section Test
variable [DecidableEq G]

/-- Executed `(R, g - g)`. -/
def testArgs : Implementation .unit (frame config) config.handler.core.arithmetic.points
    (fun v => (v.1, v.2.2.2.1 - v.2.2.2.1)) :=
  (Implementation.first (by decide) config.handler.core.point (nzInput config) config.sampler.wordFits (frame_fits config)).pair
    ((projGG config).then ops.sub) (by decide) config.sampler.wordFits
    (nameFits config ops arith _ (by
      have := Implementation.first_buffers (cost := .unit) (by decide) config.handler.core.point (nzInput config)
        config.sampler.wordFits (frame_fits config)
      omega))
    (nameFits config ops arith _ (by
      have := projGG_buffers config
      have := ops.subNames.buffers
      change max _ _ ≤ _
      unfold slots; omega))
    (frame_duplicate config) (frame_middle_point config) (points_fits config)

omit [DecidableEq G] in
theorem testArgs_buffers : (testArgs config ops arith).program.code.memBound ≤ max 2 (slots config ops arith) + 1 := by
  have hf := Implementation.first_buffers (cost := .unit) (by decide) config.handler.core.point (nzInput config)
    config.sampler.wordFits (frame_fits config)
  have projected := projGG_buffers config
  have subtracted := ops.subNames.buffers
  have second : ((projGG config).then ops.sub).program.code.memBound ≤ max 2 (slots config ops arith) := by
    change max _ _ ≤ _; unfold slots; omega
  exact (Implementation.pair_buffers _ _ _ _ _ _ _ _ hf second).trans (by omega)

/-- Executed zero test of the commitment. -/
def test : Implementation .unit (frame config) (DataImplementation.boolLayout w (width_pos config.sampler.wordFits)) zeroTest :=
  ((testArgs config ops arith).then (EncodedEquality.implementation .unit config.handler.core.point config.sampler.wordFits
    (points_fits config))).castFunction rfl

theorem test_buffers : (test config ops arith).program.code.memBound ≤ max 5 (slots config ops arith + 1) := by
  have := testArgs_buffers config ops arith
  have := (EncodedEquality.implementation_names .unit config.handler.core.point config.sampler.wordFits (points_fits config)).buffers
  change max _ _ ≤ _
  omega

end Test

/-- Executed repair `(a • g, z + a)`. -/
def repair : Implementation .unit (frame config) config.handler.core.reply
    (fun v => (v.2.1 • v.2.2.2.1, v.2.2.1.2 + v.2.1)) :=
  ((projAG config).then ops.scale).pair ((projZA config).then arith.add) (by decide) config.sampler.wordFits
    (nameFits config ops arith _ (by
      have := projAG_buffers config
      have := ops.scaleNames.buffers
      change max _ _ ≤ _
      unfold slots; omega))
    (nameFits config ops arith _ (by
      have := projZA_buffers config
      have := arith.addNames.buffers
      change max _ _ ≤ _
      unfold slots; omega))
    (frame_duplicate config) (frame_middle_point config) (reply_fits config)

theorem repair_buffers : (repair config ops arith).program.code.memBound ≤ max 2 (slots config ops arith) + 1 := by
  have := projAG_buffers config
  have := projZA_buffers config
  have := ops.scaleNames.buffers
  have := arith.addNames.buffers
  have hl : ((projAG config).then ops.scale).program.code.memBound ≤ max 2 (slots config ops arith) := by
    change max _ _ ≤ _; unfold slots; omega
  have hr : ((projZA config).then arith.add).program.code.memBound ≤ max 2 (slots config ops arith) := by
    change max _ _ ≤ _; unfold slots; omega
  exact (Implementation.pair_buffers _ _ _ _ _ _ _ _ hl hr).trans (by omega)

section Guarded
variable [DecidableEq G]

/-- The guarded branch on the executed zero test. -/
def guarded : Implementation .unit (frame config) config.handler.core.reply repaired :=
  (GuardedBranch.implementation (hw := config.sampler.wordFits) (test config ops arith) (by decide)
    (nameFits config ops arith _ ((test_buffers config ops arith).trans (by omega)))
    (frame_duplicate config) (frame_tag config)
    ((repair config ops arith).restrictInput (fun v => zeroTest v = true))
    ((projRZ config).restrictInput (fun v => zeroTest v = false))).castFunction rfl

theorem guarded_buffers : (guarded config ops arith).program.code.memBound ≤ max 6 (slots config ops arith + 2) := by
  have := GuardedBranch.implementation_buffers (hw := config.sampler.wordFits) (test config ops arith)
    (nameFits config ops arith _ ((test_buffers config ops arith).trans (by omega)))
    (frame_duplicate config) (frame_tag config)
    ((repair config ops arith).restrictInput (fun v => zeroTest v = true))
    ((projRZ config).restrictInput (fun v => zeroTest v = false))
    (test_buffers config ops arith) (repair_buffers config ops arith)
    (projRZ_buffers config)
  change _ ≤ _ at this
  exact this.trans (by omega)

/-- Executed `(reply, frame)`: the guarded reply with a retained frame copy. -/
def framedReply : Implementation .unit (frame config) (framed config) (fun v => (repaired v, v)) :=
  (guarded config ops arith).pair (Implementation.identity (frame config) (width_pos config.sampler.wordFits)) (by decide)
    config.sampler.wordFits (nameFits config ops arith _ ((guarded_buffers config ops arith).trans (by omega)))
    (nameFits config ops arith _ ((le_of_eq (identity_buffers config _)).trans (Nat.zero_le _)))
    (frame_duplicate config) (frame_middle_reply config) (framed_fits config)

theorem framedReply_buffers : (framedReply config ops arith).program.code.memBound ≤ max 7 (slots config ops arith + 3) :=
  (Implementation.pair_buffers _ _ _ _ _ _ _ _ (guarded_buffers config ops arith) (le_of_eq (identity_buffers config _))).trans
    (by omega)

variable [Zero F] [DecidableEq M]

/-- The complete executed deterministic suffix. -/
def implementation : Implementation .unit (nzInput config) config.handler.core.output value :=
  ((((commit config ops arith).then (framedReply config ops arith)).then (routeWork config)).then
    (Signing.Cache.implementation config.handler.core)).castFunction rfl

theorem buffers : (implementation config ops arith).program.code.memBound ≤ max 9 (slots config ops arith + 3) := by
  have := commit_buffers config ops arith
  have := framedReply_buffers config ops arith
  have := routeWork_buffers config
  have := Signing.Cache.buffers config.handler.core
  change max (max (max _ _) _) _ ≤ _
  omega

end Guarded
end Code
end Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
