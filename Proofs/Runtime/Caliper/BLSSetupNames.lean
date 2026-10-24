import Proofs.Runtime.Caliper.BLSSetupBounds

/-! Derived setup name bounds. Primitive name reservations are explicit; all
new names introduced by copying and pairing are accounted by generated code. -/

namespace Signatures.Runtime.CaliperBackend.BLSSetup
open Caliper BoundedSource

variable {w : Nat} {M F G K : Type} (layout : Layouts w M F G K) (names : Nat)

theorem points_names : NamesAccounted (points layout).program.code names := Implementation.first_names _ _ _ _ _
theorem keys_names : NamesAccounted (keys layout).program.code names := Implementation.second_names _ _ _ _ _
theorem publicKey_names : NamesAccounted (publicKey layout).program.code names :=
  (keys_names layout names).seq (Implementation.second_names _ _ _ _ _)
theorem generator_names : NamesAccounted (generator layout).program.code names :=
  (keys_names layout names).seq (Implementation.first_names _ _ _ _ _)
theorem scalar_names : NamesAccounted (scalar layout).program.code names := Implementation.first_names _ _ _ _ _
theorem challenge_names : NamesAccounted (challenge layout).program.code names := Implementation.second_names _ _ _ _ _
theorem sampledPoints_names : NamesAccounted (sampledPoints layout).program.code names :=
  (challenge_names layout names).seq (points_names layout names)
theorem sampledGenerator_names : NamesAccounted (sampledGenerator layout).program.code names :=
  (challenge_names layout names).seq (generator_names layout names)

theorem goodPrefix_names : NamesAccounted (goodPrefix layout).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (publicKey_names layout names) (points_names layout names)
theorem config_names : NamesAccounted (config layout).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (scalar_names layout names) (sampledPoints_names layout names)
theorem arguments_names : NamesAccounted (arguments layout).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (scalar_names layout names) (sampledGenerator_names layout names)

theorem good_names : NamesAccounted (good layout).program.code (max 3 names) :=
  ((goodPrefix_names layout names).mono (Nat.le_max_right _ _)).seq
    ((BLSInitialization.implementation_names layout.scheme.good layout.key layout.goodFits).accounted.mono (Nat.le_max_left _ _))

variable [SMul F K]
    (scale : Implementation .unit layout.scaleArgs layout.key (fun value => value.1 • value.2))
    (scaleNames : NamesAccounted scale.program.code names)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)

include scaleNames in
theorem signingKey_names : NamesAccounted (signingKey layout scale).program.code names :=
  (arguments_names layout names).seq scaleNames

include scaleNames in
theorem badPrefix_names : NamesAccounted (badPrefix layout scale scaleBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (signingKey_names layout names scale scaleNames) (config_names layout names)

include scaleNames in
theorem badLocal_names : NamesAccounted (badLocal layout scale scaleBuffers reserve).program.code (max 3 names) :=
  ((badPrefix_names layout names scale scaleNames scaleBuffers reserve).mono (Nat.le_max_right _ _)).seq
    ((BLSInitialization.implementation_names layout.scheme.bad layout.key layout.badFits).accounted.mono (Nat.le_max_left _ _))

end Signatures.Runtime.CaliperBackend.BLSSetup
