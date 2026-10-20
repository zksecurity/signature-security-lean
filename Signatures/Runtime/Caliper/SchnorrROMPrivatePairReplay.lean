import Signatures.Runtime.Caliper.SchnorrROMPrivatePair
import Signatures.Runtime.SchnorrROMSharedState

/-! The generated pair sampler refines the two ordered private draws used by
the shared-tape signing oracle. Equality preserves the original sampler's
internal uniform-query tree, including replay-family chronology. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Pair
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F C : Type} [Field F] [SampleableType F] (layout : Layouts w F C)
    (caller : Caller layout) (zeroValid : layout.tape.scalar.valid 0)
    (fuel : Nat) (terminates : Terminates layout caller fuel)
    (samples : Subtype.val <$> original layout caller fuel terminates (Service.unit layout) = ($ᵗ F : ProbComp F))

include terminates samples

theorem scalar_source (saved : Store layout) (valid : ready layout fuel saved) :
    Subtype.val <$> source layout caller zeroValid fuel saved = (do
      let first ← Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (F := F) (.inr ())) saved.val
      (fun second => (first.1, second)) <$>
        Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (F := F) (.inr ())) first.2) := by
  have scalar (state : Store layout) (admitted : Service.ready layout fuel state) :
      Subtype.val <$> Service.source layout caller zeroValid fuel state =
        Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (.inr ())) state.val :=
    Service.scalar_source layout caller zeroValid fuel terminates samples state admitted
  rw [source, map_bind]
  calc
    _ = (do
        let first ← Service.source layout caller zeroValid fuel saved
        (fun second => (first.val.1, second)) <$>
          Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (.inr ())) first.val.2) := by
      apply bind_congr_of_forall_mem_support
      intro first supported
      simpa only [Functor.map_map, pack, unpack] using
        congrArg (Functor.map (fun second => (first.val.1, second)))
          (scalar (unpack layout first).2 (second_ready layout caller zeroValid fuel saved valid first supported))
    _ = _ := by
      have same := congrArg (fun draw : ProbComp (F × Schnorr.ListROM.Shared.Tape F) =>
        draw >>= fun first => (fun second : F × Schnorr.ListROM.Shared.Tape F => (first.1, second)) <$>
          Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (F := F) (.inr ())) first.2)
          (scalar saved (first_ready layout fuel saved valid))
      simp only [bind_map_left] at same
      convert same using 1

theorem observe_scalar (tape : RandomTape w) (saved : Store layout) (valid : ready layout fuel saved)
    (before : State w) (holds : (Read.tapes layout.tape).representation.Holds saved before) :
    (fun result => (Interactive.observe (output layout).representation result).map Subtype.val) <$>
      (code layout caller zeroValid fuel).execute (Fresh.port layout.tape) .unit tape before =
        some <$> (do
          let first ← Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (.inr ())) saved.val
          (fun second => (first.1, second)) <$>
            Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (.inr ())) first.2) := by
  have observed := (refines layout caller zeroValid fuel).observe tape saved valid before holds
  have mapped := congrArg (Functor.map (Option.map Subtype.val)) observed
  simp only [Functor.map_map, Option.map_some] at mapped
  have same := scalar_source layout caller zeroValid fuel terminates samples saved valid
  simpa only [Functor.map_map, Option.map_some] using mapped.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Pair
