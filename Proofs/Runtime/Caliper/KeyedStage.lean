import Proofs.Runtime.Caliper.KeyedSetupBounds
import Proofs.Runtime.Caliper.WeightedBadSetupBounds
import Proofs.Runtime.Caliper.Preparation

/-! The known-key draw and the bad branch's outer resampling as preparation stages. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec

namespace KeyedSetup
variable {w : Nat} {F C K : Type} (layout : Layouts w F C K) [SMul F K]
    (scale : Implementation .unit layout.arguments layout.key (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 5 < 2 ^ w)
    {scaleTime scaleWords : Nat} (scaleBound : scale.BoundedBy scaleTime scaleWords)
    {scaleSlots : Nat} (scaleNames : NamesAccounted scale.program.code scaleSlots)
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w) (source : ProbComp layout.scalar.Value)
    (drawCorrect : Interactive.Refines port .unit layout.unit.representation layout.scalar.representation (fun _ => source) draw)
    {drawTime drawWords drawSlots : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (drawNames : WordIO.NamesBound (draw.lower port) drawSlots)
    (drawFits : (draw.lower port).DescriptionFits) (drawReserve : drawSlots < 2 ^ w)

include scaleBound scaleNames drawCorrect drawTimeBound drawWordsBound drawNames drawFits drawReserve in
def stage : Preparation.Stage port layout.challenge layout.output where
  code := code layout scale scaleBuffers reserve port draw
  source := denote layout scale scaleBuffers reserve source
  refines := refines layout scale scaleBuffers reserve port draw source drawCorrect
  time := timeBudget layout drawTime scaleTime
  words := codeBudget layout drawWords scaleWords
  slots := max (max 3 drawSlots) scaleSlots
  timeBound := time layout scale scaleBuffers reserve scaleBound port draw source drawCorrect drawTimeBound
  wordsBound := words layout scale scaleBuffers reserve scaleBound port draw drawWordsBound
  names := names layout scale scaleBuffers reserve scaleNames port draw drawNames
  fits := descriptionFits layout scale scaleBuffers reserve port draw drawFits drawNames drawReserve
end KeyedSetup

namespace WeightedBadSetup
variable {w : Nat} {F G PK : Type} (layout : Layouts w F G PK) [SMul F PK]
    (scale : Implementation .unit layout.arguments layout.key (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 5 < 2 ^ w)
    {scaleTime scaleWords : Nat} (scaleBound : scale.BoundedBy scaleTime scaleWords)
    {scaleSlots : Nat} (scaleNames : NamesAccounted scale.program.code scaleSlots)
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w) (source : ProbComp layout.scalar.Value)
    (drawCorrect : Interactive.Refines port .unit layout.unit.representation layout.scalar.representation (fun _ => source) draw)
    {drawTime drawWords drawSlots : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (drawNames : WordIO.NamesBound (draw.lower port) drawSlots)
    (drawFits : (draw.lower port).DescriptionFits) (drawReserve : drawSlots < 2 ^ w)

include scaleBound scaleNames drawCorrect drawTimeBound drawWordsBound drawNames drawFits drawReserve in
def stage : Preparation.Stage port layout.challenge layout.output where
  code := code layout scale scaleBuffers reserve port draw
  source := denote layout scale scaleBuffers reserve source
  refines := refines layout scale scaleBuffers reserve port draw source drawCorrect
  time := timeBudget layout drawTime scaleTime
  words := codeBudget layout drawWords scaleWords
  slots := max (max 3 drawSlots) scaleSlots
  timeBound := time layout scale scaleBuffers reserve scaleBound port draw source drawCorrect drawTimeBound
  wordsBound := words layout scale scaleBuffers reserve scaleBound port draw drawWordsBound
  names := names layout scale scaleBuffers reserve scaleNames port draw drawNames
  fits := descriptionFits layout scale scaleBuffers reserve port draw drawFits drawNames drawReserve
end WeightedBadSetup

end Signatures.Runtime.CaliperBackend
