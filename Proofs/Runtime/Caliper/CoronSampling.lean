import Proofs.Runtime.Caliper.UniformSamplingBounds
import Proofs.Runtime.Caliper.PairSamplingBounds

/-! Fresh scalar/coin entries for the Coron co-CDH reduction. Only the scalar
sampler is a primitive input. The coin draw, independent composition, retained
scalar, output permutation and their complete resource bounds are constructed.
Persistent per-message caching is a separate part of the reduction. -/
namespace Signatures.Runtime.CaliperBackend.CoronSampling
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {F : Type} (scalar : Layout w F)
    (bound : Nat) (hw : 16 < 2 ^ w) (fits : bound + 1 ≤ 2 ^ w)
    (qS : Fin (bound + 1)) (storage : scalar.representation.encoding.words + 1 < 2 ^ w)

def output : Layout w (F × Fin (qS.val + 1)) :=
  scalar.prod (UniformSampling.output bound hw fits qS) storage

def code (draw : Interactive.Code w) : Interactive.Code w :=
  PairSampling.code scalar (UniformSampling.output bound hw fits qS) hw storage
    (UniformQuery.port bound hw fits) draw (UniformSampling.code bound hw fits qS)

def source (drawSource : ProbComp scalar.Value) : ProbComp (output scalar bound hw fits qS storage).Value :=
  PairSampling.denote scalar (UniformSampling.output bound hw fits qS) storage
    drawSource (UniformSampling.source bound hw fits qS)

def timeBudget (scalarTime : Nat) : Nat := scalarTime + 20 * scalar.representation.encoding.words + 42
def codeBudget (scalarWords : Nat) : Nat := scalarWords + 65 * scalar.representation.encoding.words + 235
def memoryBudget (scalarTime scalarWords scalarSlots : Nat) : Nat :=
  codeBudget scalar scalarWords + 4 * max 4 scalarSlots + 3 + timeBudget scalar scalarTime

variable {draw : Interactive.Code w} {drawSource : ProbComp scalar.Value}
    (drawCorrect : Interactive.Refines (UniformQuery.port bound hw fits) .unit
      (UniformSampling.input (w := w)).representation scalar.representation (fun _ => drawSource) draw)

include drawCorrect in
theorem refines : Interactive.Refines (UniformQuery.port bound hw fits) .unit
    (UniformSampling.input (w := w)).representation (output scalar bound hw fits qS storage).representation
    (fun _ => source scalar bound hw fits qS storage drawSource) (code scalar bound hw fits qS storage draw) :=
  PairSampling.refines (hw := hw) (fits := storage) drawCorrect (UniformSampling.refines bound hw fits qS)

theorem uniform [SampleableType F]
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ F : ProbComp F)) :
    Subtype.val <$> source scalar bound hw fits qS storage drawSource = ($ᵗ (F × Fin (qS.val + 1)) : ProbComp _) :=
  PairSampling.uniform scalar (UniformSampling.output bound hw fits qS) storage drawSource
    (UniformSampling.source bound hw fits qS) drawLaw (UniformSampling.uniform bound hw fits qS)

include drawCorrect in
theorem time_bound {scalarTime : Nat}
    (drawTime : Interactive.TimeBound (UniformQuery.port bound hw fits) .unit
      (UniformSampling.input (w := w)).representation draw scalarTime) :
    Interactive.TimeBound (UniformQuery.port bound hw fits) .unit
      (UniformSampling.input (w := w)).representation (code scalar bound hw fits qS storage draw) (timeBudget scalar scalarTime) := by
  have bounded := PairSampling.time_bound (hw := hw) (fits := storage) drawCorrect
    (UniformSampling.refines bound hw fits qS) drawTime (UniformSampling.time_bound bound hw fits qS)
  exact bounded.mono (by change scalarTime + 26 + 20 * _ + 16 * 1 ≤ scalarTime + 20 * _ + 42; omega)

theorem code_words {scalarWords : Nat}
    (drawWords : (draw.lower (UniformQuery.port bound hw fits)).descriptionWords ≤ scalarWords) :
    ((code scalar bound hw fits qS storage draw).lower (UniformQuery.port bound hw fits)).descriptionWords ≤ codeBudget scalar scalarWords := by
  have bounded := PairSampling.code_bound scalar (UniformSampling.output bound hw fits qS) hw storage
    (UniformQuery.port bound hw fits) draw (UniformSampling.code bound hw fits qS) drawWords
    (UniformSampling.code_words bound hw fits qS)
  exact bounded.trans (by change scalarWords + 125 + 65 * _ + 52 * 1 + 58 ≤ scalarWords + 65 * _ + 235; omega)

theorem names {scalarSlots : Nat}
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port bound hw fits)) scalarSlots) :
    WordIO.NamesBound ((code scalar bound hw fits qS storage draw).lower (UniformQuery.port bound hw fits)) (max 4 scalarSlots) := by
  have named := PairSampling.names scalar (UniformSampling.output bound hw fits qS) hw storage
    (UniformQuery.port bound hw fits) draw (UniformSampling.code bound hw fits qS) drawNames
    (UniformSampling.names bound hw fits qS)
  have larger : PairSampling.slots scalarSlots 3 ≤ max 4 scalarSlots := by unfold PairSampling.slots; omega
  exact ⟨named.registers.trans larger, named.buffers.trans larger⟩

theorem descriptionFits (drawFits : (draw.lower (UniformQuery.port bound hw fits)).DescriptionFits) :
    ((code scalar bound hw fits qS storage draw).lower (UniformQuery.port bound hw fits)).DescriptionFits :=
  PairSampling.descriptionFits scalar (UniformSampling.output bound hw fits qS) hw storage
    (UniformQuery.port bound hw fits) draw (UniformSampling.code bound hw fits qS) drawFits
    (UniformSampling.descriptionFits bound hw fits qS) (UniformSampling.names bound hw fits qS) (by omega)

include drawCorrect in
theorem within [SampleableType F] (drawLaw : Subtype.val <$> drawSource = ($ᵗ F : ProbComp F))
    {scalarTime scalarWords scalarSlots : Nat}
    (drawTime : Interactive.TimeBound (UniformQuery.port bound hw fits) .unit
      (UniformSampling.input (w := w)).representation draw scalarTime)
    (drawWords : (draw.lower (UniformQuery.port bound hw fits)).descriptionWords ≤ scalarWords)
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port bound hw fits)) scalarSlots)
    (drawFits : (draw.lower (UniformQuery.port bound hw fits)).DescriptionFits) :
    Interactive.Within (UniformQuery.port bound hw fits) (UniformSampling.input (w := w))
      (output scalar bound hw fits qS storage) (codeBudget scalar scalarWords)
      (memoryBudget scalar scalarTime scalarWords scalarSlots) (timeBudget scalar scalarTime)
      (fun _ => ($ᵗ (F × Fin (qS.val + 1)) : ProbComp _)) := by
  have bounded := Interactive.within_of_refines (refines scalar bound hw fits qS storage drawCorrect)
    (time_bound scalar bound hw fits qS storage drawCorrect drawTime)
    (code_words scalar bound hw fits qS storage drawWords) (names scalar bound hw fits qS storage drawNames)
    (descriptionFits scalar bound hw fits qS storage drawFits)
  exact bounded.congr (fun _ => uniform scalar bound hw fits qS storage drawLaw)

end Signatures.Runtime.CaliperBackend.CoronSampling
