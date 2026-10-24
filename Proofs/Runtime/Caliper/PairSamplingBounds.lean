import Proofs.Runtime.Caliper.PairSampling
import Proofs.Runtime.Caliper.InteractiveNames
import Proofs.Runtime.Caliper.InteractiveAcceptance

/-! Derived pair-sampler resources. Only the component samplers supply budgets
and accepted descriptions. The saved buffer, copies, permutation and both
stored component bodies are included in the resulting bounds. -/

namespace Signatures.Runtime.CaliperBackend.PairSampling

open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {A B I : Type} {spec : OracleSpec I}
    (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    (port : Interactive.Port w spec)

def timeBudget (firstTime secondTime : Nat) : Nat :=
  firstTime + secondTime + 20 * left.representation.encoding.words + 16 * right.representation.encoding.words

def codeBudget (firstWords secondWords : Nat) : Nat :=
  firstWords + secondWords + 65 * left.representation.encoding.words + 52 * right.representation.encoding.words + 58

def slots (firstSlots secondSlots : Nat) : Nat := max 3 (max firstSlots (secondSlots + 1))

variable {left right hw fits port} {first second : Interactive.Code w}
    {firstSource : OracleComp spec left.Value} {secondSource : OracleComp spec right.Value}

include hw in
theorem retained_time
    (secondCorrect : Interactive.Refines port .unit (input w).representation right.representation
      (fun _ => secondSource) second) {secondTime : Nat}
    (secondBound : Interactive.TimeBound port .unit (input w).representation second secondTime) :
    Interactive.TimeBound port .unit left.representation (retained left right port second)
      (secondTime + 8 * right.representation.encoding.words + 12 * left.representation.encoding.words) := by
  have saved := secondBound.retain secondCorrect (by decide) left.representation hw
    (by change 0 + left.representation.encoding.words < 2 ^ w; simpa using left.representation.fits)
  have viewed := saved.viewInput left.representation (fun x => (⟨(), trivial⟩, x)) (fun _ => rfl)
  exact viewed.mono (Interactive.retain_time_unit_le _ 0 _ _ _)

theorem time_bound
    (firstCorrect : Interactive.Refines port .unit (input w).representation left.representation
      (fun _ => firstSource) first)
    (secondCorrect : Interactive.Refines port .unit (input w).representation right.representation
      (fun _ => secondSource) second) {firstTime secondTime : Nat}
    (firstBound : Interactive.TimeBound port .unit (input w).representation first firstTime)
    (secondBound : Interactive.TimeBound port .unit (input w).representation second secondTime) :
    Interactive.TimeBound port .unit (input w).representation (code left right hw fits port first second)
      (timeBudget left right firstTime secondTime) := by
  have finishBound := Interactive.TimeBound.compute (port := port) (cost := .unit) (finish left right hw fits)
    (8 * (right.representation.encoding.words + left.representation.encoding.words))
    (Pairing.swap_time_unit_le right.representation left.representation hw (by omega))
  have combined := firstBound.seq firstCorrect
    ((retained_time (hw := hw) secondCorrect secondBound).seq
      (retained_refines (hw := hw) (fits := fits) secondCorrect) finishBound)
  exact combined.mono (by unfold timeBudget; omega)

variable (left right hw fits port)

theorem code_bound (first second : Interactive.Code w) {firstWords secondWords : Nat}
    (firstBound : (first.lower port).descriptionWords ≤ firstWords)
    (secondBound : (second.lower port).descriptionWords ≤ secondWords) :
    ((code left right hw fits port first second).lower port).descriptionWords ≤ codeBudget left right firstWords secondWords := by
  have saved := Interactive.retain_descriptionWords_le port second (Interactive.savedBuffer port second) 0
    right.representation.encoding.words left.representation.encoding.words
  have swapped := Pairing.swap_descriptionWords_le .unit (by decide) right.representation left.representation hw (by omega)
  change descriptionWords (finish left right hw fits).code ≤ _ at swapped
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  change ((retained left right port second).lower port).descriptionWords ≤ _ at saved
  unfold codeBudget
  omega

theorem finish_names : registerSlots (finish left right hw fits).code ≤ 3 ∧ (finish left right hw fits).code.memBound ≤ 2 := by
  change registerSlots (Assembly.code (Reorder.operands (w := w) right.representation.encoding.words left.representation.encoding.words 0)) ≤ 3 ∧ _
  apply Assembly.code_names _ 1
  simp only [Reorder.operands, Assembly.sourcesBound_append]
  exact ⟨⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩,
    Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩

theorem names (first second : Interactive.Code w) {firstSlots secondSlots : Nat}
    (firstNames : WordIO.NamesBound (first.lower port) firstSlots)
    (secondNames : WordIO.NamesBound (second.lower port) secondSlots) :
    WordIO.NamesBound ((code left right hw fits port first second).lower port) (slots firstSlots secondSlots) := by
  have prepared := Retain.prepare_names (w := w) (Interactive.savedBuffer port second) 0 left.representation.encoding.words
  have restored := Retain.finish_names (w := w) (Interactive.savedBuffer port second)
    right.representation.encoding.words left.representation.encoding.words
  have savedBuffers := Interactive.retain_buffers port second 0 right.representation.encoding.words left.representation.encoding.words
  have swapped := finish_names left right hw fits
  rcases firstNames with ⟨firstRegisters, firstBuffers⟩
  rcases secondNames with ⟨secondRegisters, secondBuffers⟩
  constructor
  · simp only [code, retained, Interactive.retain, Interactive.Code.lower, WordIO.Code.registerSlots]
    unfold slots
    omega
  · change max (first.lower port).memBound (max ((retained left right port second).lower port).memBound
      (finish left right hw fits).code.memBound) ≤ _
    change ((retained left right port second).lower port).memBound ≤ _ at savedBuffers
    unfold slots
    omega

theorem descriptionFits (first second : Interactive.Code w)
    (firstFits : (first.lower port).DescriptionFits) (secondFits : (second.lower port).DescriptionFits)
    {secondSlots : Nat} (secondNames : WordIO.NamesBound (second.lower port) secondSlots)
    (slotsFit : secondSlots < 2 ^ w) :
    ((code left right hw fits port first second).lower port).DescriptionFits := by
  have nameFits : Interactive.savedBuffer port second < 2 ^ w := by
    have buffers := secondNames.buffers
    dsimp only [Interactive.savedBuffer]
    omega
  have saved := Interactive.retain_descriptionFits port second (Interactive.savedBuffer port second) 0
    right.representation.encoding.words left.representation.encoding.words hw secondFits nameFits
    (by positivity) left.representation.fits (by omega)
  exact WordIO.Code.DescriptionFits.seq hw firstFits
    (.seq hw saved (.compute (finish left right hw fits).description_fits))

theorem staticMemory (first second : Interactive.Code w) {firstWords secondWords firstSlots secondSlots : Nat}
    (firstBound : (first.lower port).descriptionWords ≤ firstWords) (secondBound : (second.lower port).descriptionWords ≤ secondWords)
    (firstNames : WordIO.NamesBound (first.lower port) firstSlots) (secondNames : WordIO.NamesBound (second.lower port) secondSlots)
    (registers buffers : Nat) :
    ((code left right hw fits port first second).lower port).staticWords registers buffers ≤
      codeBudget left right firstWords secondWords + 4 * slots firstSlots secondSlots + registers + 3 * buffers := by
  have stored := code_bound left right hw fits port first second firstBound secondBound
  rcases names left right hw fits port first second firstNames secondNames with ⟨registerBound, bufferBound⟩
  unfold WordIO.Code.staticWords
  omega

end Signatures.Runtime.CaliperBackend.PairSampling
