import Signatures.Runtime.Caliper.SchnorrROMReplayExtract
import Signatures.Runtime.Caliper.SchnorrROMReplayExtractArithmeticBounds
import Signatures.Runtime.Caliper.StatefulCacheBuffers
import Signatures.Runtime.Caliper.CacheReadBuffers

/-! Resources of the executed extractor derived from its local code: every tag
dispatch, header projection, distribution copy, swap, routed frame, both
equality scans, both primitive contracts, the fallback draw and the retained
quotient path are charged. Budgets are stated in the width of one pass frame. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

/-- Uniform time and stored-code bounds of a representation-level realizer. -/
structure Bounded {A B : Type} {input : Representation w A} {output : Representation w B} {f : A → B}
    (realizer : Realizer .unit input output f) (time words : Nat) : Prop where
  time_le : ∀ value, realizer.time value ≤ time
  code_le : descriptionWords realizer.code ≤ words

section Generic
variable {A B D E : Type} {input : Representation w A} {middle : Representation w B} {output : Representation w D}
    {f : A → B} {g : B → D}

theorem Bounded.mono {realizer : Realizer .unit input output (g ∘ f)} {time words largerTime largerWords : Nat}
    (bound : Bounded realizer time words) (timeLe : time ≤ largerTime) (wordsLe : words ≤ largerWords) :
    Bounded realizer largerTime largerWords :=
  ⟨fun value => (bound.time_le value).trans timeLe, bound.code_le.trans wordsLe⟩
theorem Bounded.mono' {h : A → D} {realizer : Realizer .unit input output h} {time words largerTime largerWords : Nat}
    (bound : Bounded realizer time words) (timeLe : time ≤ largerTime) (wordsLe : words ≤ largerWords) :
    Bounded realizer largerTime largerWords :=
  ⟨fun value => (bound.time_le value).trans timeLe, bound.code_le.trans wordsLe⟩

theorem Bounded.then {first : Realizer .unit input middle f} {second : Realizer .unit middle output g}
    {firstTime firstWords secondTime secondWords : Nat}
    (firstBound : Bounded first firstTime firstWords) (secondBound : Bounded second secondTime secondWords) :
    Bounded (first.then second) (firstTime + secondTime) (firstWords + secondWords + 1) := by
  constructor
  · intro value
    exact Nat.add_le_add (firstBound.time_le value) (secondBound.time_le _)
  · change descriptionWords (first.code ;; second.code) ≤ _
    rw [descriptionWords_seq]
    have := firstBound.code_le
    have := secondBound.code_le
    omega

theorem Bounded.viewOutput {E' : Type} {h : A → E} {target : Representation w E'} {output : Representation w E}
    {realizer : Realizer .unit input output h} {time words : Nat} (bound : Bounded realizer time words)
    (k : A → E') (sameBytes : ∀ value, target.encoding.encode (k value) = output.encoding.encode (h value)) :
    Bounded (realizer.viewOutput target k sameBytes) time words :=
  ⟨bound.time_le, bound.code_le⟩

theorem Bounded.branch (leftRep : Representation w A) (rightRep : Representation w B) (output : Representation w D)
    {f : A → D} {g : B → D} (first : Realizer .unit leftRep output f) (second : Realizer .unit rightRep output g)
    (hw : 16 < 2 ^ w) (fits : 1 + max leftRep.encoding.words rightRep.encoding.words < 2 ^ w)
    {firstTime firstWords secondTime secondWords leftWords rightWords : Nat}
    (firstBound : Bounded first firstTime firstWords) (secondBound : Bounded second secondTime secondWords)
    (leftLe : leftRep.encoding.words ≤ leftWords) (rightLe : rightRep.encoding.words ≤ rightWords) :
    Bounded (branchRealizer .unit (by decide) leftRep rightRep output first second hw fits)
      (firstTime + secondTime + 8 * (leftWords + rightWords) + 2)
      (firstWords + secondWords + 26 * leftWords + 26 * rightWords + 37) := by
  constructor
  · rintro (value | value)
    · have bound := firstBound.time_le value
      change 1 + (1 + ((selectSlice (w := w) 1 leftRep.encoding.words).staticTime .unit + first.time value)) ≤ _
      simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
      omega
    · have bound := secondBound.time_le value
      change 1 + (1 + ((selectSlice (w := w) 1 rightRep.encoding.words).staticTime .unit + second.time value)) ≤ _
      simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
      omega
  · change descriptionWords (Dispatch.code first.code second.code _ _) ≤ _
    rw [Dispatch.code_descriptionWords]
    have := firstBound.code_le
    have := secondBound.code_le
    omega

theorem Bounded.route (parts : List (ByteRoute.Part w)) (h : A → D) (hw : 16 < 2 ^ w)
    (bounded : ByteRoute.Valid input.encoding.words parts) (size : ByteRoute.words parts = output.encoding.words)
    (correct : ∀ value, ByteRoute.bytes (input.encoding.encode value) parts = output.encoding.encode (h value)) :
    Bounded (ByteRoute.realizer input output h parts hw bounded size correct)
      (8 * output.encoding.words) (26 * output.encoding.words + 14) :=
  ⟨ByteRoute.time _ _ _ _ _ _ _ _, ByteRoute.codeWords _ _ _ _ _ _ _ _⟩
end Generic

/-! Width facts in terms of the pass frame `first`. -/

abbrev passWords := (ReplaySecond.first config).encoding.words
theorem result_words : (ForgeryHash.result config).encoding.words =
    config.message.representation.encoding.words + config.point.representation.encoding.words + 2 := by
  change (config.message.representation.encoding.words + (config.point.representation.encoding.words + 1)) + 1 = _
  omega
theorem quad_le : (quad config).representation.encoding.words ≤ 2 * (ForgeryHash.result config).encoding.words := by
  rw [quad_words, result_words]
  omega
theorem widths : (header config).encoding.words ≤ passWords config ∧
    (ForgeryHash.result config).encoding.words + 1 ≤ (header config).encoding.words ∧
    (quad config).representation.encoding.words ≤ 2 * (ForgeryHash.result config).encoding.words :=
  ⟨header_le config, forged_le config, quad_le config⟩

theorem fallback_bounded {X : Type} (input : Representation w X) : Bounded (fallback config input) 16 66 :=
  Bounded.route _ _ _ _ _ _

theorem headers_bounded : Bounded (headersRoute config) (16 * passWords config) (52 * passWords config + 14) := by
  have := widths config
  apply (Bounded.route (h := headersValue config) _ _ _ _ _).mono'
  · change 8 * ((header config).encoding.words + (header config).encoding.words) ≤ _; omega
  · change 26 * ((header config).encoding.words + (header config).encoding.words) + 14 ≤ _; omega

theorem distributeFirst_bounded : Bounded (distributeFirst config) (48 * passWords config + 26) (312 * passWords config + 251) := by
  have := widths config
  have zero : (Pairing.unitRepresentation w).encoding.words = 0 := rfl
  constructor
  · intro value
    have bound := SumContext.time (Pairing.unitRepresentation w) (ForgeryHash.result config) (header config)
      config.sampler.wordFits (frame_fits config) value
    rw [zero, Nat.zero_max] at bound
    exact bound.trans (by omega)
  · have bound := SumContext.words (Pairing.unitRepresentation w) (ForgeryHash.result config) (header config)
      config.sampler.wordFits (frame_fits config)
    rw [zero, Nat.zero_max] at bound
    exact bound.trans (by omega)

theorem distributeSecond_bounded : Bounded (distributeSecond config) (48 * passWords config + 26) (312 * passWords config + 251) := by
  have := widths config
  have zero : (Pairing.unitRepresentation w).encoding.words = 0 := rfl
  constructor
  · intro value
    have bound := SumContext.time (Pairing.unitRepresentation w) (ForgeryHash.result config) (ForgeryHash.result config)
      config.sampler.wordFits (second_fits config) value
    rw [zero, Nat.zero_max] at bound
    exact bound.trans (by omega)
  · have bound := SumContext.words (Pairing.unitRepresentation w) (ForgeryHash.result config) (ForgeryHash.result config)
      config.sampler.wordFits (second_fits config)
    rw [zero, Nat.zero_max] at bound
    exact bound.trans (by omega)

theorem swapFrame_bounded : Bounded (swapFrame config) (16 * passWords config) (52 * passWords config + 14) := by
  have := widths config
  constructor
  · intro value
    exact (Pairing.swap_time_unit_le _ _ _ _ value).trans (by omega)
  · exact (Pairing.swap_descriptionWords_le _ _ _ _ _ _).trans (by omega)

theorem gather_bounded : Bounded (gather config) (16 * passWords config) (52 * passWords config + 14) := by
  have := widths config
  apply (Bounded.route (h := gatherValue config) _ _ _ _ _).mono' <;> omega

def classifyTime (coreBudget : Nat) : Nat := coreBudget + 210 * passWords config + 110
def classifyWords (coreBudget : Nat) : Nat := coreBudget + 1000 * passWords config + 900

section Classify
variable [DecidableEq F] [DecidableEq G] [Sub F] [Div F] (arith : Arithmetic config) (budget : Arithmetic.Budget config arith)

theorem coreRealizer_bounded : Bounded (coreRealizer config arith)
    (coreTime config budget.subTime budget.divideTime) (coreWords config budget.subWords budget.divideWords) :=
  ⟨(core_bounded config arith budget).time_le, (core_bounded config arith budget).code_le⟩

theorem forged_bounded : Bounded (forged config arith)
    (coreTime config budget.subTime budget.divideTime + 16 * passWords config)
    (coreWords config budget.subWords budget.divideWords + 52 * passWords config + 15) := by
  apply ((gather_bounded config).then (coreRealizer_bounded config arith budget)).mono <;> omega

theorem secondBranch_bounded : Bounded (secondBranch config arith)
    (coreTime config budget.subTime budget.divideTime + 40 * passWords config + 18)
    (coreWords config budget.subWords budget.divideWords + 130 * passWords config + 118) := by
  have := widths config
  apply (Bounded.branch _ _ _ _ _ _ _ (fallback_bounded config _) (forged_bounded config arith budget)
    (leftWords := passWords config) (rightWords := 2 * passWords config)
    (by change 0 + _ ≤ _; omega) (by change _ + _ ≤ _; omega)).mono' <;> omega

theorem afterFirst_bounded : Bounded (afterFirst config arith)
    (coreTime config budget.subTime budget.divideTime + 104 * passWords config + 44)
    (coreWords config budget.subWords budget.divideWords + 494 * passWords config + 385) := by
  apply ((swapFrame_bounded config).then ((distributeSecond_bounded config).then
    (secondBranch_bounded config arith budget))).mono' <;> omega

theorem firstBranch_bounded : Bounded (firstBranch config arith)
    (coreTime config budget.subTime budget.divideTime + 128 * passWords config + 62)
    (coreWords config budget.subWords budget.divideWords + 572 * passWords config + 488) := by
  have := widths config
  apply (Bounded.branch _ _ _ _ _ _ _ (fallback_bounded config _) (afterFirst_bounded config arith budget)
    (leftWords := passWords config) (rightWords := 2 * passWords config)
    (by change 0 + _ ≤ _; omega) (by change _ + _ ≤ _; omega)).mono' <;> omega

theorem passes_bounded : Bounded (passes config arith)
    (coreTime config budget.subTime budget.divideTime + 192 * passWords config + 88)
    (coreWords config budget.subWords budget.divideWords + 936 * passWords config + 755) := by
  apply ((headers_bounded config).then ((distributeFirst_bounded config).then
    (firstBranch_bounded config arith budget))).mono' <;> omega

theorem classifier_bounded : Bounded (classifier config arith)
    (classifyTime config (coreTime config budget.subTime budget.divideTime))
    (classifyWords config (coreWords config budget.subWords budget.divideWords)) := by
  have bounded := Bounded.branch (Pairing.unitRepresentation w) (pair config) (choice config) (fallback config _) (passes config arith)
    config.sampler.wordFits (output config).fits (fallback_bounded config _) (passes_bounded config arith budget)
    (leftWords := 0) (rightWords := 2 * passWords config)
    (by change 0 ≤ 0; omega) (by change _ + _ ≤ 2 * (ReplaySecond.first config).encoding.words; omega)
  apply (bounded.viewOutput (classifyChoice config) (dispatched_value config arith)).mono'
  · unfold classifyTime; omega
  · unfold classifyWords; omega

end Classify

section Names
variable [DecidableEq F] [DecidableEq G] [Sub F] [Div F] (arith : Arithmetic config)

theorem classifier_names : NamesAccounted (classifier config arith).code (nameSlots config arith) := by
  have three : 3 ≤ nameSlots config arith := by unfold nameSlots; omega
  have distributedFirst := (SumContext.names (Pairing.unitRepresentation w) (ForgeryHash.result config) (header config)
    config.sampler.wordFits (frame_fits config)).mono three
  have distributedSecond := (SumContext.names (Pairing.unitRepresentation w) (ForgeryHash.result config) (ForgeryHash.result config)
    config.sampler.wordFits (second_fits config)).mono three
  have swapped : NamesAccounted (swapFrame config).code (nameSlots config arith) := Reorder.names _ _ _ _
  have fallbackNames : ∀ {X : Type} (input : Representation w X), NamesAccounted (fallback config input).code (nameSlots config arith) :=
    fun _ => ByteRoute.names _ _ _ _ _ _ _ _ _
  have gathered : NamesAccounted (gather config).code (nameSlots config arith) := ByteRoute.names _ _ _ _ _ _ _ _ _
  have headed : NamesAccounted (headersRoute config).code (nameSlots config arith) := ByteRoute.names _ _ _ _ _ _ _ _ _
  have core : NamesAccounted (coreRealizer config arith).code (nameSlots config arith) := core_names config arith
  have second : NamesAccounted (secondBranch config arith).code (nameSlots config arith) :=
    Dispatch.names (fallbackNames _) (gathered.seq core) _ _
  have first : NamesAccounted (firstBranch config arith).code (nameSlots config arith) :=
    Dispatch.names (fallbackNames _) (swapped.seq (distributedSecond.seq second)) _ _
  exact Dispatch.names (fallbackNames _) (headed.seq (distributedFirst.seq first)) _ _

def bufferBudget : Nat := max 6 (arith.slots + 1)

theorem classifier_buffers : (classifier config arith).code.memBound ≤ bufferBudget config arith := by
  have six : 6 ≤ bufferBudget config arith := by unfold bufferBudget; omega
  have core : (coreRealizer config arith).code.memBound ≤ bufferBudget config arith :=
    (core_buffers config arith).trans (by unfold bufferBudget; omega)
  have distributedFirst := (SumContext.buffers (Pairing.unitRepresentation w) (ForgeryHash.result config) (header config)
    config.sampler.wordFits (frame_fits config)).trans (show 3 ≤ bufferBudget config arith by omega)
  have distributedSecond := (SumContext.buffers (Pairing.unitRepresentation w) (ForgeryHash.result config)
    (ForgeryHash.result config) config.sampler.wordFits (second_fits config)).trans (show 3 ≤ bufferBudget config arith by omega)
  have swapped : (swapFrame config).code.memBound ≤ bufferBudget config arith := (Reorder.buffers _ _ _).trans (by omega)
  have fallbackBound : ∀ {X : Type} (input : Representation w X), (fallback config input).code.memBound ≤ bufferBudget config arith :=
    fun input => (ByteRoute.buffers _ _ _ _ _ _ _ _).trans (by omega)
  have gathered : (gather config).code.memBound ≤ bufferBudget config arith := (ByteRoute.buffers _ _ _ _ _ _ _ _).trans (by omega)
  have headed : (headersRoute config).code.memBound ≤ bufferBudget config arith := (ByteRoute.buffers _ _ _ _ _ _ _ _).trans (by omega)
  have second : (secondBranch config arith).code.memBound ≤ bufferBudget config arith :=
    (Dispatch.buffers _ _ _ _).trans (max_le (by omega) (max_le (fallbackBound _) (max_le gathered core)))
  have first : (firstBranch config arith).code.memBound ≤ bufferBudget config arith :=
    (Dispatch.buffers _ _ _ _).trans (max_le (by omega) (max_le (fallbackBound _)
      (max_le swapped (max_le distributedSecond second))))
  exact (Dispatch.buffers _ _ _ _).trans (max_le (by omega) (max_le (fallbackBound _)
    (max_le headed (max_le distributedFirst first))))

end Names

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
