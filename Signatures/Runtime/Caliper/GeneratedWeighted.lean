import Signatures.Runtime.Caliper.WeightedRows

/-! Generate a bounded weighted term list, retaining the private state in
charged storage, then execute its lazy cache fold. The generator is ordinary
Caliper code; no term list is materialized by the mathematical host. -/
namespace Signatures.Runtime.CaliperBackend.GeneratedWeighted
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F M : Type}
    (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    (domain : Layout w M) (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout).representation.encoding.words +
      (WeightedRows.rows layout).state.representation.encoding.words < 2 ^ w)

def terms := (WeightedRows.term layout).boundedList capacity countFits (by omega)
abbrev Input := domain.Value × (WeightedRows.rows layout).state.Value
def input (inputFits : domain.representation.encoding.words +
    (WeightedRows.rows layout).state.representation.encoding.words < 2 ^ w) :
    Representation w (Input layout domain) :=
  domain.representation.prod (WeightedRows.rows layout).state.representation inputFits

variable {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit domain (terms layout capacity countFits storageFits) generate)

def prepared (value : Input layout domain) : WeightedRows.Input layout capacity :=
  (listView (WeightedRows.term layout) capacity
    ⟨generate value.1.val, generator.preserves value.1.val value.1.property⟩, value.2)

theorem prepared_values (value : Input layout domain) :
    (prepared layout domain capacity countFits storageFits generator value).1.val.map Subtype.val =
      generate value.1.val :=
  listView_values (WeightedRows.term layout) capacity _

theorem prepared_length (value : Input layout domain) :
    (prepared layout domain capacity countFits storageFits generator value).1.val.length =
      (generate value.1.val).length := by
  have length := congrArg List.length
    (prepared_values layout domain capacity countFits storageFits generator value)
  simpa only [List.length_map] using length

def valid (value : Input layout domain) : Prop :=
  value.2.val.2.length + (generate value.1.val).length ≤ layout.cache.capacityPred + 1

theorem prepared_valid (value : Input layout domain) :
    WeightedRows.valid layout (prepared layout domain capacity countFits storageFits generator value) =
      valid layout domain (generate := generate) value := by
  unfold WeightedRows.valid
  rw [prepared_length]
  rfl

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)

def prepare : Interactive.Code w :=
  Interactive.retain (.compute generator.program.code)
    (Interactive.savedBuffer port (.compute generator.program.code))
    domain.representation.encoding.words
    (terms layout capacity countFits storageFits).representation.encoding.words
    (WeightedRows.rows layout).state.representation.encoding.words

variable (inputFits : domain.representation.encoding.words +
    (WeightedRows.rows layout).state.representation.encoding.words < 2 ^ w)

theorem prepare_refines :
    Interactive.Refines port .unit (input layout domain inputFits)
      (WeightedRows.input layout capacity countFits storageFits)
      (fun value => pure (prepared layout domain capacity countFits storageFits generator value))
      (prepare layout domain capacity countFits storageFits generator port) := by
  have retained := (Interactive.Refines.compute port .unit generator.program).retain (by decide)
    (WeightedRows.rows layout).state.representation layout.cache.wordFits inputFits storageFits
  have viewed := retained.viewOutput (WeightedRows.input layout capacity countFits storageFits)
    (fun value => (listView (WeightedRows.term layout) capacity value.1, value.2)) (fun _ => rfl)
  simp only [map_pure] at viewed
  exact viewed

def prepareTime (generatorTime : Nat) : Nat :=
  generatorTime + 8 * domain.representation.encoding.words +
    8 * (terms layout capacity countFits storageFits).representation.encoding.words +
    12 * (WeightedRows.rows layout).state.representation.encoding.words

def prepareWords (generatorWords : Nat) : Nat :=
  generatorWords + 26 * domain.representation.encoding.words +
    26 * (terms layout capacity countFits storageFits).representation.encoding.words +
    39 * (WeightedRows.rows layout).state.representation.encoding.words + 42

theorem prepare_time {generatorTime generatorWords : Nat}
    (budget : generator.BoundedBy generatorTime generatorWords) :
    Interactive.TimeBound port .unit (input layout domain inputFits)
      (prepare layout domain capacity countFits storageFits generator port)
      (prepareTime layout domain capacity countFits storageFits generatorTime) :=
  ((Interactive.TimeBound.compute (port := port) (cost := .unit) generator.program generatorTime budget.time_le).retain
    (Interactive.Refines.compute port .unit generator.program) (by decide)
    (WeightedRows.rows layout).state.representation layout.cache.wordFits inputFits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)

theorem prepare_words {generatorTime generatorWords : Nat}
    (budget : generator.BoundedBy generatorTime generatorWords) :
    ((prepare layout domain capacity countFits storageFits generator port).lower port).descriptionWords ≤
      prepareWords layout domain capacity countFits storageFits generatorWords := by
  have bound := Interactive.retain_descriptionWords_le port (.compute generator.program.code)
    (Interactive.savedBuffer port (.compute generator.program.code)) domain.representation.encoding.words
    (terms layout capacity countFits storageFits).representation.encoding.words
    (WeightedRows.rows layout).state.representation.encoding.words
  have stored := budget.code_le
  simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_compute] at bound
  exact bound.trans (by unfold prepareWords; omega)

theorem prepare_names {generatorNames : Nat}
    (names : NamesAccounted generator.program.code generatorNames) :
    WordIO.NamesAccounted ((prepare layout domain capacity countFits storageFits generator port).lower port)
      generatorNames :=
  Interactive.retain_names port (body := .compute generator.program.code)
    (WordIO.NamesAccounted.compute names) _ _ _

variable [DecidableEq (key.Value base)] (default : layout.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.combine layout.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)

def code (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (prepare layout domain capacity countFits storageFits generator port)
    (WeightedRows.code layout default P comparison correct update updateBuffers reserve capacity port draw)

def denote (source : OracleComp spec layout.cache.value.Value) (value : Input layout domain) :
    OracleComp spec (WeightedRows.rows layout).state.Value :=
  WeightedRows.denote layout default P comparison correct update updateBuffers reserve source
    (prepared layout domain capacity countFits storageFits generator value)

theorem listCache (source : OracleComp spec layout.cache.value.Value) (value : Input layout domain)
    (admitted : valid layout domain (generate := generate) value) :
    Subtype.val <$> denote layout domain capacity countFits storageFits generator
      default P comparison correct update updateBuffers reserve source value =
      (generate value.1.val).foldlM (WeightedRows.sourceStep (combine := combine) (Subtype.val <$> source))
        value.2.val := by
  have result := WeightedRows.listCache layout default P comparison correct update updateBuffers reserve source
    (prepared layout domain capacity countFits storageFits generator value)
    ((prepared_valid layout domain capacity countFits storageFits generator value).mpr admitted)
  rw [prepared_values] at result
  exact result

theorem cache_growth (source : OracleComp spec layout.cache.value.Value) (value : Input layout domain)
    (admitted : valid layout domain (generate := generate) value) (answer : (WeightedRows.rows layout).state.Value)
    (reached : answer ∈ support (denote layout domain capacity countFits storageFits generator
      default P comparison correct update updateBuffers reserve source value)) :
    answer.val.2.length ≤ value.2.val.2.length + (generate value.1.val).length := by
  have growth := WeightedRows.cache_growth layout default P comparison correct update updateBuffers reserve source
    (prepared layout domain capacity countFits storageFits generator value)
    ((prepared_valid layout domain capacity countFits storageFits generator value).mpr admitted) answer reached
  rw [prepared_length] at growth
  exact growth

variable {source : OracleComp spec layout.cache.value.Value} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation
      layout.cache.value.representation (fun _ => source) draw)

include drawCorrect in
theorem refines :
    Interactive.RefinesOn (valid layout domain (generate := generate)) port .unit (input layout domain inputFits)
      (WeightedRows.rows layout).state.representation
      (denote layout domain capacity countFits storageFits generator default P comparison correct update updateBuffers reserve source)
      (code layout domain capacity countFits storageFits generator port default P comparison correct update updateBuffers reserve draw) := by
  have composed := ((prepare_refines layout domain capacity countFits storageFits generator port inputFits).on
    (valid layout domain (generate := generate))).seq
    (WeightedRows.refines layout default P comparison correct update updateBuffers reserve port drawCorrect
      capacity countFits storageFits) (by
        intro value admitted answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact (prepared_valid layout domain capacity countFits storageFits generator value).mpr admitted)
  simp only [pure_bind] at composed
  exact composed

include drawCorrect in
theorem time_bound {generatorTime generatorWords drawTime updateTime updateWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) :
    Interactive.TimeBoundOn (valid layout domain (generate := generate)) port .unit (input layout domain inputFits)
      (code layout domain capacity countFits storageFits generator port default P comparison correct update updateBuffers reserve draw)
      (prepareTime layout domain capacity countFits storageFits generatorTime +
        RowFold.timeBudget (WeightedRows.rows layout) capacity drawTime updateTime) :=
  ((prepare_time layout domain capacity countFits storageFits generator port inputFits generatorBound).on
    (valid layout domain (generate := generate))).seq
    ((prepare_refines layout domain capacity countFits storageFits generator port inputFits).on
      (valid layout domain (generate := generate)))
    (WeightedRows.time_bound layout default P comparison correct update updateBuffers reserve port drawCorrect
      capacity countFits storageFits drawBound updateBound) (by
        intro value admitted answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact (prepared_valid layout domain capacity countFits storageFits generator value).mpr admitted)

end Signatures.Runtime.CaliperBackend.GeneratedWeighted
