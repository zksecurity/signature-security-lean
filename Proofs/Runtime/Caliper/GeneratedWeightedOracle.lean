import Proofs.Runtime.Caliper.GeneratedWeightedBounds
import Proofs.Runtime.Caliper.WeightedRowsOracle
import Proofs.Runtime.WeightedCacheEncoding

/-! Source oracle identities for generated weighted evaluation. Key encoding
is an injective proof relation on encountered lists, preserving complete cache
state. No runtime traversal of the key universe or cache conversion is added. -/
namespace Signatures.Runtime.CaliperBackend.GeneratedWeighted
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F M : Type}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    (domain : Layout w M) (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout).representation.encoding.words +
      (WeightedRows.rows layout).state.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit domain (terms layout capacity countFits storageFits) generate)
    (default : layout.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.combine layout.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (source : ProbComp layout.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include combineLaw uniform in
theorem evalTerms_source (value : Input layout domain)
    (admitted : valid layout domain (generate := generate) value) :
    Subtype.val <$> denote layout domain capacity countFits storageFits generator
      default P comparison correct update updateBuffers reserve source value =
      (fun result => (value.2.val.1 + result.1, result.2)) <$>
        (simulateQ (privateListOracle (M := key.Value base) (R := val.Value base))
          (evalTerms (generate value.1.val))).run value.2.val.2 := by
  have result := WeightedRows.evalTerms_source layout default P comparison correct update updateBuffers reserve
    combineLaw source uniform (prepared layout domain capacity countFits storageFits generator value)
    ((prepared_valid layout domain capacity countFits storageFits generator value).mpr admitted)
  rw [prepared_values] at result
  exact result

include combineLaw uniform in
theorem evalTerms_encoded {J : Type} [DecidableEq J] (encode : J → key.Value base)
    (injective : Function.Injective encode) (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map encode id))
    (value : Input layout domain) (admitted : valid layout domain (generate := generate) value)
    (cache : List (J × val.Value base)) (cacheEqual : value.2.val.2 = cache.map (Prod.map encode id)) :
    Subtype.val <$> denote layout domain capacity countFits storageFits generator
      default P comparison correct update updateBuffers reserve source value =
      (fun result => (value.2.val.1 + result.1, result.2.map (Prod.map encode id))) <$>
        (simulateQ (privateListOracle (M := J) (R := val.Value base))
          (evalTerms (sourceTerms value.1.val))).run cache := by
  rw [evalTerms_source layout domain capacity countFits storageFits generator
    default P comparison correct update updateBuffers reserve combineLaw source uniform value admitted,
    termsEqual, cacheEqual, WeightedAGM.evalTerms_encoded encode injective, Functor.map_map]

include combineLaw uniform in
theorem evalTerms_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (value : Input layout domain) (admitted : valid layout domain (generate := generate) value) :
    (fun result => (result.val.1, result.val.2.map (Prod.map keys.symm id))) <$>
      denote layout domain capacity countFits storageFits generator
        default P comparison correct update updateBuffers reserve source value =
      (fun result => (value.2.val.1 + result.1, result.2)) <$>
        (simulateQ (privateListOracle (M := J) (R := val.Value base))
          (evalTerms (sourceTerms value.1.val))).run (value.2.val.2.map (Prod.map keys.symm id)) := by
  have back : (value.2.val.2.map (Prod.map keys.symm id)).map (Prod.map keys id) = value.2.val.2 := by
    simp [List.map_map, Function.comp_def, Prod.map]
  have result := evalTerms_encoded layout domain capacity countFits storageFits generator
    default P comparison correct update updateBuffers reserve combineLaw source uniform
    keys keys.injective sourceTerms termsEqual value admitted
    (value.2.val.2.map (Prod.map keys.symm id)) back.symm
  calc
    _ = (fun result => (result.1, result.2.map (Prod.map keys.symm id))) <$>
        (Subtype.val <$> denote layout domain capacity countFits storageFits generator
          default P comparison correct update updateBuffers reserve source value) := by rw [Functor.map_map]
    _ = _ := by
      rw [result, Functor.map_map]
      simp [List.map_map, Function.comp_def, Prod.map]

include combineLaw uniform in
theorem observe_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation
      layout.cache.value.representation (fun _ => source) draw)
    (inputFits : domain.representation.encoding.words +
      (WeightedRows.rows layout).state.representation.encoding.words < 2 ^ w)
    (tape : RandomTape w) (value : Input layout domain)
    (admitted : valid layout domain (generate := generate) value) (before : State w)
    (holds : (input layout domain inputFits).Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$>
        Interactive.observe (WeightedRows.rows layout).state.representation result) <$>
      (code layout domain capacity countFits storageFits generator port
        default P comparison correct update updateBuffers reserve draw).execute port .unit tape before =
      some <$> ((fun result => (value.2.val.1 + result.1, result.2)) <$>
        (simulateQ (privateListOracle (M := J) (R := val.Value base))
          (evalTerms (sourceTerms value.1.val))).run (value.2.val.2.map (Prod.map keys.symm id))) := by
  have observed := (refines layout domain capacity countFits storageFits generator port inputFits
    default P comparison correct update updateBuffers reserve drawCorrect).observe tape value admitted before holds
  have mapped := congrArg (fun program : ProbComp (Option (WeightedRows.rows layout).state.Value) =>
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$> result) <$> program) observed
  rw [← evalTerms_equiv layout domain capacity countFits storageFits generator
    default P comparison correct update updateBuffers reserve combineLaw source uniform
    keys sourceTerms termsEqual value admitted]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped

end Signatures.Runtime.CaliperBackend.GeneratedWeighted
