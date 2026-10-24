import Proofs.Runtime.Caliper.WeightedHashFinish
import Proofs.Runtime.WeightedExecution
import Proofs.Runtime.WeightedCacheEncoding

/-! Complete weighted hash handling: actual lazy lookup, one local group
response and recording of the delivered point with all retained state copied. -/
namespace Signatures.Runtime.CaliperBackend.WeightedHash
open Caliper BoundedSource OracleComp OracleSpec

def decodeOutput {K J M R C G : Type} (decode : K → J) (value : G × Store K M R C G) :
    G × Store J M R C G :=
  (value.1, value.2.1, value.2.2.1.map (Prod.map decode id),
    value.2.2.2.1.map (Prod.map decode id), value.2.2.2.2)

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M (val.Value base) C G)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w)

def lookup : Interactive.Code w := EncodedCacheRead.code layout.cache P comparison correct port draw
def read : Interactive.Code w :=
  Interactive.retain (lookup layout P comparison correct port draw)
    (Interactive.savedBuffer port (lookup layout P comparison correct port draw))
    layout.cache.input.representation.encoding.words layout.evaluated.representation.encoding.words
    layout.input.representation.encoding.words

variable {respond : val.Value base × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {slots : Nat} (responseBuffers : response.program.code.memBound ≤ slots) (reserve : slots < 2 ^ w)

def code : Interactive.Code w :=
  .seq (.compute (prepare layout).code)
    (.seq (read layout P comparison correct port draw)
      (.compute (tail layout response responseBuffers reserve).code))
def denote (source : OracleComp spec layout.cache.value.Value) (value : layout.input.Value) :
    OracleComp spec layout.output.Value :=
  (fun answer => completed layout response (answer, value)) <$>
    EncodedCacheRead.denote layout.cache P comparison correct source (argument layout value)

theorem refines {source : OracleComp spec layout.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation
      layout.cache.value.representation (fun _ => source) draw) :
    Interactive.Refines port .unit layout.input.representation layout.output.representation
      (denote layout P comparison correct response source)
      (code layout P comparison correct port draw response responseBuffers reserve) := by
  have cached := (EncodedCacheRead.refines layout.cache P comparison correct port source draw drawCorrect).retain
    (by decide) layout.input.representation layout.cache.wordFits layout.prepared.fits layout.post.fits
  have composed := (Interactive.Refines.compute port .unit (prepare layout)).seq
    (cached.seq (Interactive.Refines.compute port .unit (tail layout response responseBuffers reserve)))
  convert composed using 1
  · funext value
    simp only [pure_bind, bind_pure_comp, Functor.map_map, denote]
    rfl
  · rfl

section Source
variable {F : Type} [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (terms : M → List (key.Value base × F)) (sign : val.Value base → G)

theorem denote_source (source : ProbComp layout.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (value : layout.input.Value) :
    Subtype.val <$> denote layout P comparison correct response source value =
      (fun answer => (answer.1, value.val.2.1, answer.2)) <$>
        ((WeightedAGM.listOracle terms (fun scalar => respond (scalar, value.val.2.1)) sign)
          (.inl (.inr value.val.1))).run (value.val.2.2.1, value.val.2.2.2) := by
  have cached := BLSCache.denote_privateOracle layout.cache P comparison correct source uniform (argument layout value)
  have mapped := congrArg (fun computation : ProbComp (val.Value base × List (key.Value base × val.Value base)) =>
    (fun answer => (respond (answer.1, value.val.2.1), value.val.2.1, answer.2,
      (value.val.1, respond (answer.1, value.val.2.1)) :: value.val.2.2.2.1, value.val.2.2.2.2)) <$> computation) cached
  rw [WeightedAGM.listOracle_hash]
  simp only [denote, Functor.map_map] at mapped ⊢
  exact mapped

theorem observe (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (source : ProbComp layout.cache.value.Value)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation
      layout.cache.value.representation (fun _ => source) draw)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (tape : RandomTape w) (value : layout.input.Value)
    (before : State w) (holds : layout.input.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe layout.output.representation result) <$>
      (code layout P comparison correct port draw response responseBuffers reserve).execute port .unit tape before =
      some <$> ((fun answer => (answer.1, value.val.2.1, answer.2)) <$>
        ((WeightedAGM.listOracle terms (fun scalar => respond (scalar, value.val.2.1)) sign)
          (.inl (.inr value.val.1))).run (value.val.2.2.1, value.val.2.2.2)) := by
  have observed := (refines layout P comparison correct port draw response responseBuffers reserve drawCorrect).observe
    tape value before holds
  have mapped := congrArg (fun computation : ProbComp (Option layout.output.Value) =>
    (fun result => Subtype.val <$> result) <$> computation) observed
  rw [← denote_source layout P comparison correct response terms sign source uniform value]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped

theorem denote_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (source : ProbComp layout.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (value : layout.input.Value) :
    (fun answer => decodeOutput keys.symm answer.val) <$> denote layout P comparison correct response source value =
      (fun answer => (answer.1, value.val.2.1, answer.2)) <$>
        ((WeightedAGM.listOracle sourceTerms (fun scalar => respond (scalar, value.val.2.1)) sign)
          (.inl (.inr (keys.symm value.val.1)))).run
            (value.val.2.2.1.map (Prod.map keys.symm id),
              value.val.2.2.2.1.map (Prod.map keys.symm id), value.val.2.2.2.2) := by
  have cached :
      (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$>
        EncodedCacheRead.denote layout.cache P comparison correct source (argument layout value) =
        ((BLS.LazyAGM.Reduction.privateListOracle (M := J) (R := val.Value base))
          (.inr (keys.symm value.val.1))).run (value.val.2.2.1.map (Prod.map keys.symm id)) := by
    calc
      _ = (fun answer => (answer.1, answer.2.map (Prod.map keys.symm id))) <$>
          (Subtype.val <$> EncodedCacheRead.denote layout.cache P comparison correct source (argument layout value)) := by
        rw [Functor.map_map]
      _ = _ := by
        rw [BLSCache.denote_privateOracle layout.cache P comparison correct source uniform]
        exact (WeightedAGM.privateRead_encoded keys.symm keys.symm.injective value.val.1 value.val.2.2.1).symm
  have mapped := congrArg (fun computation : ProbComp (val.Value base × List (J × val.Value base)) =>
    (fun answer => (respond (answer.1, value.val.2.1), value.val.2.1, answer.2,
      (keys.symm value.val.1, respond (answer.1, value.val.2.1)) ::
        value.val.2.2.2.1.map (Prod.map keys.symm id), value.val.2.2.2.2)) <$> computation) cached
  rw [WeightedAGM.listOracle_hash]
  simp only [denote, Functor.map_map] at mapped ⊢
  exact mapped

theorem observe_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (source : ProbComp layout.cache.value.Value)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation
      layout.cache.value.representation (fun _ => source) draw)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (tape : RandomTape w) (value : layout.input.Value)
    (before : State w) (holds : layout.input.representation.Holds value before) :
    (fun result => (fun answer => decodeOutput keys.symm answer.val) <$>
        Interactive.observe layout.output.representation result) <$>
      (code layout P comparison correct port draw response responseBuffers reserve).execute port .unit tape before =
      some <$> ((fun answer => (answer.1, value.val.2.1, answer.2)) <$>
        ((WeightedAGM.listOracle sourceTerms (fun scalar => respond (scalar, value.val.2.1)) sign)
          (.inl (.inr (keys.symm value.val.1)))).run
            (value.val.2.2.1.map (Prod.map keys.symm id),
              value.val.2.2.2.1.map (Prod.map keys.symm id), value.val.2.2.2.2)) := by
  have observed := (refines layout P comparison correct port draw response responseBuffers reserve drawCorrect).observe
    tape value before holds
  have mapped := congrArg (fun computation : ProbComp (Option layout.output.Value) =>
    (fun result => (fun answer => decodeOutput keys.symm answer.val) <$> result) <$> computation) observed
  rw [← denote_equiv layout P comparison correct response sign keys sourceTerms source uniform value]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped

end Source
end Signatures.Runtime.CaliperBackend.WeightedHash
