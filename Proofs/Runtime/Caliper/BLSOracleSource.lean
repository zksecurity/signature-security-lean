import Proofs.Runtime.Caliper.BLSOracle

/-! Joint source semantics for every represented random/hash/sign request.
The observation erases representation proofs; execution itself manipulates words. -/

namespace Signatures.Runtime.CaliperBackend.BLSOracle
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM

section Views
variable {w : Nat} {M R C G : Type} [DecidableEq M]
    (layout : BLSReply.Layouts w M R C G) (default : layout.cache.value.Value) (randomBound : Nat)

def query : (Fin (randomBound + 1) × layout.store.Value) ⊕ (BLSDispatch.input layout default).Value → (advSpec M M G).Domain
  | .inl value => .inl (.inl value.1.val)
  | .inr ⟨.inl value, _⟩ => .inl (.inr value.1)
  | .inr ⟨.inr value, _⟩ => .inr value.1

def saved : (Fin (randomBound + 1) × layout.store.Value) ⊕ (BLSDispatch.input layout default).Value → BLSReply.Store M R C G
  | .inl value => value.2.val
  | .inr ⟨.inl value, _⟩ | .inr ⟨.inr value, _⟩ => value.2

def answer : (q : (advSpec M M G).Domain) → (advSpec M M G).Range q → Nat ⊕ G
  | .inl (.inl _), value => .inl value.val
  | .inl (.inr _), value | .inr _, value => .inr value

def decoded : (UniformQuery.Reply randomBound × layout.store.Value) ⊕ layout.output.Value →
    (Nat ⊕ G) × BLSReply.Store M R C G
  | .inl value => (.inl value.1.2.val, value.2.val)
  | .inr value => (.inr value.val.1, value.val.2)
end Views

variable {w : Nat} {C G : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (layout : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value) (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (draw : Interactive.Code w)
    (drawSource : ProbComp layout.cache.value.Value)
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => drawSource) draw)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include drawLaw in
theorem denote_source (value : (Fin (randomBound + 1) × layout.store.Value) ⊕ (BLSDispatch.input layout default).Value) :
    decoded layout randomBound <$> denote layout default randomBound P comparison correct response responseBuffers reserve drawSource value =
      (fun out => (answer (query layout default randomBound value) out.1, (saved layout default randomBound value).1, out.2)) <$>
        ((LazyAGM.listOracle (fun sample => respond false (sample, (saved layout default randomBound value).1))
          (fun sample => respond true (sample, (saved layout default randomBound value).1))) (query layout default randomBound value)).run
            (saved layout default randomBound value).2 := by
  rcases value with ⟨n, stored⟩ | ⟨value, valid⟩
  · simp only [denote, Sum.elim_inl, UniformQuery.forwardSource, UniformQuery.source, Functor.map_map,
      query, saved, LazyAGM.listOracle_random]
    rfl
  · cases value with
    | inl value =>
      have law := BLSDispatch.denote_source layout default P comparison correct response responseBuffers reserve drawSource drawLaw false ⟨value, valid⟩
      have mapped := congrArg (fun computation : ProbComp (G × BLSReply.Store (key.Value base) (val.Value base) C G) =>
        (fun out => ((Sum.inr out.1 : Nat ⊕ G), out.2)) <$> computation) law
      simp only [denote, Sum.elim_inr, Functor.map_map, decoded, query, saved, answer, BLSDispatch.request, LazyAGM.listOracle, StateT.run] at mapped ⊢
      convert mapped using 1
    | inr value =>
      have law := BLSDispatch.denote_source layout default P comparison correct response responseBuffers reserve drawSource drawLaw true ⟨value, valid⟩
      have mapped := congrArg (fun computation : ProbComp (G × BLSReply.Store (key.Value base) (val.Value base) C G) =>
        (fun out => ((Sum.inr out.1 : Nat ⊕ G), out.2)) <$> computation) law
      simp only [denote, Sum.elim_inr, Functor.map_map, decoded, query, saved, answer, BLSDispatch.request, LazyAGM.listOracle, StateT.run] at mapped ⊢
      convert mapped using 1

include drawCorrect drawLaw in
theorem observe (value : (Fin (randomBound + 1) × layout.store.Value) ⊕ (BLSDispatch.input layout default).Value)
    (tape : RandomTape w) (before : State w) (holds : (input layout default randomBound randomFits).Holds value before) :
    (fun result => decoded layout randomBound <$> Interactive.observe (output layout randomBound randomFits) result) <$>
      (code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).execute
        (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit tape before =
      some <$> ((fun out => (answer (query layout default randomBound value) out.1, (saved layout default randomBound value).1, out.2)) <$>
        ((LazyAGM.listOracle (fun sample => respond false (sample, (saved layout default randomBound value).1))
          (fun sample => respond true (sample, (saved layout default randomBound value).1))) (query layout default randomBound value)).run
            (saved layout default randomBound value).2) := by
  have observed := (refines layout default randomBound randomFits P comparison correct response responseBuffers reserve draw
    drawSource drawCorrect).observe tape value before holds
  have mapped := congrArg (fun computation : ProbComp (Option ((UniformQuery.Reply randomBound × layout.store.Value) ⊕ layout.output.Value)) =>
    (fun result => decoded layout randomBound <$> result) <$> computation) observed
  rw [← denote_source layout default randomBound P comparison correct response responseBuffers reserve drawSource drawLaw value]
  have middle : (fun result => decoded layout randomBound <$> result) <$> some <$>
      denote layout default randomBound P comparison correct response responseBuffers reserve drawSource value =
        some <$> decoded layout randomBound <$> denote layout default randomBound P comparison correct response responseBuffers reserve drawSource value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans (PFunctor.FreeM.comp_map some (decoded layout randomBound) _)
  exact (PFunctor.FreeM.comp_map _ _ _).trans (mapped.trans middle)

end Signatures.Runtime.CaliperBackend.BLSOracle
