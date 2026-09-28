import Signatures.Model.SignatureInterface
import AlgebraicGroupModel.Interaction

/-!
# Signature games through the interactive AGM

Signature requests have no group arguments. Replies expose group elements without explanations.
The compiler translates the signature's grouped coefficient lists into vectors over chronological
inputs. Malformed reply shapes are rejected, so algebraicity holds on all reply paths, not only
those produced by the signature handler. Both source groups are explicit: the generator is a
signature-group input and the verification key is a verification-group input. The initial
ordinary payload is Unit. Messages and sampled numbers remain ordinary data, never signatures.
-/

namespace AlgebraicGroupModel

/-- Translate token-indexed signature outputs to exact-length vectors in the sole group sort. -/
-- Convert a token representation using only the algebraic operations needed to evaluate it.
def Output.explain {F Token Payload G : Type} [Zero F] [AddMonoid G] [SMul F G]
    -- inputs is the ordered received basis; out provides one coefficient for each token.
    (out : Output F Token Payload) (inputs : Transcript Token G) :
    -- This helper has one group label, Unit, and preserves the ordinary payload type.
    Interaction.Explained F Payload (fun _ : Unit => G) :=
  -- Construct the point and its explanation together over the received group values.
  Interaction.Explained.ofVectors (fun _ => inputs.map Prod.snd) out.value
    -- Supply one vector with exactly one coefficient per received position, selected by its token.
    (fun _ => [fun i => out.coefficients (inputs[i.val]'(by simpa using i.isLt)).1])

theorem Output.explain_valid {F Token Payload G : Type} [Zero F] [AddMonoid G] [SMul F G]
    (out : Output F Token Payload) (inputs : Transcript Token G) :
    (out.explain inputs).Valid (fun _ => inputs.map Prod.snd) :=
  Interaction.Explained.valid_ofVectors _ _ _

/-- The adapter supplies witnesses without changing the original materialized group element. -/
theorem Output.explain_value {F Token Payload G : Type} [Zero F] [AddMonoid G] [SMul F G]
    (out : Output F Token Payload) (inputs : Transcript Token G) :
    (out.explain inputs).value = ⟨out.value, fun _ => [out.coefficients.eval inputs]⟩ := by
  simp [Output.explain, Interaction.Explained.ofVectors, Interaction.evaluate,
    Representation.eval, List.mapIdx_eq_ofFn]
  funext s
  apply congrArg (fun g => [g])
  exact congrArg List.sum (List.ofFn_getElem_eq_map inputs
    (fun p => out.coefficients p.1 • p.2))

end AlgebraicGroupModel

open OracleComp OracleSpec

namespace Model.LazyAGM

namespace Interactive

open AlgebraicGroupModel

/-- The signature and verification-key groups are tracked separately. -/
-- These labels select separate received-input lists, even if both carrier types happen to agree.
inductive GroupSort where
  -- Signature points, hash replies, and the signature-group generator use this label.
  | signature
  -- Verification keys use this label.
  | verification

-- Map each label to the Lean type of points allowed in that list.
abbrev Group (G₁ G₂ : Type) : GroupSort → Type
  -- Signature-labeled values must have type G1.
  | .signature => G₁
  -- Verification-labeled values must have type G2.
  | .verification => G₂

instance {G₁ G₂ : Type} [AddMonoid G₁] [AddMonoid G₂] (s : GroupSort) :
    AddMonoid (Group G₁ G₂ s) := by
  cases s <;> dsimp [Group] <;> infer_instance

instance (priority := high) {F G₁ G₂ : Type} [SMul F G₁] [SMul F G₂] (s : GroupSort) :
    SMul F (Group G₁ G₂ s) := by
  cases s <;> dsimp [Group] <;> infer_instance

-- Package two ordinary typed lists as the dependent family expected by the AGM library.
def groupLists {G₁ G₂ : Type} (signatures : List G₁) (keys : List G₂) :
    -- Each label returns a list whose element type is selected by Group.
    Interaction.Groups (Group G₁ G₂)
  -- Project the supplied signature-group list.
  | .signature => signatures
  -- Project the supplied verification-group list.
  | .verification => keys

@[simp] theorem extend_groupLists {G₁ G₂ : Type} (xs ys : List G₁) (ks ls : List G₂) :
    Interaction.extend (groupLists xs ks) (groupLists ys ls) =
      groupLists (xs ++ ys) (ks ++ ls) := by
  funext s
  cases s <;> rfl

-- The game initially supplies one generator and one public key, with no ordinary input data.
def initialInput {G₁ G₂ : Type} (g : G₁) (pk : G₂) : Interaction.Message Unit (Group G₁ G₂) :=
  -- Both group inputs are tracked explicitly rather than hidden in the Unit payload.
  ⟨(), groupLists [g] [pk]⟩

-- The request's data selects randomness n, base index i, or signing message m, respectively.
abbrev Query (ι M : Type) := (Nat ⊕ ι) ⊕ M

-- Only the ordinary reply-data type depends on the request; group lists are separate fields.
def Reply {ι M : Type} : Query ι M → Type
  -- A uniform request n returns a number in 0,...,n in its ordinary data field.
  | .inl (.inl n) => Fin (n + 1)
  -- Hash/sign replies put their point in groups, leaving only Unit as ordinary data.
  | _ => Unit

-- none means adapter rejection; some carries the coefficient output and actual signed messages.
abbrev Result (F M : Type) := Option (Output F M × List M)

-- The adapter evaluates F-linear combinations in the signature group G.
variable {F ι M G G₂ : Type} [Zero F] [AddCommMonoid G] [SMul F G]
  -- G2 remains a separately tracked group with the same scalar type.
  [AddMonoid G₂] [SMul F G₂]

-- Rejection has no output points, so all explanation lists are empty as well.
def reject : Interaction.Explained F (Result F M) (Group G G₂) := ⟨⟨none, fun _ => []⟩, fun _ => []⟩

-- Wrap a signature query in the generic explained-request envelope.
def request (q : Query ι M) : Interaction.Explained F (Query ι M) (Group G G₂) :=
  -- This adapter always sends zero group arguments; the generic envelope type alone is broader.
  ⟨⟨q, fun _ => []⟩, fun _ => []⟩

-- Turn A's coefficient output and recorded signing history into a final explained message.
def finish (out : Output F M) (tr : Transcript ι M G)
    -- seen records generator/hash/signature tokens in their actual order of receipt.
    (seen : AlgebraicGroupModel.Transcript Token G) :
    -- The final envelope supports both group labels, but this adapter outputs only a signature.
    Interaction.Explained F (Result F M) (Group G G₂) :=
  -- Evaluate A's coefficients and build an exact-length explanation over seen.
  let explained := out.toAlgebraic.explain seen
  -- Supply the actual signed-message log as data and the constructed signature as a G point.
  ⟨⟨some (out, tr.2.map Prod.fst), groupLists (explained.value.groups ()) []⟩,
    -- Match each group's explanation list to that group's outgoing points.
    fun s => match s with
      -- There is one signature point, with the coefficient vector just constructed.
      | .signature => explained.coefficients ()
      -- No verification-group point is output, so no vector is required for that group.
      | .verification => []⟩

-- Translate the signature-specific oracle program without restricting its adaptive branching.
def compile (program : OracleComp (advSpec ι M G) (Output F M))
    -- Carry both chronological tokens and grouped transcripts while translating each path.
    (seen : AlgebraicGroupModel.Transcript Token G) (tr : Transcript ι M G) :
    -- The translated program uses the AGM interface whose outgoing requests require explanations.
    OracleComp (Interaction.explainedSpec F (Group G G₂) (Query ι M) Reply)
      -- Its final result likewise carries ordinary data, group points, and explanation vectors.
      (Interaction.Explained F (Result F M) (Group G G₂)) :=
  -- Recurse over pure return and oracle-query nodes of the original program.
  OracleComp.recOn
    -- Each recursively translated continuation still accepts the two evolving transcripts.
    (motive := fun _ => AlgebraicGroupModel.Transcript Token G → Transcript ι M G →
      -- It produces a program using the same explained-request interface.
      OracleComp (Interaction.explainedSpec F (Group G G₂) (Query ι M) Reply)
        -- Every branch eventually returns the same explained-result type.
        (Interaction.Explained F (Result F M) (Group G G₂))) program
    -- At a return node, construct the final point from coefficients and actual received inputs.
    (fun out seen tr => pure (finish out tr seen))
    -- next is the recursively translated reply-dependent continuation; dispatch on the request.
    (fun q _ next seen tr => match q with
      -- Forward a private-randomness request as an explained envelope with empty group lists.
      | .inl (.inl n) => OracleComp.queryBind (request (.inl (.inl n))) fun reply =>
          -- The translator expects randomness replies to carry no signature-group points.
          match reply.groups .signature with
          -- Resume with the sampled number and unchanged signature transcripts.
          | [] => next reply.data seen tr
          -- A nonempty signature-group list on this branch produces the rejection result.
          | _ => pure reject
      -- Forward an explicit base request; later behavior may depend on its actual point value.
      | .inl (.inr i) => OracleComp.queryBind (request (.inl (.inr i))) fun reply =>
          -- Require exactly one signature-group point for this explicit base reply.
          match reply.groups .signature with
          -- Give H to the continuation and add its unique occurrence token chronologically.
          | [H] => next H (seen ++ [(.inr (.inl tr.1.length), H)])
              -- Also record (index,H) in the hash transcript, leaving signing history unchanged.
              (tr.1 ++ [(i, H)], tr.2)
          -- Zero or multiple signature-group points are a malformed base reply.
          | _ => pure reject
      -- Forward a signing request; the signer, not the adversary, determines the returned point.
      | .inr m => OracleComp.queryBind (request (.inr m)) fun reply =>
          -- Require exactly one signature-group point for the signing response.
          match reply.groups .signature with
          -- Deliver the signature and append its signing-occurrence token to the received basis.
          | [s] => next s (seen ++ [(.inr (.inr tr.2.length), s)])
              -- Record the actual signed message and point, without adding internal hash lookups.
              (tr.1, tr.2 ++ [(m, s)])
          -- Reject malformed signing replies; initialize this recursion with the supplied state.
          | _ => pure reject) seen tr

theorem compile_algebraic (program : OracleComp (advSpec ι M G) (Output F M))
    (seen : AlgebraicGroupModel.Transcript Token G) (tr : Transcript ι M G) (keys : List G₂) :
    Interaction.IsAlgebraic (groupLists (seen.map Prod.snd) keys)
      (compile program seen tr) := by
  induction program using OracleComp.recOn generalizing seen tr keys with
  | pure out =>
      intro s
      cases s with
      | signature => exact AlgebraicGroupModel.Output.explain_valid out.toAlgebraic seen ()
      | verification => exact List.Forall₂.nil
  | queryBind q next ih =>
      rcases q with ((n | i) | m)
      all_goals
        change Interaction.IsAlgebraic _ (OracleComp.queryBind _ _)
        rw [Interaction.isAlgebraic_query]
        refine ⟨fun _ => List.Forall₂.nil, ?_⟩
        intro reply
        rcases reply with ⟨data, groups⟩
        obtain ⟨xs, ks, rfl⟩ : ∃ xs : List G, ∃ ks : List G₂, groups = groupLists xs ks :=
          ⟨groups .signature, groups .verification, by funext s; cases s <;> rfl⟩
        rw [extend_groupLists]
        cases xs with
        | nil =>
            first
            | exact fun _ => List.Forall₂.nil
            | change Interaction.IsAlgebraic _ (compile (next data) seen tr)
              simpa only [List.append_nil] using ih data seen tr (keys ++ ks)
        | cons g rest =>
            first
            | exact fun _ => List.Forall₂.nil
            | cases rest with
              | nil =>
                  first
                  | change Interaction.IsAlgebraic _ (compile (next g)
                      (seen ++ [(.inr (.inl tr.1.length), g)]) (tr.1 ++ [(i, g)], tr.2))
                    have valid := ih g (seen ++ [(.inr (.inl tr.1.length), g)])
                      (tr.1 ++ [(i, g)], tr.2) (keys ++ ks)
                    simpa only [List.map_append, List.map_cons, List.map_nil] using valid
                  | change Interaction.IsAlgebraic _ (compile (next g)
                      (seen ++ [(.inr (.inr tr.2.length), g)]) (tr.1, tr.2 ++ [(m, g)]))
                    have valid := ih g (seen ++ [(.inr (.inr tr.2.length), g)])
                      (tr.1, tr.2 ++ [(m, g)]) (keys ++ ks)
                    simpa only [List.map_append, List.map_cons, List.map_nil] using valid
              | cons _ _ => exact fun _ => List.Forall₂.nil

/-- The real interface always returns zero (randomness) or one (hash/sign) group input. -/
-- Supply effects in any monad N; the query types alone do not define these oracle behaviors.
def impl {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N)
    -- The actual game supplies cached base lookup and secret-key signing implementations.
    (hash : ι → N G) (sign : M → N G) :
    -- Read q from ordinary request data; compile produces no outgoing group arguments to inspect.
    QueryImpl (Interaction.plainSpec (Group G G₂) (Query ι M) Reply) N := fun ⟨q, _⟩ =>
  -- Reply types depend on the request tag, while the implementation fixes group-list contents.
  match q with
  -- Randomness returns its number in data and leaves both group lists empty.
  | .inl (.inl n) => do return ⟨← random n, fun _ => []⟩
  -- An explicit base request selects the point associated with index i.
  | .inl (.inr i) => do
      -- The surrounding lazy implementation samples once and reuses the cached point.
      let H ← hash i
      -- Return an unexplained point in the signature group; it becomes a new received input.
      return ⟨(), groupLists [H] []⟩
  -- A signing request selects the scheme's secret-key signer for message m.
  | .inr m => do
      -- Produce the signature, possibly using internal lookups in the shared base cache.
      let s ← sign m
      -- Expose only that signature as a new received input, with no G2 point or explanation.
      return ⟨(), groupLists [s] []⟩

/-- Chronological and grouped transcripts evaluate every signature representation identically. -/
def Aligned (g : G) (seen : AlgebraicGroupModel.Transcript Token G)
    (tr : Transcript ι M G) : Prop :=
  ∀ out : Output F M, out.toAlgebraic.coefficients.eval seen = materialize g out tr

theorem aligned_initial (g : G) :
    Aligned (F := F) (ι := ι) (M := M) g [(.inl (), g)] ([], []) := by
  intro out
  rfl

theorem aligned_hash (g : G) (seen : AlgebraicGroupModel.Transcript Token G)
    (tr : Transcript ι M G) (h : Aligned (F := F) g seen tr) (i : ι) (H : G) :
    Aligned (F := F) g (seen ++ [(.inr (.inl tr.1.length), H)])
      (tr.1 ++ [(i, H)], tr.2) := by
  intro out
  rw [AlgebraicGroupModel.Representation.eval_append, h out]
  simp only [materialize_eq_weightedReplies, weightedReplies, List.mapIdx_append_one,
    List.sum_append, AlgebraicGroupModel.Representation.eval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Output.toAlgebraic]
  ac_rfl

theorem aligned_sign (g : G) (seen : AlgebraicGroupModel.Transcript Token G)
    (tr : Transcript ι M G) (h : Aligned (F := F) g seen tr) (m : M) (s : G) :
    Aligned (F := F) g (seen ++ [(.inr (.inr tr.2.length), s)])
      (tr.1, tr.2 ++ [(m, s)]) := by
  intro out
  rw [AlgebraicGroupModel.Representation.eval_append, h out]
  simp only [materialize_eq_weightedReplies, weightedReplies, List.mapIdx_append_one,
    List.sum_append, AlgebraicGroupModel.Representation.eval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Output.toAlgebraic]
  ac_rfl

-- This is the final message reconstructed from the grouped-transcript proof view.
def observe (g : G) (z : Output F M × Transcript ι M G) :
    -- Its ordinary data and group lists have exactly the types used by the source experiment.
    Interaction.Message (Result F M) (Group G G₂) :=
  -- Derive signed messages from the transcript and the signature from the algebraic coefficients.
  ⟨some (z.1, z.2.2.map Prod.fst), groupLists [materialize g z.1 z.2] []⟩

omit [AddMonoid G₂] [SMul F G₂] in
/-- Exact computation equality, including adaptive query ordering and private random choices. -/
theorem compile_run {N : Type → Type} [Monad N] [LawfulMonad N]
    (random : QueryImpl unifSpec N) (hash : ι → N G) (sign : M → N G)
    (program : OracleComp (advSpec ι M G) (Output F M))
    (g : G) (seen : AlgebraicGroupModel.Transcript Token G) (tr : Transcript ι M G)
    (h : Aligned (F := F) g seen tr) (basis : Interaction.Groups (Group G G₂)) :
    (fun z => z.1.value) <$>
        (simulateQ (fun q => StateT.mk fun inputs => do
          let reply ← impl random hash sign q.value
          pure (reply, Interaction.extend inputs reply.groups)) (compile program seen tr)).run basis =
      observe g <$> (simulateQ (handler random hash sign) program).run tr := by
  induction program using OracleComp.recOn generalizing seen tr basis with
  | pure out =>
      change (fun z => z.1.value) <$> pure (finish out tr seen, basis) =
        observe g <$> pure (out, tr)
      simp only [map_pure, finish, AlgebraicGroupModel.Output.explain_value, observe, h out]
  | queryBind q next ih =>
      rcases q with ((n | i) | m)
      all_goals
        change (fun z : Interaction.Explained F (Result F M) (Group G G₂) ×
            Interaction.Groups (Group G G₂) => z.1.value) <$>
          (simulateQ (fun q : Interaction.Explained F (Query ι M) (Group G G₂) =>
            StateT.mk fun inputs => do
              let reply ← impl random hash sign q.value
              pure (reply, Interaction.extend inputs reply.groups)) (OracleComp.queryBind _ _)).run basis =
            observe g <$> (simulateQ (handler random hash sign)
              ((liftM ((advSpec ι M G).query _) : OracleComp (advSpec ι M G) _) >>= next)).run tr
        simp only [simulateQ, OracleComp.queryBind, PFunctor.FreeM.liftM,
          StateT.run_bind, StateT.run_mk]
        simp only [impl, request, StateT.run, StateT.mk,
          bind_assoc, pure_bind, map_bind]
      · change _ = observe g <$> ((random n >>= fun u => pure (u, tr)) >>=
          fun z => (simulateQ (handler random hash sign) (next z.1)).run z.2)
        simp only [bind_assoc, pure_bind, map_bind]
        exact bind_congr fun u => ih u seen tr h _
      · change _ = observe g <$> ((hash i >>= fun H => pure (H, (tr.1 ++ [(i, H)], tr.2))) >>=
          fun z => (simulateQ (handler random hash sign) (next z.1)).run z.2)
        simp only [bind_assoc, pure_bind, map_bind]
        exact bind_congr fun H => ih H _ _ (aligned_hash g seen tr h i H) _
      · change _ = observe g <$> ((sign m >>= fun s => pure (s, (tr.1, tr.2 ++ [(m, s)]))) >>=
          fun z => (simulateQ (handler random hash sign) (next z.1)).run z.2)
        simp only [bind_assoc, pure_bind, map_bind]
        exact bind_congr fun s => ih s _ _ (aligned_sign g seen tr h m s) _

end Interactive

/-- Compile a signature adversary with its public key in the tracked verification group. -/
-- This is the boundary from the signature-specific interface to the generic AGM library.
def Adversary.toInteractive {F ι M G₁ G₂ : Type}
    -- Require just the operations needed to construct and explain group outputs.
    [Zero F] [AddCommMonoid G₁] [SMul F G₁] [AddMonoid G₂] [SMul F G₂]
    -- A itself receives a public key, makes typed oracle requests, and returns coefficient lists.
    (A : Adversary F ι M G₁ G₂) :
    -- The generic adversary has two group labels and no ordinary initial payload beyond Unit.
    AlgebraicGroupModel.Interaction.Adversary F (Interactive.Group G₁ G₂) Unit
      -- Fix its allowed query data, dependent reply data, and final result data types.
      (Interactive.Query ι M) Interactive.Reply (Interactive.Result F M) where
  -- Check the game-chosen initial group's lists before exposing the public key to A.
  main input := match input.groups .signature, input.groups .verification with
    -- One generator and one key initialize the compiler; A sees pk, not a full public base table.
    | [g], [pk] => Interactive.compile (A.main pk) [(.inl (), g)] ([], [])
    -- Other initial shapes reject instead of supplying missing or extra input points.
    | _, _ => pure Interactive.reject
  -- Certify explanations for every initial input and every possible typed oracle-reply path.
  algebraic input := by
    rcases input with ⟨_, groups⟩
    obtain ⟨xs, ks, rfl⟩ : ∃ xs : List G₁, ∃ ks : List G₂,
        groups = Interactive.groupLists xs ks :=
      ⟨groups .signature, groups .verification, by funext s; cases s <;> rfl⟩
    cases xs with
    | nil => exact fun _ => List.Forall₂.nil
    | cons g rest =>
        cases rest with
        | cons _ _ => exact fun _ => List.Forall₂.nil
        | nil =>
            cases ks with
            | nil => exact fun _ => List.Forall₂.nil
            | cons pk rest =>
                cases rest with
                | nil => exact Interactive.compile_algebraic _ _ _ _
                | cons _ _ => exact fun _ => List.Forall₂.nil

theorem Adversary.toInteractive_run {F ι M G₁ G₂ : Type}
    [Zero F] [AddCommMonoid G₁] [SMul F G₁] [AddMonoid G₂] [SMul F G₂]
    {N : Type → Type} [Monad N] [LawfulMonad N] (A : Adversary F ι M G₁ G₂)
    (random : QueryImpl unifSpec N) (hash : ι → N G₁) (sign : M → N G₁)
    (g₁ : G₁) (pk : G₂) :
    (fun z => z.1.value) <$>
        A.toInteractive.run (Interactive.impl random hash sign) (Interactive.initialInput g₁ pk) =
      Interactive.observe g₁ <$>
        (simulateQ (handler random hash sign) (A.main pk)).run ([], []) :=
  Interactive.compile_run random hash sign (A.main pk) g₁ _ _
    (Interactive.aligned_initial g₁) (Interactive.groupLists [g₁] [pk])

end Model.LazyAGM
