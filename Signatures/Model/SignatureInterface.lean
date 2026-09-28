import Signatures.Model.CoCDH
import Signatures.AlgebraicGroupModel.Spec.BilinearGroup
import Signatures.AlgebraicGroupModel.Spec.Representation
import Mathlib.Data.List.Indexes
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation


/-! Signature-specific oracle messages and algebraic output format. -/

open OracleComp OracleSpec

namespace Model.LazyAGM

-- The ambient interface has private uniform randomness on the left and base queries on the right.
abbrev baseSpec (ι G : Type) := unifSpec + (ι →ₒ G)
-- A additionally gets signing: requests are ((randomness | base index) | signed message).
abbrev advSpec (ι M G : Type) := baseSpec ι G + (M →ₒ G)
-- Keep ordered explicit base replies and signing replies separately, preserving repetitions.
abbrev Transcript (ι M G : Type) := List (ι × G) × List (M × G)

/-- Coefficient at a received token; absent entries contribute zero. -/
-- Read the coefficient assigned to the nth actual reply, without demanding equal list lengths.
def tokenCoeff {F : Type} [Zero F] (coeff : List F) (n : Nat) : F :=
  -- A missing entry contributes zero; extra entries are unused unless a matching reply exists.
  (coeff[n]?).getD 0

-- This is the only final-output shape exposed to the signature-specific adversary.
structure Output (F M : Type) where
  -- The proposed fresh message; M also includes a topic or slot for OOPS and Proximity.
  mstar : M
  -- The coefficient multiplying the explicitly supplied signature-group generator.
  β : F
  -- One positional list for coefficients on the explicit base-query replies.
  γ : List F
  -- One positional list for coefficients on the explicit signing-query replies.
  ξ : List F

-- Fix the scalar, base-index, message, signature-group, and verification-key types of the game.
structure Adversary (F ι M G₁ G₂ : Type) where
  -- Given pk, A can adaptively use only advSpec and must finish with coefficients, not a raw point.
  main (pk : G₂) : OracleComp (advSpec ι M G₁) (Output F M)

variable {F ι M G₁ G₂ : Type}

/-- Signature-specific tokens: the generator, explicit base replies, and signing replies. -/
-- Unit names the single generator; the two Nat alternatives index hash and signing replies.
abbrev Token := Unit ⊕ (Nat ⊕ Nat)

/-- Interpret the signature output format as a token-indexed algebraic output. -/
-- Adapt the signature-specific coefficient lists to the token representation helper.
def Output.toAlgebraic [Zero F] (out : Output F M) :
    -- Its ordinary payload is M; its representation is a scalar coefficient for each Token.
    AlgebraicGroupModel.Output F Token M where
  -- Keep the candidate message as data; this field is not a signature point.
  value := out.mstar
  -- Token labels determine which coefficient list is read; the message is not used as a point.
  coefficients
    -- The generator's token uses the single generator coefficient.
    | .inl _ => out.β
    -- The nth explicit base reply uses the nth hash coefficient, defaulting to zero.
    | .inr (.inl n) => tokenCoeff out.γ n
    -- The nth explicit signing reply uses the nth signing coefficient, defaulting to zero.
    | .inr (.inr n) => tokenCoeff out.ξ n

/-- Supply only the generator and replies actually delivered to the signature adversary. -/
-- Build the proof-side grouped basis from a generator and actual visible replies.
def Transcript.inputs (g₁ : G₁) (tr : Transcript ι M G₁) :
    -- Each entry pairs a stable token with its G1 point.
    AlgebraicGroupModel.Transcript Token G₁ :=
  -- First supply the generator under the distinguished token.
  [(.inl (), g₁)] ++
    -- Number explicit base replies within the hash transcript.
    tr.1.mapIdx (fun n p => (.inr (.inl n), p.2)) ++
    -- Number explicit signing replies within the signing transcript; internal lookups are absent.
    tr.2.mapIdx (fun n p => (.inr (.inr n), p.2))

/-- A finite linear combination of oracle bases, evaluated through the shared cache. -/
-- Evaluating weighted bases needs addition, zero, and scalar multiplication on G1.
def evalTerms [AddCommMonoid G₁] [SMul F G₁] :
    -- Consume a finite weighted-index list and produce a point through the ambient oracle.
    List (ι × F) → OracleComp (baseSpec ι G₁) G₁
  -- An empty sum is the group identity and needs no query.
  | [] => pure 0
  -- For each term, look up its base and add its weighted contribution.
  | (i, c) :: rest => do
      -- Use the base branch of the shared oracle, even if this is an internal signer lookup.
      let H ← (liftM ((baseSpec ι G₁).query (.inr i)) : OracleComp (baseSpec ι G₁) G₁)
      -- Evaluate the remaining terms against that same oracle state.
      let R ← evalTerms rest
      -- Combine this scalar multiple with the rest of the sum.
      pure (c • H + R)

/-- Record only the base and signature replies actually delivered to the adversary. -/
-- This proof-side handler works in any chosen effect monad N and receives a randomness handler.
def handler {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N)
    -- The caller supplies base and signing behavior separately from the request types.
    (hash : ι → N G₁) (sign : M → N G₁) :
    -- Interpret advSpec while carrying the two lists of replies actually delivered to A.
    QueryImpl (advSpec ι M G₁) (StateT (Transcript ι M G₁) N) :=
  -- Dispatch on the tagged request; subsequent requests can depend on the returned reply.
  fun
  -- Left-left is private uniform randomness, with request parameter n.
  | .inl (.inl n) => StateT.mk fun tr => do
      -- Obtain a value of Fin (n + 1) from the supplied randomness implementation.
      let u ← random n
      -- Deliver the random value without adding a group point to either transcript.
      pure (u, tr)
  -- Left-right is an explicit request for the base at index i.
  | .inl (.inr i) => StateT.mk fun tr => do
      -- Obtain the base value; persistent caching is supplied by the surrounding game.
      let H ← hash i
      -- Record this occurrence even when i was queried before and H was already cached.
      pure (H, (tr.1 ++ [(i, H)], tr.2))
  -- Right is a signing request for message m.
  | .inr m => StateT.mk fun tr => do
      -- The signer may perform internal base lookups, which do not pass through this handler.
      let σ ← sign m
      -- Record only the message and signature delivered to A, not the signer's internal bases.
      pure (σ, (tr.1, tr.2 ++ [(m, σ)]))

-- Sum scalar-weighted received points; the transcript's associated data D does not affect the sum.
def weightedReplies [Zero F] [AddCommMonoid G₁] [SMul F G₁] {D : Type}
    -- Match coefficients to actual reply positions, not to distinct messages or point values.
    (coeff : List F) (tr : List (D × G₁)) : G₁ :=
  -- Missing coefficients are zero; only points present in tr contribute.
  (tr.mapIdx fun n p => tokenCoeff coeff n • p.2).sum

-- Materialization turns the algebraic recipe into the candidate G1 signature.
def materialize [Zero F] [AddCommMonoid G₁] [SMul F G₁]
    -- The available basis is just g1 and the recorded explicit replies.
    (g₁ : G₁) (out : Output F M) (tr : Transcript ι M G₁) : G₁ :=
  -- Evaluate the token representation and select its point, discarding the unchanged data field.
  (out.toAlgebraic.materialize (tr.inputs g₁)).2

/-- The token representation interpreter preserves the original signature expression exactly. -/
theorem materialize_eq_weightedReplies [Zero F] [AddCommMonoid G₁] [SMul F G₁]
    (g₁ : G₁) (out : Output F M) (tr : Transcript ι M G₁) :
    materialize g₁ out tr =
      out.β • g₁ + weightedReplies out.γ tr.1 + weightedReplies out.ξ tr.2 := by
  simp [materialize, AlgebraicGroupModel.Output.materialize,
    AlgebraicGroupModel.Representation.eval, Transcript.inputs, Output.toAlgebraic,
    weightedReplies, List.mapIdx_eq_ofFn, List.map_ofFn, Function.comp_def,
    List.sum_append, add_assoc]

end Model.LazyAGM
