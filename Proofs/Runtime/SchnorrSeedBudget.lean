import Proofs.Runtime.ProgramQueries
import Proofs.Runtime.SchnorrTrace

/-! Source-derived query capacity for the typed Schnorr simulation. Private
scalar draws are kept as their own family, so the bound does not assume that a
scalar sampler consists of one raw uniform query. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr

/-- Families needed by each source capability. Simulator scalars retain a
separate tape from source uniform draws. -/
def seedLabels {randomBound a b} : Command randomBound a b → List ((Nat ⊕ Unit) ⊕ Unit)
  | .random n => [.inl (.inl n.val)]
  | .hash => [.inr ()]
  | .sign => [.inl (.inr ())]

def sourceFamilies {randomBound Γ a} (code : Program CryptoOp (Command randomBound) Γ a) :
    List ((Nat ⊕ Unit) ⊕ Unit) :=
  .inr () :: code.queryFamilies seedLabels

def sourceSeedCapacity (localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  (localTime + ∑ k, queries k) * 2 + 1

def sourceSeedBudget {randomBound Γ a} (code : Program CryptoOp (Command randomBound) Γ a)
    (localTime : Nat) (queries : Fin 3 → Nat) : (Nat ⊕ Unit) ⊕ Unit → Nat := by
  letI : BEq ((Nat ⊕ Unit) ⊕ Unit) := instBEqOfDecidableEq
  exact fun (i : (Nat ⊕ Unit) ⊕ Unit) =>
    if i ∈ sourceFamilies code then sourceSeedCapacity localTime queries else 0

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem taggedSign_totalBound (cost : PrimitiveCosts) (msg : M) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) :
    IsTotalQueryBound ((taggedSign.denote (arithmetic F G₁ G₂ K M cost)
      taggedSemantics (msg, ())).run ((g, pk), managed, live)) 2 := by
  rw [taggedSign_denote]
  simp [IsTotalQueryBound]

theorem taggedHash_totalBound (cost : PrimitiveCosts) (k : M × G₁) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) :
    IsTotalQueryBound ((taggedHash.denote (arithmetic F G₁ G₂ K M cost)
      taggedSemantics (k, ())).run ((g, pk), managed, live)) 1 := by
  rw [taggedHash_denote]
  cases cacheMap managed k <;> cases cacheMap live k <;>
    simp [IsTotalQueryBound, map_eq_bind_pure_comp]

theorem taggedFinalHash_totalBound (cost : PrimitiveCosts) (k : M × G₁) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) :
    IsTotalQueryBound ((taggedFinalHash.denote (arithmetic F G₁ G₂ K M cost)
      taggedSemantics (k, ())).run ((g, pk), managed, live)) 1 := by
  rw [taggedFinalHash_denote]
  cases cacheMap live k <;> simp [IsTotalQueryBound, map_eq_bind_pure_comp]

/-- At most two random-oracle-family requests implement a source command:
two private scalar draws for signing, one live draw for hashing, or one
private uniform draw. Cache accesses do not consume randomness. -/
theorem taggedRoutines_totalBound (cost : PrimitiveCosts) (randomBound : Nat)
    {a b} (cmd : Command randomBound a b) (arg : a.Value (cryptoBase F G₁ G₂ K M))
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M)) :
    IsTotalQueryBound (((taggedRoutines randomBound cmd).denote
      (arithmetic F G₁ G₂ K M cost) taggedSemantics (arg, ())).run state) 2 := by
  rcases state with ⟨⟨g, pk⟩, managed, live⟩
  cases cmd with
  | random n => simp [taggedRoutines, Program.denote, taggedSemantics,
      IsTotalQueryBound, StateT.run, map_eq_bind_pure_comp]
  | hash => exact (taggedHash_totalBound cost arg g pk managed live).mono (by omega)
  | sign => exact taggedSign_totalBound cost arg g pk managed live

/-- Capacity for every family, derived from the source certificate rather than
assumed for a completed fork. This includes the final live verifier query. -/
theorem macroPass_totalBound (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      code env localTime queries)
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M)) :
    IsTotalQueryBound ((macroPass cost randomBound code env).run state)
      ((localTime + ∑ k, queries k) * 2 + 1) := by
  have hbody := SourceBudget.denote_totalQueryBound (arithmetic F G₁ G₂ K M cost)
    (replies randomBound) kind (fun _ _ _ => trivial) code env localTime queries hsource
    (fun cmd arg => (taggedRoutines randomBound cmd).denote
      (arithmetic F G₁ G₂ K M cost) taggedSemantics (arg, ())) 2
    (taggedRoutines_totalBound cost randomBound) state
  rw [macroPass, StateT.run_bind, Program.inline_denote]
  refine isTotalQueryBound_bind hbody fun first => ?_
  simp only [bind_pure_comp, StateT.run_map]
  apply (isQueryBound_map_iff _ _ _ _ _).2
  exact taggedFinalHash_totalBound cost _ first.2.1.1 first.2.1.2 first.2.2.1 first.2.2.2

theorem taggedRoutines_families (cost : PrimitiveCosts) (randomBound : Nat)
    {a b} (cmd : Command randomBound a b) (arg : a.Value (cryptoBase F G₁ G₂ K M))
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M)) :
    AllQueriesSatisfy (((taggedRoutines randomBound cmd).denote
      (arithmetic F G₁ G₂ K M cost) taggedSemantics (arg, ())).run state)
      (fun i => i ∈ seedLabels cmd) := by
  rcases state with ⟨⟨g, pk⟩, managed, live⟩
  cases cmd with
  | random n => simp [taggedRoutines, Program.denote, taggedSemantics,
      AllQueriesSatisfy, StateT.run, map_eq_bind_pure_comp, seedLabels]
  | hash =>
      change AllQueriesSatisfy ((taggedHash.denote (arithmetic F G₁ G₂ K M cost)
        taggedSemantics (arg, ())).run ((g, pk), managed, live)) _
      rw [taggedHash_denote]
      cases cacheMap managed arg <;> cases cacheMap live arg <;>
        simp [AllQueriesSatisfy, map_eq_bind_pure_comp, seedLabels]
  | sign =>
      change AllQueriesSatisfy ((taggedSign.denote (arithmetic F G₁ G₂ K M cost)
        taggedSemantics (arg, ())).run ((g, pk), managed, live)) _
      rw [taggedSign_denote]
      simp [AllQueriesSatisfy, seedLabels]

theorem macroPass_families (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M)) :
    AllQueriesSatisfy ((macroPass cost randomBound code env).run state)
      (fun i => i ∈ sourceFamilies code) := by
  rw [macroPass, StateT.run_bind, Program.inline_denote]
  apply allQueriesSatisfy_bind
  · apply allQueriesSatisfy_of_imp _ (code.denote_queryFamilies
      (arithmetic F G₁ G₂ K M cost)
      (fun cmd arg => (taggedRoutines randomBound cmd).denote
        (arithmetic F G₁ G₂ K M cost) taggedSemantics (arg, ())) seedLabels
      (taggedRoutines_families cost randomBound) env state)
    intro i hi
    exact List.mem_cons_of_mem _ hi
  · intro first
    simp only [bind_pure_comp, StateT.run_map]
    apply (isQueryBound_map_iff _ _ _ _ _).2
    rcases first with ⟨forged, ⟨g, pk⟩, managed, live⟩
    rw [taggedFinalHash_denote]
    cases cacheMap live (forged.1, forged.2.1) <;>
      simp [map_eq_bind_pure_comp, sourceFamilies]

/-- Every required tape is finite, and its capacity follows from the original
source certificate. No seed is allocated for an arity absent from the code. -/
theorem macroPass_seedBudget (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      code env localTime queries)
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M)) :
    IsPerIndexQueryBound ((macroPass cost randomBound code env).run state)
      (sourceSeedBudget code localTime queries) :=
  perIndexBound_of_total_families _ _ _
    (macroPass_totalBound cost randomBound code env localTime queries hsource state)
    (macroPass_families cost randomBound code env state)

end Signatures.Runtime.Schnorr
