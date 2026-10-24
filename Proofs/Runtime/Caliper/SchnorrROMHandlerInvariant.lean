import Proofs.Runtime.Caliper.SchnorrROMHandlerMemory

/-! Reserve one managed/LIVE insertion and two saved cells per remaining call,
plus one LIVE insertion and one saved cell for final verification. This coarse
invariant works for all three branches and decreases after every supported reply. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def Reserved (remaining : Nat) (saved : Schnorr.ListROM.Shared.Store F G M) : Prop :=
  saved.1.2.1.length + remaining ≤ config.capacityPred + 1 ∧
    saved.1.2.2.length + (remaining + 1) ≤ config.capacityPred + 1 ∧
    saved.2.1.length + (3 * remaining + 1) ≤ config.sampler.capacity

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem reserved_empty (remaining : Nat) (generator publicKey : G)
    (tables : remaining + 1 ≤ config.capacityPred + 1) (tapes : 3 * remaining + 1 ≤ config.sampler.capacity) :
    Reserved config remaining (((generator, publicKey), [], []), [], []) := by
  simp only [Reserved, List.length_nil, Nat.zero_add]
  exact ⟨by omega, tables, tapes⟩

theorem reserved_ready (remaining : Nat) (value : Input config)
    (room : Reserved config (remaining + 1) (initialStore config value)) : ready config value := by
  rcases value with (value | value) | value
  · trivial
  · intro missing
    rcases room with ⟨_, live, tape⟩
    constructor
    · intro _
      change value.val.2.1.2.2.length ≤ config.capacityPred
      change value.val.2.1.2.2.length + (remaining + 1 + 1) ≤ _ at live
      omega
    · change value.val.2.2.1.length < config.sampler.capacity
      change value.val.2.2.1.length + (3 * (remaining + 1) + 1) ≤ _ at tape
      omega
  · change value.val.2.2.1.length + 3 ≤ config.sampler.capacity
    have tape := room.2.2
    change value.val.2.2.1.length + (3 * (remaining + 1) + 1) ≤ _ at tape
    omega

theorem reserved_final (key : M × G) (saved : Schnorr.ListROM.Shared.Store F G M)
    (room : Reserved config 0 saved) :
    FinalHash.admissible config (key, saved) ∧ saved.2.1.length < config.sampler.capacity := by
  rcases room with ⟨_, live, tape⟩
  constructor
  · intro _
    change saved.1.2.2.length ≤ config.capacityPred
    omega
  · omega

variable [SMul F G] [Sub G] (ops : Operations config)

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem sign_preserves_config (value : config.handler.input.Value) (answer : config.handler.output.Value)
    (reached : answer ∈ support (signSource config ops value)) : answer.val.2.1.1 = value.val.2.1.1 :=
  ops.signing.preserves_config value answer reached

theorem reserved_after (remaining : Nat) (value : Input config)
    (room : Reserved config (remaining + 1) (initialStore config value))
    (answer : Output config) (reached : answer ∈ support (source config ops value)) :
    (observed config answer).2.1.1 = (initialStore config value).1.1 ∧
      Reserved config remaining (observed config answer).2 := by
  have valid := reserved_ready config remaining value room
  rcases value with (value | value) | value
  · simp only [source, Sum.elim, randomSource, support_map, Set.mem_image] at reached
    obtain ⟨read, supported, rfl⟩ := reached
    have caches := Random.preserves_caches config value read supported
    have tape := (Random.tape_lengths config value read supported).1
    change read.val.2.1.1 = value.val.2.1.1 ∧ Reserved config remaining read.val.2
    refine ⟨congrArg Prod.fst caches, ?_⟩
    change Reserved config (remaining + 1) value.val.2 at room
    rcases room with ⟨managed, live, saved⟩
    unfold Reserved
    rw [caches]
    exact ⟨by omega, by omega, by omega⟩
  · simp only [source, Sum.elim, hashSource, support_map, Set.mem_image] at reached
    obtain ⟨read, supported, rfl⟩ := reached
    have tables := Hash.postcondition config value valid read supported
    have tape := (Hash.tape_lengths config value valid read supported).1
    change read.val.2.1.1 = value.val.2.1.1 ∧ Reserved config remaining read.val.2
    refine ⟨tables.1, ?_⟩
    change Reserved config (remaining + 1) value.val.2 at room
    rcases room with ⟨managed, live, saved⟩
    unfold Reserved
    exact ⟨by omega, by omega, by omega⟩
  · simp only [source, Sum.elim, signingSource, support_map, Set.mem_image] at reached
    obtain ⟨read, supported, rfl⟩ := reached
    have managed := ops.signing.managed_length value read supported
    have live := ops.signing.preserves_live value read supported
    have tape := (ops.signing.tape_lengths value valid read supported).1
    change read.val.2.1.1 = value.val.2.1.1 ∧ Reserved config remaining read.val.2
    refine ⟨sign_preserves_config config ops value read supported, ?_⟩
    change Reserved config (remaining + 1) value.val.2 at room
    rcases room with ⟨managedRoom, liveRoom, saved⟩
    unfold Reserved
    rw [live]
    exact ⟨by omega, by omega, by omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
