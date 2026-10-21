import Signatures.Runtime.Caliper.SchnorrROMFullSecurity
import Signatures.Schnorr.QueryAllowance

/-! Fixed Caliper components and local attacker allowances for ordinary-ROM
Schnorr. The handler, extractor primitives, caller shape and allowances are
fixed before the attacker; the attacker supplies local routines over that shape,
its source correspondence and its own query bounds. The complete replaying
solver and every resource budget are constructed from these components. -/
namespace Schnorr.CaliperROM
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

variable (F G M : Type) [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
    (queries : QueryAllowance) (generator : G)

structure Parameters where
  wordBits : Nat
  config : SchnorrROM.Signing.Enumerated.Configuration wordBits M F G
  operations : SchnorrROM.Handler.Operations config
  handlerBudget : SchnorrROM.Handler.Budget config operations
  arithmetic : SchnorrROM.ReplayFork.Extract.Arithmetic config
  arithmeticBudget : SchnorrROM.ReplayFork.Extract.Arithmetic.Budget config arithmetic
  shape : SchnorrROM.Full.Shape config
  limits : SchnorrROM.Full.Limits
  indexFits : queries.hash + 1 < 2 ^ wordBits
  tables : queries.total + 1 ≤ config.capacityPred + 1
  tapes : 4 * queries.total + 3 ≤ config.sampler.capacity
  handlerRoom : SchnorrROM.Handler.nameBudget config operations ≤ limits.names
  slotsRoom : operations.slots + 4 < 2 ^ wordBits
  generatorValid : config.point.valid generator

variable {F G M queries generator} (P : Parameters F G M queries generator)

/-- Arbitrary local Caliper code over the fixed caller shape, with its own
resource and query allowances and a source correspondence for its machine.
No algebraicity, arithmetic-language certificate or fixed query schedule is required. -/
structure UnrestrictedAdversary [SampleableType F] [SampleableType G] where
  source : ROM.Adversary (F := F) (M := M) generator
  caller : SchnorrROM.Full.Caller P.config P.shape
  bounds : caller.Bounds P.config P.shape P.limits
  correspondence : SchnorrROM.Pass.Caller.Source P.config (caller.toPass P.config P.shape) queries.total
  source_eq : ∀ pk : P.config.point.Value,
    Subtype.val <$> correspondence.program (correspondence.inputView pk) = source.main pk.val
  randomQueries : ∀ pk, IsQueryBoundP (source.main pk) (· matches .inl (.inl _)) queries.random
  signingQueries : ∀ pk, IsQueryBoundP (source.main pk) (· matches .inr _) queries.sign
  hashQueries : ∀ pk, IsQueryBoundP (source.main pk) (· matches .inl (.inr _)) queries.hash

namespace Parameters
/-- Derived cost of setup, both attacker executions, lazy hashing/signing,
private-tape replay, selection, extraction and uniform fallback. -/
def solverTime : Nat := SchnorrROM.Full.timeBudget P.config P.shape P.limits P.operations P.handlerBudget
  queries.hash P.indexFits P.arithmetic P.arithmeticBudget queries.total
def solverCode : Nat := SchnorrROM.Full.codeBudget P.config P.shape P.limits P.operations P.handlerBudget
  queries.hash P.indexFits P.arithmetic P.arithmeticBudget queries.total
def solverMemory : Nat := SchnorrROM.Full.memoryBudget P.config P.shape P.limits P.operations P.handlerBudget
  queries.hash P.indexFits P.arithmetic P.arithmeticBudget queries.total
def within (time : Nat) (solver : DiffieHellman.DLogAdversary F G) : Prop :=
  cyclicDLogWithin (SchnorrROMTape.Fresh.port P.config.handler.sampler.tape) (SchnorrROM.Pass.Initialization.points P.config)
    P.config.handler.sampler.tape.scalar generator P.solverCode P.solverMemory time solver
noncomputable def dlogBound [SampleableType F] (time : Nat) : ENNReal :=
  cyclicDLogSuccessBound (SchnorrROMTape.Fresh.port P.config.handler.sampler.tape) (SchnorrROM.Pass.Initialization.points P.config)
    P.config.handler.sampler.tape.scalar generator P.solverCode P.solverMemory time
end Parameters

end Schnorr.CaliperROM
