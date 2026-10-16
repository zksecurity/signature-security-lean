import Signatures.Schnorr.LazyROMReduction

/-! The retained-private-tape Fiat--Shamir reduction, parameterized by its
protocol and signing simulator. The replay controller records encountered draws;
neither a private-family cover nor an eager seed allocation is an algorithm input. -/

open OracleComp OracleSpec

namespace FiatShamir.LazyTape

variable {Stmt Wit Commit PrvState Chal Resp M : Type} {rel : Stmt → Wit → Bool}
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)
  [DecidableEq M] [DecidableEq Commit] [DecidableEq Chal]
  [SampleableType Wit] [SampleableType Chal]

abbrev main (simulator : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.UnforgeableAdversary (inROM σ hr M)) (pk : Stmt) :=
  Fork.runTrace σ hr M (cmaToNmaAdv σ hr M simulator adv) pk

/-- Both executions share the retained private randomness, including draws
after the selected challenge. Fresh challenges after the fork remain independent. -/
def reduction (simulator : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.UnforgeableAdversary (inROM σ hr M)) (qH : Nat) :
    Stmt → ProbComp Wit := fun pk =>
  simulateQ Schnorr.LazyROM.sample
    (Schnorr.LazyROM.fork (main σ hr M simulator adv pk) qH
      (Fork.forkPoint Commit Chal Resp M qH) >>= nmaForkExtractBranch (M := M) σ)

end FiatShamir.LazyTape
