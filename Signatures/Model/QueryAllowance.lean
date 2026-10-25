/-! The attacker's oracle-call allowance. An attacker promises at most `random`
requests for coins, `hash` hash queries and `sign` signing queries; its local
computation is bounded separately by the execution model. The reduction is a
fixed program, so it sizes its oracle tables, replay tapes and transcript
capacities from this allowance before the attacker runs, charges its own work per
served call, and states its loss factors (`coronFactor sign`, `sign * (sign + hash) / |F|`,
`(hash + 1)` fork points) in these counts. The asymptotic statements ask each count
to be polynomial in the security parameter. -/

namespace Model

structure QueryAllowance where
  random : Nat
  hash : Nat
  sign : Nat

/-- Every call the reduction may have to serve. -/
def QueryAllowance.total (q : QueryAllowance) : Nat := q.random + q.hash + q.sign

end Model
