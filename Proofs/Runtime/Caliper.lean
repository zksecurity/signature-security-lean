import Proofs.Runtime.Caliper.Program
import Proofs.Runtime.Caliper.Encoding
import Proofs.Runtime.Caliper.Crypto
import Proofs.Runtime.Caliper.Routine
import Proofs.Runtime.Caliper.Hoare
import Proofs.Runtime.Caliper.Realizer
import Proofs.Runtime.Caliper.Resources
import Proofs.Runtime.Caliper.Words
import Proofs.Runtime.Caliper.Memory
import Proofs.Runtime.Caliper.Layouts
import Proofs.Runtime.Caliper.Slice
import Proofs.Runtime.Caliper.Wiring
import Proofs.Runtime.Caliper.Replay
import Proofs.Runtime.Caliper.Mailbox
import Proofs.Runtime.Caliper.Assembly
import Proofs.Runtime.Caliper.Construct
import Proofs.Runtime.Caliper.Retain
import Proofs.Runtime.Caliper.Branch
import Proofs.Runtime.Caliper.Loop
import Proofs.Runtime.Caliper.BoundedSource
import Proofs.Runtime.Caliper.OracleCall
import Proofs.Runtime.Caliper.SourceAcceptance
import Proofs.Runtime.Caliper.InteractiveDescription
import Proofs.Runtime.Caliper.SourceLists
import Proofs.Runtime.Caliper.SourceFold
import Proofs.Runtime.Caliper.ScalarBounds
import Proofs.Runtime.Caliper.SourceStructure
import Proofs.Runtime.Caliper.ExpressionCompilation
import Proofs.Runtime.Caliper.StagedFoldBounds
import Proofs.Runtime.Caliper.StructuralBudgets
import Proofs.Runtime.Caliper.ExpressionBounds
import Proofs.Runtime.Caliper.ExpressionMemory
import Proofs.Runtime.Caliper.ImplementationMemory
import Proofs.Runtime.Caliper.LookupAcceptance
import Proofs.Runtime.Caliper.CacheBounds
import Proofs.Runtime.Caliper.CacheReadMemory
import Proofs.Runtime.Caliper.CacheReadOracle
import Proofs.Runtime.Caliper.SourcePrefix
import Proofs.Runtime.Caliper.PairSamplingMemory
import Proofs.Runtime.Caliper.UniformQuery
import Proofs.Runtime.Caliper.UniformSamplingBounds
import Proofs.Runtime.Caliper.TagBounds
import Proofs.Runtime.Caliper.InteractiveMemory
import Proofs.Runtime.Caliper.InteractiveInvariantBounds
import Proofs.Runtime.Caliper.SumContextBounds
import Proofs.Runtime.Caliper.SumContextMerge
import Proofs.Runtime.Caliper.CallerStepBounds
import Proofs.Runtime.Caliper.CallerExecution
import Proofs.Runtime.Caliper.CallerPresentation
import Proofs.Runtime.Caliper.SynchronizesObservations

/-! Caliper execution and separately certified encoded cryptographic routines.
This module is independent of the signature games. It supplies a concrete local
quantitative backend, bounded layouts, construction, saved-state composition,
branching and bounded local loops, bounded-source refinement, a proved word I/O
adapter for typed oracle calls, plus copying and recording/replay primitives.
Interactive compilation refines all constructors of the existing source
language, including bounded loops and input-counted iteration, retaining execution
profiles and deriving uniform time/additional-buffer bounds from primitive
implementation budgets. The memory account includes initial storage, code,
registers, descriptors and every intermediate buffer state. Checked emission
validates generated names and proves word-sized capacities throughout execution.
Bounded list construction, case analysis and capacity growth use actual copying,
stored-header arithmetic and branch instructions, with linear time/code bounds.
List folds execute their compiled bodies with retained tails and environments;
their polynomial time and code bounds include every copy and stored branch.
Bounded natural arithmetic, comparisons, Boolean selection and finite-index
conversions execute actual instructions with source-correct results. Shared-input
pairing includes copies and retained state in its time and stored-code bounds.
Checked compilation covers the original expression constructors on certified
bounded layouts, rejecting generated scratch names outside the word domain.
Folds support iteration-dependent accumulator domains and storage widths;
early returns execute and charge their conversion to the final layout.
Complete staged folds have uniform polynomial time/code budgets derived from
the individual body/conversion budgets and layout widths. Source implementations
also have compositional bounds for projections, pairing and list construction.
The complete original-expression compiler derives uniform time/code budgets
structurally from primitive and final-conversion budgets, including fold input
construction. Its budget-certified result erases to the original compiler result.
Actual execution time and additional buffer usage satisfy the derived bounds.
Dense register/descriptor reservations are also derived from primitive name
limits and generated code size. Complete expression memory budgets include all
initial capacity and every intermediate and final state of actual execution.
Encoded equality executes a linear word scan, including zero-word layouts.
The original association-list lookup has a constructed compilation certificate
and concrete polynomial time/code budgets in stored-entry capacity and widths.
Structured-key lookup is normalized to this code using a proved source equality
test, retaining its result and complete resource bounds.
Encoded lookup compiles for every admitted layout, with at most seven buffer
slots. Its total implementation is obtained from the existing checked compiler.
The original cache-programming expression now has a total fixed-capacity
implementation on the proved hit-or-room domain, including full-table hits.
Its time/code bounds add linear overhead to lookup; at most eight buffer slots
are used, with complete intermediate-state memory accounting. Branch-local
invariants come from the executed test, and removing padding requires paid copies.
Effectful cache reads also implement the original source expression. Hits make
no draw call; misses retain their frame across an actual primitive draw, then
insert the returned value. Time/code and complete memory bounds include this
saved-state copying and the primitive's own resources. Draw semantics and its
implementation remain explicit primitive contracts, including sampling laws.
The same code implements the shared association-list oracle. Adaptive source
prefixes retain query allowances and state-growth bounds along supported paths.
Independent pair sampling is derived from two certified component samplers.
Saved-state copying and output permutation execute, with linear overhead and
complete memory bounds; the product sampling law follows from component laws.
Fixed-range uniform sampling is constructed through the word port, including
request preparation and reply copying, with constant local time/code/memory
bounds even when the range fills the word domain. The oracle remains ideal.
Interactive loops now carry decreasing reachable-domain invariants through
supported source answers, with time and complete memory bounds for the same run.
Generated caller steps preserve caller state across handlers and private stores
across local continuations. Their copying, padding and routing have linear
overhead bounds. Complete bounded controllers include charged initialization,
early return and observable cutoff, with time, stored-code and whole-memory bounds.
Their original OracleMachine bridge preserves the final private store and uses
ImplementsWithin to identify the source program and exclude cutoff. A canonical
machine and finite source can also be constructed from local transitions and
branchwise termination, including restricted source-input domains. Scheme-specific
packet layouts and the local source-correspondence proofs still need instantiation.
Scheme-specific primitive implementations, reachable-state invariants, replay
linking and signature model instantiation remain separate obligations.
-/
