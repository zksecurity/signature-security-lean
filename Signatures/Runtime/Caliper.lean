import Signatures.Runtime.Caliper.Program
import Signatures.Runtime.Caliper.Encoding
import Signatures.Runtime.Caliper.Crypto
import Signatures.Runtime.Caliper.Routine
import Signatures.Runtime.Caliper.Hoare
import Signatures.Runtime.Caliper.Realizer
import Signatures.Runtime.Caliper.Resources
import Signatures.Runtime.Caliper.Words
import Signatures.Runtime.Caliper.Memory
import Signatures.Runtime.Caliper.Layouts
import Signatures.Runtime.Caliper.Slice
import Signatures.Runtime.Caliper.Wiring
import Signatures.Runtime.Caliper.Replay
import Signatures.Runtime.Caliper.Mailbox
import Signatures.Runtime.Caliper.Assembly
import Signatures.Runtime.Caliper.Construct
import Signatures.Runtime.Caliper.Retain
import Signatures.Runtime.Caliper.Branch
import Signatures.Runtime.Caliper.Loop
import Signatures.Runtime.Caliper.BoundedSource
import Signatures.Runtime.Caliper.OracleCall
import Signatures.Runtime.Caliper.SourceAcceptance
import Signatures.Runtime.Caliper.InteractiveDescription
import Signatures.Runtime.Caliper.SourceLists
import Signatures.Runtime.Caliper.SourceFold
import Signatures.Runtime.Caliper.ScalarBounds
import Signatures.Runtime.Caliper.SourceStructure
import Signatures.Runtime.Caliper.ExpressionCompilation
import Signatures.Runtime.Caliper.StagedFoldBounds
import Signatures.Runtime.Caliper.StructuralBudgets
import Signatures.Runtime.Caliper.ExpressionBounds
import Signatures.Runtime.Caliper.ExpressionMemory
import Signatures.Runtime.Caliper.LookupBounds

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
Scheme-specific primitive implementations, reachable-state invariants, replay
linking and signature model instantiation remain separate obligations.
-/
