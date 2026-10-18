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
Scheme-specific primitive implementations, reachable-state invariants, replay
linking and signature model instantiation remain separate obligations.
-/
