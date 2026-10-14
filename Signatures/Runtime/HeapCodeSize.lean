import Signatures.Runtime.HeapPackage

/-! Static footprint of executable packages. Counts every branch, stored
literal, list spine, circuit address, layout, and sampler parameter, whether
executed or not. Cells use a fixed finite alphabet for tags and bits; natural
metadata uses a length-delimited binary representation. This is a separate
resource from online execution, not a claim about compiler running time. -/

namespace Signatures.Runtime

namespace CodeSize

/-- Unary bit-length delimiter followed by binary payload. -/
def natural (n : Nat) : Nat := 2*n.size+1

def atom : CryptoAtom → Nat
  | .fin n => natural n+1
  | _ => 1

def ty : Ty CryptoAtom → Nat
  | .atom a => atom a+1
  | .unit | .bool | .nat => 1
  | .pair a b => ty a+ty b+1
  | .list a => ty a+1

end CodeSize

def BitRejection.Code.cells (code : BitRejection.Code) : Nat :=
  code.width.length + code.attempts.length +
    (match code.limit with | none => 1 | some bits => 2*bits.length+2) + 3

def PaddedSampling.Code.cells (code : PaddedSampling.Code) : Nat :=
  code.sampler.cells + code.padding.length + 2

def HeapExpression.Code.cells : HeapExpression.Code → Nat
  | .var slot => slot.length+2
  | .word bits => 2*bits.length+2
  | .nil => 1
  | .pair left right | .cons left right | .letE left right => left.cells+right.cells+1
  | .project _ arg => arg.cells+2
  | .branch cond yes no | .fold cond yes no => cond.cells+yes.cells+no.cells+1
  | @HeapExpression.Code.primitive a _ code arg => CodeSize.ty a+code.cells+arg.cells+1

def HeapProgram.Code.cells {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    (fee : {a b : Ty CryptoAtom} → Cmd a b → Nat) : HeapProgram.Code Cmd → Nat
  | .ret value => value.cells+1
  | @HeapProgram.Code.query _ a b cmd arg =>
      CodeSize.ty a+CodeSize.ty b+fee cmd+arg.cells+1
  | .bind first body => first.cells fee+body.cells fee+1
  | .branch cond yes no => cond.cells+yes.cells fee+no.cells fee+1
  | .loop count init body => count.cells+init.cells+body.cells fee+1
  | .call body args => body.cells fee+(args.map HeapExpression.Code.cells).sum+args.length+2

def HeapMachine.Instruction.cells {storage a b : Ty CryptoAtom} : HeapMachine.Instruction storage a b → Nat
  | .scalar code => code.cells+1
  | .uniform n code => CodeSize.natural n+code.cells+1
  | .read | .write => 1

def HeapMachine.Code.cells (code : HeapMachine.Code) : Nat :=
  CodeSize.ty code.storage+code.init.cells+code.body.cells HeapMachine.Instruction.cells+1

def HeapMachine.Package.cells (pack : HeapMachine.Package) : Nat :=
  (pack.data.map HeapExpression.Code.cells).sum+pack.data.length+pack.code.cells+2

end Signatures.Runtime
