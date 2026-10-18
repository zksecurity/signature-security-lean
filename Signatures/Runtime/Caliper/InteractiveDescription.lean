import Signatures.Runtime.Caliper.InteractiveRetain

/-! Stored-code overhead of interactive control. Every inlined copy of a bounded
loop body and every save/project/rebuild instruction is included. The I/O envelope
is counted as well as its embedded Caliper descriptions.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat}

theorem WordIO.Code.descriptionWords_seq (left right : WordIO.Code w) :
    (WordIO.Code.seq left right).descriptionWords = left.descriptionWords + right.descriptionWords + 1 := by
  simp [WordIO.Code.descriptionWords, WordIO.Code.description]

theorem WordIO.Code.descriptionWords_branch (condition : Reg) (left right : WordIO.Code w) :
    (WordIO.Code.branch condition left right).descriptionWords = left.descriptionWords + right.descriptionWords + 2 := by
  simp [WordIO.Code.descriptionWords, WordIO.Code.description]

theorem WordIO.Code.descriptionWords_compute (code : Stmt w) :
    (WordIO.Code.compute code).descriptionWords = CaliperBackend.descriptionWords code + 1 := by
  simp [WordIO.Code.descriptionWords, WordIO.Code.description, CaliperBackend.descriptionWords]

namespace Interactive

variable {I : Type} {spec : OracleSpec I}

theorem dispatch_descriptionWords (port : Port w spec) (left right : Code w) (leftWords rightWords : Nat) :
    ((dispatch left right leftWords rightWords).lower port).descriptionWords =
      (left.lower port).descriptionWords + (right.lower port).descriptionWords + 26 * leftWords + 26 * rightWords + 40 := by
  simp only [dispatch, Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_branch,
    WordIO.Code.descriptionWords_compute, selectSlice_descriptionWords]
  simp only [descriptionWords, description, List.length_cons, List.length_nil]
  omega

theorem retain_descriptionWords_le (port : Port w spec) (body : Code w) (buffer inputWords outputWords savedWords : Nat) :
    ((retain body buffer inputWords outputWords savedWords).lower port).descriptionWords ≤
      (body.lower port).descriptionWords + 26 * inputWords + 26 * outputWords + 39 * savedWords + 41 := by
  have bound := Assembly.code_descriptionWords_le (Retain.restoreOperands (w := w) buffer outputWords savedWords)
  simp only [Retain.restoreOperands, List.length_append, Assembly.reads_length] at bound
  simp only [retain, Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute,
    Retain.prepare, Retain.finish, descriptionWords_seq, Retain.save_descriptionWords, selectSlice_descriptionWords]
  simp only [Retain.restoreOperands, descriptionWords, description, List.length_cons, List.length_nil] at *
  omega

theorem loop_descriptionWords (port : Port w spec) (body stop : Code w) (resultWords stateWords fuel : Nat) :
    ((loop body stop resultWords stateWords fuel).lower port).descriptionWords =
      (stop.lower port).descriptionWords + fuel *
        ((body.lower port).descriptionWords + 26 * resultWords + 26 * stateWords + 43) := by
  induction fuel with
  | zero => simp [loop]
  | succ fuel ih =>
    simp only [loop, Code.lower, WordIO.Code.descriptionWords_seq, dispatch_descriptionWords] at *
    rw [ih]
    simp only [WordIO.Code.descriptionWords_compute, descriptionWords, description,
      List.length_cons, List.length_nil]
    ring

end Interactive
end Signatures.Runtime.CaliperBackend
