import Proofs.Runtime.Caliper.TokenRowsBounds
import Proofs.Runtime.TokenCoefficients

/-! The constructed word program implements the original AGM coefficient-row
expression on its represented input domain, with the same derived resources.
Zero is stored as its actual encoding, and chronological tokens retain both
message and group-output components. -/

namespace Signatures.Runtime.CaliperBackend.TokenRows
open Caliper BoundedSource

variable {w : Nat} {dataTy : Ty CryptoAtom} {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (layout : AttachRows.Layouts w (dataTy.Value (cryptoBase F G₁ G₂ K M) × G₁) F)
  (zeroValid : layout.value.valid 0) (cost : PrimitiveCosts)

def source : Implementation .unit (input layout) layout.output
    (fun value => ((AGM.tokenRows (dataTy := dataTy)).run (arithmetic F G₁ G₂ K M cost) (value.1, value.2, ())).value) :=
  (implementation layout ⟨0, zeroValid⟩).castFunction (by
    funext value
    exact (AGM.tokenRows_value (dataTy := dataTy) (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost value.1 value.2).symm)
theorem source_bounded : (source layout zeroValid cost).BoundedBy (timeBudget layout) (codeBudget layout) :=
  ⟨(bounded layout ⟨0, zeroValid⟩).time_le, (bounded layout ⟨0, zeroValid⟩).code_le⟩
theorem source_buffers : (source layout zeroValid cost).program.code.memBound ≤ 10 := buffers layout ⟨0, zeroValid⟩
theorem source_names (slots : Nat) : NamesAccounted (source layout zeroValid cost).program.code slots := names layout ⟨0, zeroValid⟩ slots

end Signatures.Runtime.CaliperBackend.TokenRows
