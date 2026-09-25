import Proof.Packets.VectorTerminalZero
import Proof.Packets.VectorTerminalBank
import Proof.Packets.PacketsXNormalizedFiniteTransport

/-! The actual terminal initializer emits the exact frozen normalized vector,
including its positional order and the real mask-bank encoding. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorTerminal
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding NormalizedFiniteTransport

theorem terminal_vector (depth population : Nat) :
    List.ofFn (Normalized.structuralTerminalPolynomialVector depth population 0)=
      [[]]::List.replicate population [] := by
  rw [List.ofFn_succ]
  have rest : (fun i : Fin population=>Normalized.structuralTerminalPolynomialVector depth population 0 i.succ)=fun _=>[] := by
    funext i
    rw [terminal_zero]
    simp
  rw [rest,List.ofFn_const]
  rw [terminal_zero]
  rfl

theorem terminal_masks (C depth population : Nat) :
    (List.ofFn (Normalized.structuralTerminalPolynomialVector depth population 0)).map (List.map (maskNat C))=
      [List.replicate C false]::List.replicate population [] := by
  rw [terminal_vector]
  simp [maskNat]

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorTerminal
