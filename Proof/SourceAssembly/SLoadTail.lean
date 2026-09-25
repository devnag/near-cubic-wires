import Proof.SourceAssembly.SLoadSuffixFrame

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Tail
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-- The mask producer's `∀ B` is a singleton: `MaskProducer.correct` supplies a
compatible bank, and determinism of `Step` forces every other one to be it. -/
theorem mask_bank (mask : MaskProducer) (d : MaskData) :
    ∃ B0 : Fin (5 + mask.work) → List Bool,
      Step mask.machine (maskBudget mask.coefficient mask.degree d) (fun _ => 0)
        (d.input mask.work) (fun _ => 0) B0 ∧
      B0 ⟨4, by omega⟩ = d.word ∧
      ∀ B : Fin (5 + mask.work) → List Bool,
        Step mask.machine (maskBudget mask.coefficient mask.degree d) (fun _ => 0)
          (d.input mask.work) (fun _ => 0) B → B = B0 := by
  obtain ⟨B0, hrun, hword⟩ := mask.correct d
  exact ⟨B0, hrun, hword, fun B hB => (SuffixFrame.step_det hB hrun).2⟩

/-- The packet producer's `∀ B` is a singleton, for the same reason. No private
tape of the packet worker has to be cleared by the tail. -/
theorem packet_bank {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    (packet : PacketWriter selector a) (r : Request) :
    ∃ B0 : Fin packet.ordinary.program.tapeCount → List Bool,
      B0 packet.ordinary.program.outputTape = r.raw selector a ∧
      ∀ B : Fin packet.ordinary.program.tapeCount → List Bool,
        Step packet.ordinary.program.machine (packetBudget a packet.coefficient packet.degree r)
          (fun _ => 0) (packet.ordinary.program.inputTapes (r.input a)) (fun _ => 0) B →
        B = B0 := by
  obtain ⟨B0, hrun, hout⟩ := packet.run selector a r
  exact ⟨B0, hout, fun B hB => (SuffixFrame.step_det hB hrun).2⟩

/-- The tail program: the existing raw framer, docked at the packet's own
certified output slot, a retained unary length driver, a zero-backed
destination slot and a paid rewind log. Five states, four slots, no request
in scope. -/
noncomputable def machine {U : Nat} (src drv dst log : Fin U) : Machine U 5 :=
  MaskFrame.machine src drv dst log


end
end SLoad.Tail
