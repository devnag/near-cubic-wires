import Proof.Packets.TranscriptColumnPadded

/-! Reuse an already allocated column bank after it has been physically
cleared. The machine overwrites its exact T*2R-bit backing; no tape truncation
or fresh logical empty word is assumed between candidate visits. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def outputCapacity (K : Nat) : Fin 9 → Nat := fun i=>if i=6 then K else 0

theorem pad_output_tapes (R N T column S K : Nat) (source payload count target : List Bool) :
    (fun i=>ZeroPadding.pad (outputCapacity K i) (residentTapes R N T column S source payload count target i))=
      residentTapes R N T column S source payload count (ZeroPadding.pad K target) := by
  funext i;fin_cases i <;> simp [outputCapacity,residentTapes,ZeroPadding.pad_zero]

theorem run_reuse (R N T S : Nat) (rows : Nat → List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N)
    (old : PacketVector.Packet) (hfit : ∀i,∀P∈rows i,PacketVector.Fits R P)
    (hold : PacketVector.Fits R old) :
    Step program (budget R N T column.val) (heads 0 0)
      (residentTapes R N T column.val S (PacketTranscript.prefixBank R rows T)
        (PacketVector.payload R old) (PacketVector.count R old) (List.replicate (T*(2*R)) false))
      (heads 0 0)
      (residentTapes R N T column.val S (PacketTranscript.prefixBank R rows T)
        (PacketVector.payload R (previous (rowPacket N rows hlen column) old T))
        (PacketVector.count R (previous (rowPacket N rows hlen column) old T))
        (PacketVector.bank R (List.ofFn (fun i : Fin T=>rowPacket N rows hlen column i.val)))) := by
  let bank := PacketVector.bank R (List.ofFn (fun i : Fin T=>rowPacket N rows hlen column i.val))
  have bankLength : bank.length=T*(2*R) := by
    dsimp only [bank]
    rw [PacketVector.bank_length]
    · rw [List.length_ofFn];ring
    · intro P hP
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hP
      exact rowPacket_fits R N rows hlen column hfit i.val
  have zeros : ZeroPadding.pad (T*(2*R)) []=List.replicate (T*(2*R)) false := by
    simp [ZeroPadding.pad]
  have retained : ZeroPadding.pad (T*(2*R)) bank=bank := by simp [ZeroPadding.pad,bankLength]
  dsimp only [bank] at retained
  have actual := (run_resident R N T S rows hlen column [] old hfit hold).pad (outputCapacity (T*(2*R)))
  rw [pad_output_tapes,pad_output_tapes] at actual
  simpa only [List.length_nil,List.nil_append,zeros,retained] using actual

end
end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
