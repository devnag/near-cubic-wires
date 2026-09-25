import Proof.Packets.TranscriptColumnProgram

/-! The column extractor on the resident S-bit workspace delivered by the
walk producer. Transcript and output words retain their exact lengths. -/
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


theorem empty_payload (R S : Nat) (hRS : R≤S) :
    ZeroPadding.pad S (PacketVector.payload R [])=List.replicate S false := by
  simp [PacketVector.payload,ZeroPadding.pad,←List.replicate_add,Nat.add_sub_of_le hRS]

theorem empty_count (R S : Nat) (hR : 1≤R) (hRS : R≤S) :
    ZeroPadding.pad S (PacketVector.count R [])=List.replicate S false := by
  have hlength : 1+(R-1)=R := by omega
  simp only [PacketVector.count,List.length_nil,CompareMachine.word,List.replicate_zero,List.append_nil,
    ZeroPadding.pad,List.length_singleton,List.length_append,List.length_replicate,hlength]
  rw [←List.replicate_one (a:=false),←List.replicate_add,←List.replicate_add]
  congr 1
  omega

def residentCapacities (S : Nat) : Fin 9 → Nat := ![S,0,S,S,S,S,0,0,S]
def residentTapes (R N T column S : Nat) (source payload count target : List Bool) : Fin 9 → List Bool :=
  ![ZeroPadding.pad S (UnaryTemplate.tape R),source,ZeroPadding.pad S payload,
    ZeroPadding.pad S count,ZeroPadding.pad S (CompareMachine.word N),List.replicate S false,
    target,CompareMachine.word T,ZeroPadding.pad S (CompareMachine.word column)]

theorem pad_resident_tapes (R N T column S : Nat) (source payload count target : List Bool) :
    (fun i=>ZeroPadding.pad (residentCapacities S i) (tapes R N T column source payload count target i))=
      residentTapes R N T column S source payload count target := by
  funext i;fin_cases i <;>
    simp [residentCapacities,tapes,residentTapes,A,Fin.addCases,ZeroPadding.pad_zero,ZeroPadding.pad]

theorem run_resident (R N T S : Nat) (rows : Nat → List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N) (target : List Bool)
    (old : PacketVector.Packet) (hfit : ∀i,∀P∈rows i,PacketVector.Fits R P)
    (hold : PacketVector.Fits R old) :
    Step program (budget R N T column.val) (heads 0 target.length)
      (residentTapes R N T column.val S (PacketTranscript.prefixBank R rows T)
        (PacketVector.payload R old) (PacketVector.count R old) target)
      (heads 0 target.length)
      (residentTapes R N T column.val S (PacketTranscript.prefixBank R rows T)
        (PacketVector.payload R (previous (rowPacket N rows hlen column) old T))
        (PacketVector.count R (previous (rowPacket N rows hlen column) old T))
        (target++PacketVector.bank R (List.ofFn (fun i : Fin T=>rowPacket N rows hlen column i.val)))) := by
  have actual := (run R N T rows hlen column target old hfit hold).pad (residentCapacities S)
  rw [pad_resident_tapes,pad_resident_tapes] at actual
  exact actual

end
end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
