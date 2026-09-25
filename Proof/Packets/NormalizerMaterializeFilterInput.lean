import Proof.Packets.NormalizerMaterializeData

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

theorem filter_input_heads (B : Nat) (raw : List (List Bool)) :
    (ParityFilter.readyInput B (candidates raw) [] [] [] [] [] (records raw) 0
      (probeCap B) (scanCap B raw.length) (filterCap B raw.length) (countCap B raw.length) false false).heads=
      ![0,0,0,0,0,1,0,0,1,1,0,0] := by
  funext i; fin_cases i <;>
    simp [ParityFilter.readyInput,CursorReady.input,ZeroPadding.config,Rewind.recording,Rewind.config,
      ParityFilter.loopCfg,ParityFilter.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases]

theorem filter_input_tapes (B : Nat) (raw : List (List Bool)) :
    (ParityFilter.readyInput B (candidates raw) [] [] [] [] [] (records raw) 0
      (probeCap B) (scanCap B raw.length) (filterCap B raw.length) (countCap B raw.length) false false).tapes=
      ![ParityFilter.candidateStream (candidates raw),SuffixScan.stream (records raw),[false],[false],
        List.replicate (probeCap B) false,CompareMachine.word raw.length,List.replicate (scanCap B raw.length) false,
        [],CompareMachine.word 0,CompareMachine.word (candidates raw).length,
        List.replicate (filterCap B raw.length) false,List.replicate (countCap B raw.length) false] := by
  funext i; fin_cases i <;>
    simp [ParityFilter.readyInput,CursorReady.input,ZeroPadding.config,Rewind.recording,Rewind.config,
      Rewind.Workspace.capacities,ZeroPadding.pad,
      ParityFilter.loopCfg,ParityFilter.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases,
      records,PhysicalParityScan.stream,SuffixScan.stream]

theorem probes_fit (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∀ bits∈candidates raw,∀ row∈records raw,
      PhysicalParityProbe.budget (PhysicalParityScan.supportRecord bits) row≤probeCap B := by
  intro bits hb row hr
  obtain ⟨r,hrmem,rfl⟩ := List.mem_map.mp hr
  simp [PhysicalParityProbe.budget,ClauseEquality.budget,PhysicalParityScan.supportRecord,
    candidate_width B raw hw bits hb,hw r hrmem,probeCap]

theorem filter_fits (B : Nat) (raw : List (List Bool)) :
    ParityFilter.filterBudget B (records raw).length (candidates raw).length (probeCap B)≤filterCap B raw.length := by
  have hn := (List.dedup_sublist raw).length_le
  simp only [records,List.length_map,candidates,List.length_reverse,ParityFilter.filterBudget,filterCap]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _

end PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
