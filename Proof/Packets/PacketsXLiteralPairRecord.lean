import Proof.CaseAnalysis.RowsModeIndexBlock
import Proof.Packets.ReflectedLiteralCache

/-! The physical writer for one native singleton-pair cache record. It consumes
an actual framed binary code, writes all six framing/boundary cells, and appends
to an arbitrary retained prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairRecord
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.RepairOrdinary.SignedSortKey

noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine
    (Composition.machine (CloseoutRowsModeIndexBlock.mark true)
      CloseoutRowsModeIndexBlock.machine) (CloseoutRowsModeIndexBlock.mark false))
    (CloseoutRowsModeIndexBlock.mark false)) (CloseoutRowsModeIndexBlock.mark false)
def budget (width code : Nat) := CloseoutRowsModeIndexBlock.budget width code+8

theorem mark_step (bit : Bool) (bits pre : List Bool) (flag : Bool) (C : Nat) :
    Step (CloseoutRowsModeIndexBlock.mark bit) 1 ![0,0,0,pre.length]
      ![frame bits,[flag],List.replicate C false,pre]
      ![0,0,0,(pre++[bit]).length]
      ![frame bits,[flag],List.replicate C false,pre++[bit]] := by
  obtain ⟨r,hr,hf,hs⟩ := CloseoutRowsModeIndexBlock.mark_run bit bits pre flag C
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs.le⟩

theorem run (width code C : Nat) (pre : List Bool) (flag : Bool)
    (hn : code<2^width) (hc : 2*width+1≤C) :
    ∃ residue : List Bool,residue.length=width ∧
      Step machine (budget width code) ![0,0,0,pre.length]
        ![frame (binary width code),[flag],List.replicate C false,pre]
        ![0,0,0,(pre++ReflectedLiteralCache.singletonWord code).length]
        ![frame residue,[false],List.replicate C false,
          pre++ReflectedLiteralCache.singletonWord code] := by
  obtain ⟨residue,hlen,hblock⟩ := CloseoutRowsModeIndexBlock.block_run
    width code C (pre++[true]) flag hn hc
  have h := ((((mark_step true (binary width code) pre flag C).seq hblock).seq
    (mark_step false residue ((pre++[true])++ExtIncidence.block code) false C)).seq
    (mark_step false residue (((pre++[true])++ExtIncidence.block code)++[false]) false C)).seq
    (mark_step false residue ((((pre++[true])++ExtIncidence.block code)++[false])++[false]) false C)
  have hout : (((((pre++[true])++ExtIncidence.block code)++[false])++[false])++[false])=
      pre++ReflectedLiteralCache.singletonWord code := by
    rw [ReflectedLiteralCache.singletonWord_eq]
    simp [ExtIncidence.block,List.append_assoc]
  refine ⟨residue,hlen,?_⟩
  rw [hout] at h
  convert h using 1 <;>first | rfl | (unfold budget;omega)

end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairRecord
