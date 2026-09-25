import Proof.Packets.PacketsXWindowLevelAtoms
import Proof.Packets.PacketsXWindowLiteralState

/-! Paid right-operand clearing before a new level-cache call. The two
actual copies retain the left operand, common resources, and every metadata
word, so a previous level's nonempty arithmetic result is permitted. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def zeroRight := Composition.machine (PhysicalCopyInto.machine (31 : Fin 256) 0 26)
  (PhysicalCopyInto.machine (31 : Fin 256) 0 27)
def rightZero (R : Nat) (A : Fin 256→List Bool) :=
  Function.update (Function.update A 26 (List.replicate R false)) 27 (List.replicate R false)

theorem zero_right_run (R : Nat) (A : Fin 256→List Bool)
    (hw : A 31=UnaryTemplate.tape R) (hz : A 0=List.replicate R false)
    (hp : (A 26).length=R) (hc : (A 27).length=R) :
    Step zeroRight (4*R+5) heads A heads (rightZero R A) := by
  have first:=PhysicalCopyInto.run R (31 : Fin 256) 0 26 (by decide) (by decide) (by decide)
    heads A rfl rfl rfl hw (by rw [hz,List.length_replicate]) hp
  have last:=PhysicalCopyInto.run R (31 : Fin 256) 0 27 (by decide) (by decide) (by decide)
    heads (Function.update A 26 (A 0)) rfl rfl rfl
    (by simpa [Function.update] using hw) (by simp [Function.update,hz])
    (by simpa [Function.update] using hc)
  have whole:=first.seq last
  have hf : (2*R+2)+1+(2*R+2)=4*R+5 := by omega
  rw [hf] at whole
  simpa [zeroRight,rightZero,Function.update_of_ne (by decide : (0 : Fin 256)≠26),hz] using whole

theorem right_zero_completed (R : Nat) (hR : 1≤R) (A : Fin 256→List Bool) :
    rightZero R A=completed R [] A := by
  have hnil : ZeroPadding.pad R ([] : List Bool)=List.replicate R false := by simp [ZeroPadding.pad]
  have hword : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := by
    simpa only [CompareMachine.word,List.replicate_zero,List.replicate_one,Nat.max_eq_left hR] using
      Rewind.Workspace.pad_zeros R 1
  simp only [rightZero,completed,List.flatten_nil,List.length_nil,hnil,hword]

theorem zero_right_engine (C R : Nat) (left right : PacketVector.Packet)
    (A : Fin 256→List Bool) (hR : 1≤R)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left right i) :
    ∀i : Fin 34,rightZero R A (i.castAdd 222)=ReusableArithmetic.state C R left [] i := by
  rw [right_zero_completed R hR A]
  exact completed_core C R left right [] A hengine

theorem zero_right_other (R : Nat) (A : Fin 256→List Bool) (i : Fin 256)
    (h26 : i≠26) (h27 : i≠27) : rightZero R A i=A i := by
  simp only [rightZero,Function.update_of_ne h26,Function.update_of_ne h27]

theorem zero_right_provider (C R : Nat) (left right : PacketVector.Packet)
    (A : Fin 256→List Bool) (hR : 1≤R) (hr : VectorAccumulator.Fits R right)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left right i) :
    Step zeroRight (4*R+5) heads A heads (rightZero R A) ∧
    (∀i : Fin 34,rightZero R A (i.castAdd 222)=ReusableArithmetic.state C R left [] i) := by
  refine ⟨zero_right_run R A (hengine 31) ?_ ?_ ?_,zero_right_engine C R left right A hR hengine⟩
  · exact hengine 0
  · rw [show A 26=ReusableArithmetic.state C R left right 26 from hengine 26]
    exact VectorAccumulator.flat_length R right hr
  · rw [show A 27=ReusableArithmetic.state C R left right 27 from hengine 27]
    exact VectorAccumulator.count_length R right hr

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
