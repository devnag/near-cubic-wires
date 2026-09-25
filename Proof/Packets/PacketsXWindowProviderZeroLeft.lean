import Proof.Packets.PacketsXWindowCoordinateBoundary
import Proof.Packets.PacketsXWindowProviderZeroRight

/-! Actual left-operand clearing at the coordinate-phase boundary. This
permits the last vector-loop operand to be an arbitrary fitting packet. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def zeroLeft := Composition.machine (PhysicalCopyInto.machine (31 : Fin 256) 0 25)
  (PhysicalCopyInto.machine (31 : Fin 256) 0 28)
def leftZero (R : Nat) (A : Fin 256 → List Bool) :=
  Function.update (Function.update A 25 (List.replicate R false)) 28 (List.replicate R false)

theorem zero_left_run (R : Nat) (A : Fin 256 → List Bool)
    (hw : A 31=UnaryTemplate.tape R) (hz : A 0=List.replicate R false)
    (hp : (A 25).length=R) (hc : (A 28).length=R) :
    Step zeroLeft (4*R+5) heads A heads (leftZero R A) := by
  have first:=PhysicalCopyInto.run R (31 : Fin 256) 0 25 (by decide) (by decide) (by decide)
    heads A rfl rfl rfl hw (by rw [hz,List.length_replicate]) hp
  have last:=PhysicalCopyInto.run R (31 : Fin 256) 0 28 (by decide) (by decide) (by decide)
    heads (Function.update A 25 (A 0)) rfl rfl rfl
    (by simpa [Function.update] using hw) (by simp [Function.update,hz])
    (by simpa [Function.update] using hc)
  have whole:=first.seq last
  have hf : (2*R+2)+1+(2*R+2)=4*R+5 := by omega
  rw [hf] at whole
  simpa [zeroLeft,leftZero,Function.update_of_ne (by decide : (0 : Fin 256)≠25),hz] using whole

theorem zero_left_other (R : Nat) (A : Fin 256 → List Bool) (i : Fin 256)
    (h25 : i≠25) (h28 : i≠28) : leftZero R A i=A i := by
  simp only [leftZero,Function.update_of_ne h25,Function.update_of_ne h28]

theorem zero_left_engine (C R : Nat) (left right : PacketVector.Packet)
    (A : Fin 256 → List Bool) (hR : 1≤R)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left right i) :
    ∀i : Fin 34,leftZero R A (i.castAdd 222)=ReusableArithmetic.state C R [] right i := by
  intro i
  by_cases h25 : i=25
  · subst i
    change List.replicate R false=ZeroPadding.pad R []
    simp [ZeroPadding.pad]
  by_cases h28 : i=28
  · subst i
    change List.replicate R false=ZeroPadding.pad R (CompareMachine.word 0)
    simpa only [CompareMachine.word,List.replicate_zero,List.replicate_one,Nat.max_eq_left hR] using
      (Rewind.Workspace.pad_zeros R 1).symm
  have ne (j : Fin 34) (hij : i≠j) : i.castAdd 222≠j.castAdd 222 := by
    intro he;exact hij (Fin.ext (congrArg (fun k : Fin 256=>k.val) he))
  rw [zero_left_other R A _ (ne 25 h25) (ne 28 h28),hengine]
  simpa only [VectorAccumulator.tapes_engine] using
    VectorAccumulator.tapes_left_outside C R left right [] [] (i.castAdd 2)
      (by intro he;exact h25 (Fin.ext (congrArg (fun k : Fin 36=>k.val) he)))
      (by intro he;exact h28 (Fin.ext (congrArg (fun k : Fin 36=>k.val) he)))

theorem zero_left_provider (C R : Nat) (left right : PacketVector.Packet)
    (A : Fin 256 → List Bool) (hR : 1≤R) (hl : VectorAccumulator.Fits R left)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left right i) :
    Step zeroLeft (4*R+5) heads A heads (leftZero R A) ∧
    (∀i : Fin 34,leftZero R A (i.castAdd 222)=ReusableArithmetic.state C R [] right i) := by
  refine ⟨zero_left_run R A (hengine 31) (hengine 0) ?_ ?_,zero_left_engine C R left right A hR hengine⟩
  · rw [show A 25=ReusableArithmetic.state C R left right 25 from hengine 25]
    exact VectorAccumulator.flat_length R left hl
  · rw [show A 28=ReusableArithmetic.state C R left right 28 from hengine 28]
    exact VectorAccumulator.count_length R left hl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
