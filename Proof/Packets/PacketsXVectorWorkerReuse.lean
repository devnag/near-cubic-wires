import Proof.Packets.PacketsXVectorWorkerArena

/-! Existing metadata frames are physically cleared before their next cold
scalar calculation. No prior frame is replaced by a mathematical assignment. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def clearFields := Composition.machine
  (Composition.machine (PhysicalCopyInto.machine (31 : Fin 296) 0 180)
    (PhysicalCopyInto.machine (31 : Fin 296) 0 181)) (PhysicalCopyInto.machine (31 : Fin 296) 0 182)
def fieldsZero (R : Nat) (A : Fin 296→List Bool) :=
  Function.update (Function.update (Function.update A 180 (List.replicate R false))
    181 (List.replicate R false)) 182 (List.replicate R false)
def reusableMetadata := Composition.machine clearFields metadataMachine

theorem clear_fields_run (R : Nat) (A : Fin 296→List Bool)
    (hw : A 31=UnaryTemplate.tape R) (hz : A 0=List.replicate R false)
    (h180 : (A 180).length=R) (h181 : (A 181).length=R) (h182 : (A 182).length=R) :
    Step clearFields (6*R+8) heads A heads (fieldsZero R A) := by
  have first:=PhysicalCopyInto.run R (31 : Fin 296) 0 180 (by decide) (by decide) (by decide)
    heads A rfl rfl rfl hw (by rw [hz,List.length_replicate]) h180
  have second:=PhysicalCopyInto.run R (31 : Fin 296) 0 181 (by decide) (by decide) (by decide)
    heads (Function.update A 180 (A 0)) rfl rfl rfl
    (by simpa [Function.update] using hw) (by simp [Function.update,hz])
    (by simpa [Function.update] using h181)
  have third:=PhysicalCopyInto.run R (31 : Fin 296) 0 182 (by decide) (by decide) (by decide)
    heads (Function.update (Function.update A 180 (A 0)) 181 ((Function.update A 180 (A 0)) 0))
    rfl rfl rfl (by simpa [Function.update] using hw) (by simp [Function.update,hz])
    (by simpa [Function.update] using h182)
  have whole:=(first.seq second).seq third
  have hf : ((2*R+2)+1+(2*R+2))+1+(2*R+2)=6*R+8 := by omega
  rw [hf] at whole
  simpa [clearFields,fieldsZero,Function.update,hz] using whole

theorem cleared_metadata_input (R u n w parent child : Nat) (A : Fin 296→List Bool)
    (hin : ∀j,j≠11→j≠12→j≠21→A (metadataSlots j)=DeltaScalarFields.input R u n w parent child j) :
    ∀j,fieldsZero R A (metadataSlots j)=DeltaScalarFields.input R u n w parent child j := by
  intro j
  by_cases h11 : j=11
  · subst j;rfl
  by_cases h12 : j=12
  · subst j;rfl
  by_cases h21 : j=21
  · subst j;rfl
  have hi : Function.Injective metadataSlots := by decide
  have s180 : metadataSlots j≠180 := by
    intro he;exact h11 (hi (show metadataSlots j=metadataSlots 11 from he))
  have s181 : metadataSlots j≠181 := by
    intro he;exact h12 (hi (show metadataSlots j=metadataSlots 12 from he))
  have s182 : metadataSlots j≠182 := by
    intro he;exact h21 (hi (show metadataSlots j=metadataSlots 21 from he))
  simpa only [fieldsZero,Function.update_of_ne s180,Function.update_of_ne s181,
    Function.update_of_ne s182] using hin j h11 h12 h21

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
