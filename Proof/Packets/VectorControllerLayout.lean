import Proof.Packets.PhysicalIndexReload
import Proof.Packets.PhysicalIndexedAt
import Proof.Packets.VectorParentCommit
import Proof.Packets.VectorTransferReady

/-! A common finite arena for the physical vector controller. Ports0..255 are
reserved for the concrete delta provider, whose arithmetic block is0..33.
Resident vector banks, live loop indices, and the parent accumulator are
outside that provider arena. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorController
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

/-- 256/257 are previous/next banks;258/259/260 are child/parent/level indices;
261/262 hold the accumulated parent packet;263 is the retained zero dummy. -/
def childSlots : Fin 39→Fin 264 := Fin.addCases (m:=34) (n:=5) (motive:=fun _=>Fin 264)
  (fun i=>i.castAdd 230) (![256,258,263,261,262])
def parentSlots : Fin 41→Fin 264 := Fin.addCases (m:=39) (n:=2) (motive:=fun _=>Fin 264)
  childSlots (![257,259])




theorem childSlots_core (i : Fin 34) : childSlots (i.castAdd 5)=i.castAdd 230 := Fin.addCases_left i
theorem childSlots_extra (i : Fin 5) : childSlots (i.natAdd 34)=(![256,258,263,261,262] : Fin 5→Fin 264) i :=
  Fin.addCases_right i

theorem childSlots_injective : Function.Injective childSlots := by
  intro i j he
  revert he
  refine Fin.addCases (m:=34) (n:=5) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=34) (n:=5) (fun b=>?_) (fun b=>?_) j
    · intro he
      rw [childSlots_core,childSlots_core] at he
      have h:=congrArg Fin.val he
      exact Fin.ext h
    · intro he
      rw [childSlots_core,childSlots_extra] at he
      have h:=congrArg Fin.val he
      fin_cases b <;>dsimp at h <;>omega
  · refine Fin.addCases (m:=34) (n:=5) (fun b=>?_) (fun b=>?_) j
    · intro he
      rw [childSlots_extra,childSlots_core] at he
      have h:=congrArg Fin.val he
      fin_cases a <;>dsimp at h <;>omega
    · intro he
      rw [childSlots_extra,childSlots_extra] at he
      have hinj : Function.Injective (![256,258,263,261,262] : Fin 5→Fin 264) := by decide
      exact congrArg (fun k : Fin 5=>k.natAdd 34) (hinj he)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorController
