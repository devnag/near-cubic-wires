import Proof.MachineModel.CacheTail

/-! The cache finalizer reuses sixteen existing source-bank scratch tapes.
Live source, occurrence counts, body, domain and capacity driver stay separate. -/
namespace NearCubicWires.ExtDecompositionBatch.FinalLayout
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a:DecompositionAlgorithm)

def prefixValue (S j:ℕ):=if j=0 then S+3 else if j=1 then S+6 else if j=2 then S+5
  else if j=19 then S+4 else if j=20 then S+7 else j-3
def prefixSlots (j:Fin 21) : Fin (T a):=⟨prefixValue (SB a) j.val,by
  have hj:=j.isLt
  have hs:=sb_eq a
  unfold prefixValue T
  split_ifs <;> omega⟩
theorem prefix_injective : Function.Injective (prefixSlots a):=by
  intro i j h
  have hv:=congrArg (fun x:Fin (T a)=>x.val) h
  change prefixValue (SB a) i.val=prefixValue (SB a) j.val at hv
  have hi:=i.isLt;have hj:=j.isLt;have hs:=sb_eq a
  unfold prefixValue at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def tailValue (S j:ℕ):=if j=0 then S+2 else if j=1 then 14 else if j=2 then S+4
  else if j=3 then S+10 else if j=4 then S+3 else if j=5 then S+8 else S+9
def tailSlots (j:Fin 7) : Fin (T a):=⟨tailValue (SB a) j.val,by
  have hs:=sb_eq a
  unfold tailValue T
  split_ifs <;> omega⟩
theorem tail_injective : Function.Injective (tailSlots a):=by
  intro i j h
  have hv:=congrArg (fun x:Fin (T a)=>x.val) h
  change tailValue (SB a) i.val=tailValue (SB a) j.val at hv
  have hi:=i.isLt;have hj:=j.isLt;have hs:=sb_eq a
  unfold tailValue at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem prefix_other (e:Fin 12) (h3:e.val≠3) (h4:e.val≠4) (h5:e.val≠5)
    (h6:e.val≠6) (h7:e.val≠7) : ∀j,prefixSlots a j≠ex a e:=by
  intro j h
  have hv:=congrArg (fun x:Fin (T a)=>x.val) h
  change prefixValue (SB a) j.val=SB a+e.val at hv
  have hj:=j.isLt;have hs:=sb_eq a
  unfold prefixValue at hv
  split_ifs at hv <;> omega

theorem tail_other (e:Fin 12) (h2:e.val≠2) (h3:e.val≠3) (h4:e.val≠4)
    (h8:e.val≠8) (h9:e.val≠9) (h10:e.val≠10) : ∀j,tailSlots a j≠ex a e:=by
  intro j h
  have hv:=congrArg (fun x:Fin (T a)=>x.val) h
  change tailValue (SB a) j.val=SB a+e.val at hv
  have hs:=sb_eq a
  unfold tailValue at hv
  split_ifs at hv <;> omega


noncomputable def prefixMachine:=RecoveryFocus.machine (prefixSlots a) CachePrefix.machine
noncomputable def tailMachine:=RecoveryFocus.machine (tailSlots a) CacheTail.machine
noncomputable def machine:=Composition.machine (prefixMachine a) (tailMachine a)

end NearCubicWires.ExtDecompositionBatch.FinalLayout
