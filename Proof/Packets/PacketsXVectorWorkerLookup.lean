import Proof.Packets.PacketVector
import Proof.Packets.PacketsXVectorWorkerData

/-! Actual final-coordinate lookup into the right arithmetic operand, retaining
the full provider state, both vector banks, and all live counters. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def lookupSlots (j : Fin 37) : Fin 296:=childSlots (j.castAdd 2)
def lookupRight:=RecoveryFocus.machine lookupSlots VectorChildLookup.machine

theorem lookup_injective : Function.Injective lookupSlots := by
  intro i j he
  have ho : VectorController.childSlots (i.castAdd 2)=VectorController.childSlots (j.castAdd 2) :=
    Fin.ext (congrArg (fun z : Fin 296=>z.val) he)
  have hi:=VectorController.childSlots_injective ho
  exact Fin.ext (congrArg (fun z : Fin 39=>z.val) hi)

theorem lookup_core (i : Fin 34) : lookupSlots (i.castAdd 3)=i.castAdd 262 := by
  change (VectorController.childSlots (i.castAdd 5)).castAdd 32=i.castAdd 262
  rw [VectorController.childSlots_core]
  rfl

theorem lookup_extra (i : Fin 3) : lookupSlots (i.natAdd 34)=(![256,258,263] : Fin 3→Fin 296) i := by
  fin_cases i <;>rfl

theorem lookup_heads (mh : Fin 222→Nat) (j : Fin 37) :
    VectorChildLookup.heads j=H mh (lookupSlots j) := by
  refine Fin.addCases (m:=34) (n:=3) (fun k=>?_) (fun k=>?_) j
  · rw [lookup_core]
    change (Fin.addCases (m:=34) (n:=3) (motive:=fun _=>Nat) ReusableArithmetic.heads (![0,1,0])) (k.castAdd 3)=_
    rw [Fin.addCases_left]
    change ReusableArithmetic.heads k=(Fin.addCases (m:=264) (n:=32) (motive:=fun _=>Nat)
      (VectorController.H mh) (fun _=>0)) ((k.castAdd 230).castAdd 32)
    rw [Fin.addCases_left,VectorController.H_core]
  · rw [lookup_extra];fin_cases k <;>rfl

theorem lookup_tapes (C R ci pi li : Nat) (left right acc : PacketVector.Packet)
    (previous next : List Bool) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (j : Fin 37) :
    VectorChildLookup.tapes C R ci left right previous j=
      A C R ci pi li left right acc previous next fields extra (lookupSlots j) := by
  refine Fin.addCases (m:=34) (n:=3) (fun k=>?_) (fun k=>?_) j
  · rw [lookup_core]
    change (Fin.addCases (m:=34) (n:=3) (motive:=fun _=>List Bool) (ReusableArithmetic.state C R left right)
      (![previous,ZeroPadding.pad R (CompareMachine.word ci),List.replicate R false])) (k.castAdd 3)=_
    rw [Fin.addCases_left]
    change ReusableArithmetic.state C R left right k=(Fin.addCases (m:=264) (n:=32) (motive:=fun _=>List Bool)
      (VectorController.A C R ci pi li left right acc previous next fields) extra) ((k.castAdd 230).castAdd 32)
    rw [Fin.addCases_left,VectorController.A_core]
  · rw [lookup_extra];fin_cases k <;>rfl

theorem lookup_outside (C R ci pi li : Nat) (left right selected acc : PacketVector.Packet)
    (previous next : List Bool) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (i : Fin 296) (away : ∀j,lookupSlots j≠i) :
    A C R ci pi li left right acc previous next fields extra i=
      A C R ci pi li left selected acc previous next fields extra i := by
  revert away
  refine Fin.addCases (m:=264) (n:=32) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=256) (n:=8) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=34) (n:=222) (fun l=>?_) (fun l=>?_) k
      · intro away;exact False.elim (away (l.castAdd 3) (lookup_core l))
      · intro _;simp only [A,VectorController.A,Fin.addCases_left,Fin.addCases_right]
    · intro _;simp only [A,VectorController.A,Fin.addCases_left,Fin.addCases_right]
  · intro _;simp only [A,Fin.addCases_right]

attribute [local irreducible] VectorChildLookup.machine lookupRight

theorem lookup_vector_run (C R pi li : Nat) (ps : List PacketVector.Packet) (i : Fin ps.length)
    (left right acc : PacketVector.Packet) (next : List Bool)
    (mh : Fin 222→Nat) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (hps : ∀P∈ps,PacketVector.Fits R P) (hr : VectorAccumulator.Fits R right) :
    Step lookupRight (PacketBank.lookupBudget R i.val+4)
      (H mh) (A C R i.val pi li left right acc (PacketVector.bank R ps) next fields extra)
      (H mh) (A C R i.val pi li left ps[i.val] acc (PacketVector.bank R ps) next fields extra) := by
  have hs:=hps _ (List.getElem_mem i.isLt)
  have hpre : (PacketVector.bank R (ps.take i.val)).length=2*i.val*R := by
    rw [PacketVector.bank_length R _ (fun P hP=>hps P (List.mem_of_mem_take hP)),List.length_take]
    rw [Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  have hc : ps[i.val].length+1≤R := by simpa [CompareMachine.word] using hs.2
  have small:=VectorChildLookup.run C R i.val left right ps[i.val]
    (PacketVector.bank R (ps.take i.val)) (PacketVector.bank R (ps.drop (i.val+1))) hpre hr.1 hr.2 hs.1 hc
  have bank:=PacketVector.bank_split R ps i
  unfold PacketVector.payload PacketVector.count at bank
  dsimp only at small
  rw [←bank] at small
  unfold lookupRight
  apply PhysicalFocusBoundary.focus small lookupSlots lookup_injective (H mh) (H mh) _ _
  · exact lookup_heads mh
  · exact lookup_tapes C R i.val pi li left right acc _ next fields extra
  · exact lookup_heads mh
  · exact lookup_tapes C R i.val pi li left ps[i.val] acc _ next fields extra
  · intro j away
    exact ⟨rfl,lookup_outside C R i.val pi li left right ps[i.val] acc _ next fields extra j away⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
