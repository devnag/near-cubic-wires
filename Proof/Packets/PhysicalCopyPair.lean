import Proof.Packets.PhysicalCopyInto

/-! Two paid resident-word copies using the same retained physical reserve.
The second source and target are required to survive the first write. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCopyPair
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

noncomputable def machine {t : Nat} (width s1 t1 s2 t2 : Fin t) :=
  Composition.machine (PhysicalCopyInto.machine width s1 t1) (PhysicalCopyInto.machine width s2 t2)

theorem run {t : Nat} (R : Nat) (width s1 t1 s2 t2 : Fin t) (H : Fin t→Nat) (A : Fin t→List Bool)
    (hne1 : s1≠t1) (hne2 : s2≠t2) (hsurvive : s2≠t1) (htarget : t2≠t1)
    (hw : H width=1) (hs1 : H s1=0) (ht1 : H t1=0) (hs2 : H s2=0) (ht2 : H t2=0)
    (hwA : A width=UnaryTemplate.tape R)
    (hl1 : (A s1).length=R) (hlt1 : (A t1).length=R)
    (hl2 : (A s2).length=R) (hlt2 : (A t2).length=R) :
    Step (machine width s1 t1 s2 t2) (4*R+5) H A H
      (Function.update (Function.update A t1 (A s1)) t2 (A s2)) := by
  have nw1 : width≠s1 := by intro he;have e:=congrArg H he;omega
  have nwt1 : width≠t1 := by intro he;have e:=congrArg H he;omega
  have nw2 : width≠s2 := by intro he;have e:=congrArg H he;omega
  have nwt2 : width≠t2 := by intro he;have e:=congrArg H he;omega
  have first:=PhysicalCopyInto.run R width s1 t1 nw1 nwt1 hne1 H A hw hs1 ht1 hwA hl1 hlt1
  have second:=PhysicalCopyInto.run R width s2 t2 nw2 nwt2 hne2 H (Function.update A t1 (A s1))
    hw hs2 ht2 (by simpa only [Function.update_of_ne nwt1] using hwA)
    (by simpa only [Function.update_of_ne hsurvive] using hl2)
    (by simpa only [Function.update_of_ne htarget] using hlt2)
  simp only [Function.update_of_ne hsurvive] at second
  have h:=first.seq second
  have hf : (2*R+2)+1+(2*R+2)=4*R+5 := by omega
  rw [hf] at h
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCopyPair
