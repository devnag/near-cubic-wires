import Proof.Packets.SubstitutionOuterData

/-! The executed descending product loop docked into the outer sum arena. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def innerH (position : Nat) : Fin 39→Nat :=
  Fin.addCases (m:=38) (n:=1) (SubstitutionBit.H position) (fun _=>1)
def innerA (C R index : Nat) (left right : Packet) (atoms source : List Bool) : Fin 39→List Bool :=
  Fin.addCases (m:=38) (n:=1) (SubstitutionBit.A C R index left right atoms source)
    (fun _=>CompareMachine.word C)

theorem innerA_core (C R index : Nat) (left right : Packet) (atoms source : List Bool) (i : Fin 34) :
    innerA C R index left right atoms source (i.castAdd 5)=ReusableArithmetic.state C R left right i := by
  change innerA C R index left right atoms source (((i.castAdd 3).castAdd 1).castAdd 1)=_
  unfold innerA SubstitutionBit.A ArithmeticLookup.A
  rw [Fin.addCases_left,Fin.addCases_left,Fin.addCases_left]


theorem innerA_extra (C R index : Nat) (left right : Packet) (atoms source : List Bool) (i : Fin 5) :
    innerA C R index left right atoms source (i.natAdd 34)=
      (![atoms,ZeroPadding.pad R (CompareMachine.word index),List.replicate R false,source,
        CompareMachine.word C] : Fin 5→List Bool) i := by
  fin_cases i <;>rfl

theorem innerH_core (position : Nat) (i : Fin 34) :
    innerH position (i.castAdd 5)=ReusableArithmetic.heads i := by
  change innerH position (((i.castAdd 3).castAdd 1).castAdd 1)=_
  unfold innerH SubstitutionBit.H
  rw [Fin.addCases_left,Fin.addCases_left]
  fin_cases i <;>rfl


theorem innerH_extra (position : Nat) (i : Fin 5) :
    innerH position (i.natAdd 34)=(![0,1,0,position,1] : Fin 5→Nat) i := by
  fin_cases i <;>rfl

theorem inner_heads (position : Nat) :
    (fun i : Fin 39=>H position 1 (i.castAdd 4))=innerH position := by
  funext i
  refine Fin.addCases (m:=34) (n:=5) (fun j=>?_) (fun j=>?_) i
  · rw [innerH_core]
    exact H_core position 1 j
  · rw [innerH_extra]
    fin_cases j <;>rfl

theorem inner_tapes (C R index : Nat) (left right : Packet) (atoms source : List Bool) (stored : Packet) :
    (fun i : Fin 39=>A C R index left right atoms source stored (i.castAdd 4))=
      innerA C R index left right atoms source := by
  funext i
  refine Fin.addCases (m:=34) (n:=5) (fun j=>?_) (fun j=>?_) i
  · rw [innerA_core]
    exact A_core C R index left right atoms source stored j
  · rw [innerA_extra]
    fin_cases j <;>rfl


theorem outside_inner (C R index index' position position' : Nat) (left right left' right' : Packet)
    (atoms source : List Bool) (stored : Packet) (j : Fin 4) :
    H position 1 (j.natAdd 39)=H position' 1 (j.natAdd 39) ∧
    A C R index left right atoms source stored (j.natAdd 39)=
      A C R index' left' right' atoms source stored (j.natAdd 39) := by
  have he : (j.natAdd 5).natAdd 34=j.natAdd 39 := by
    apply Fin.ext
    simp only [Fin.val_natAdd]
    omega
  rw [←he,H_extra,H_extra,A_extra,A_extra]
  fin_cases j <;>exact ⟨rfl,rfl⟩

noncomputable def scanMachine := RecoveryFocus.machine (Fin.castAdd 4) SubstitutionScan.machine

set_option maxHeartbeats 18000 in
theorem dock_scan (C R base : Nat) (source : List Bool) (atoms : List Packet) (left right stored : Packet)
    (hlen : atoms.length=C) (hR : C+1≤R)
    (hAtoms : ∀ P∈atoms,PacketVector.Fits R P ∧ ∀ bits∈P,bits.length=C)
    (hstates : ∀ k,k<C→
      let p:=SubstitutionScan.scan C base source atoms left right k
      let selected:=atoms.getD (C-(k+1)) []
      PacketVector.Fits R p.1 ∧ (∀ bits∈p.2,bits.length=C) ∧
      (∀ i,(ReusableArithmetic.data C selected p.2 i).length≤R) ∧
      NormalizedMultiply.budget C selected p.2+3≤R) :
    let answer:=SubstitutionScan.scan C base source atoms left right C
    Step scanMachine (SubstitutionScan.budget C R)
      (H (base+C) 1) (A C R C left right (PacketVector.bank R atoms) source stored)
      (H base 1) (A C R 0 answer.1 answer.2 (PacketVector.bank R atoms) source stored) := by
  dsimp only
  have small:=SubstitutionScan.run C C R base source atoms left right hlen hR hAtoms hstates
  change Step SubstitutionScan.machine (SubstitutionScan.budget C R)
    (innerH (base+(C-0))) (innerA C R (C-0) left right (PacketVector.bank R atoms) source)
    (innerH (base+(C-C))) (innerA C R (C-C) _ _ (PacketVector.bank R atoms) source) at small
  simp only [Nat.sub_zero,Nat.sub_self,Nat.add_zero] at small
  apply PhysicalFocusBoundary.focus small (Fin.castAdd 4) (Fin.castAdd_injective 39 4)
    (H (base+C) 1) (H base 1) _ _
  · intro i;exact (congrFun (inner_heads (base+C)) i).symm
  · intro i;exact (congrFun (inner_tapes C R C left right (PacketVector.bank R atoms) source stored) i).symm
  · intro i;exact (congrFun (inner_heads base) i).symm
  · intro i;exact (congrFun (inner_tapes C R 0 _ _ (PacketVector.bank R atoms) source stored) i).symm
  · intro i away
    revert away
    refine Fin.addCases (m:=39) (n:=4) (fun j=>?_) (fun j=>?_) i
    · intro away;exact False.elim (away j rfl)
    · intro _
      exact outside_inner C R C 0 (base+C) base left right _ _ (PacketVector.bank R atoms) source stored j

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
