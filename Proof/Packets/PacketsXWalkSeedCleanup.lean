import Proof.Packets.PacketsXWalkSeedResident

/-! The resident decoder's six temporary tapes are physically cleared for the
next vertex. Coordinates, rank template, label cursor and edge resources remain. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 15000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedCleanup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open NearCubicWires.RepairOrdinary.SignedSortKey
open PCJ9eff70d512234a4c_Fixed
noncomputable section

theorem output_ambient (rank R L : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code a b : List Bool) (j : Fin 9) (hj : ∀i,WalkSeedDecode.slots i≠j) :
    WalkSeedResident.output rank R L v code a b (WalkSeedResident.slots j)=
      ZeroPadding.pad R (WalkSeedDecode.middle rank
        (binary (toeplitzWalkSideBits rank) v.1.val) (binary (toeplitzWalkSideBits rank) v.2.val) a j) := by
  rw [WalkSeedResident.output,install_slot WalkSeedResident.slots (by decide)]
  exact congrArg (ZeroPadding.pad R) (WalkSeedDecode.output_ambient rank _ _ _ _ _ a b j hj)

theorem output_slice (rank R L : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code a b : List Bool) (j : Fin 6) :
    WalkSeedResident.output rank R L v code a b (WalkSeedResident.slots (WalkSeedDecode.slots j))=
      ZeroPadding.pad R (WalkSeedReady.output rank (WalkSeedBinary.vertexWord rank v)
        (WalkSeedResident.fields rank v 0) (WalkSeedResident.fields rank v 1) (WalkSeedResident.fields rank v 2) b j) := by
  rw [WalkSeedResident.output,install_slot WalkSeedResident.slots (by decide)]
  exact congrArg (ZeroPadding.pad R) (WalkSeedDecode.output_selected rank _ _ _ _ _ a b j)

def slots : Fin 8→Fin 15:=![8,9,11,12,13,14,4,6]
def scratch (rank R : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (a b : List Bool) : Fin 6→List Bool:=
  fun i=>ZeroPadding.pad R ((![WalkSeedBinary.vertexWord rank v,a,
    WalkSeedResident.fields rank v 0,WalkSeedResident.fields rank v 1,WalkSeedResident.fields rank v 2,b] : Fin 6→List Bool) i)
attribute [local irreducible] WalkSeedResident.machine RecoveryScratchErase.resetMachine

def machine:=RecoveryFocus.machine slots (CycleFields.Primitives.eraseMachine 6)

theorem scratch_length (rank R : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (a b : List Bool) (hR : 8*rank+14≤R) (ha : a.length≤6*rank+5) (hb : b.length≤8*rank+14) :
    ∀i,(scratch rank R v a b i).length≤R := by
  have hv : 2*toeplitzWalkSideBits rank≤3*rank+1 :=
    (twice_toeplitzWalkSideBits_le rank).trans (by have h:=toeplitzSeedBits_le_three_mul rank;omega)
  intro i
  fin_cases i
  · change (ZeroPadding.pad R (WalkSeedBinary.vertexWord rank v)).length≤R
    rw [ZeroPadding.pad_length,WalkSeedBinary.vertexWord_length]
    omega
  · change (ZeroPadding.pad R a).length≤R
    rw [ZeroPadding.pad_length]
    omega
  · change (ZeroPadding.pad R (List.ofFn (fun i : Fin rank=>decide ((toeplitzWalkEncoding rank v).1.1.1 i=1)))).length≤R
    rw [ZeroPadding.pad_length,List.length_ofFn]
    omega
  · change (ZeroPadding.pad R (List.ofFn (fun i : Fin (rank-1)=>decide ((toeplitzWalkEncoding rank v).1.1.2 i=1)))).length≤R
    rw [ZeroPadding.pad_length,List.length_ofFn]
    omega
  · change (ZeroPadding.pad R (List.ofFn (fun i : Fin rank=>decide ((toeplitzWalkEncoding rank v).1.2 i=1)))).length≤R
    rw [ZeroPadding.pad_length,List.length_ofFn]
    omega
  · change (ZeroPadding.pad R b).length≤R
    rw [ZeroPadding.pad_length]
    omega

theorem run (rank R L position : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code a b : List Bool) (hR : 8*rank+14≤R) (ha : a.length≤6*rank+5) (hb : b.length≤8*rank+14) :
    Step machine (2*R+4) (WalkSeedResident.heads position) (WalkSeedResident.output rank R L v code a b)
      (WalkSeedResident.heads position) (WalkSeedResident.input rank R L v code) := by
  have h:=CycleFields.Primitives.erase_step R (R+1) (scratch rank R v a b)
    (scratch_length rank R v a b hR ha hb) le_rfl
  apply PhysicalFocusBoundary.focus h slots (by decide)
    (WalkSeedResident.heads position) (WalkSeedResident.heads position)
    (WalkSeedResident.output rank R L v code a b) (WalkSeedResident.input rank R L v code)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i
    · exact (output_slice rank R L v code a b 0).symm
    · exact (output_ambient rank R L v code a b 3 (by decide)).symm
    · exact (WalkSeedResident.output_field rank R L v code a b 0).symm
    · exact (WalkSeedResident.output_field rank R L v code a b 1).symm
    · exact (WalkSeedResident.output_field rank R L v code a b 2).symm
    · exact (output_slice rank R L v code a b 5).symm
    · change WalkSeedResident.input rank R L v code 4=WalkSeedResident.output rank R L v code a b 4
      exact (install_other WalkSeedResident.slots _ _ 4 (by decide)).symm
    · change WalkSeedResident.input rank R L v code 6=WalkSeedResident.output rank R L v code a b 6
      exact (install_other WalkSeedResident.slots _ _ 6 (by decide)).symm
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    refine ⟨rfl,?_⟩
    fin_cases i
    · exact output_ambient rank R L v code a b 0 (by decide)
    · exact output_ambient rank R L v code a b 1 (by decide)
    · exact install_other WalkSeedResident.slots _ _ 2 (by decide)
    · exact install_other WalkSeedResident.slots _ _ 3 (by decide)
    · exact False.elim (away 6 rfl)
    · exact install_other WalkSeedResident.slots _ _ 5 (by decide)
    · exact False.elim (away 7 rfl)
    · exact install_other WalkSeedResident.slots _ _ 7 (by decide)
    · exact False.elim (away 0 rfl)
    · exact False.elim (away 1 rfl)
    · exact output_slice rank R L v code a b 1
    · exact False.elim (away 2 rfl)
    · exact False.elim (away 3 rfl)
    · exact False.elim (away 4 rfl)
    · exact False.elim (away 5 rfl)

end
end Theorem25Completion.WalkSeedCleanup
