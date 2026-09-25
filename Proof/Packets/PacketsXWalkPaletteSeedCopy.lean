import Proof.Packets.PhysicalTripleCopy
import Proof.Packets.PacketsXWalkSeedResident

/-! Route the resident walk decoder's three actual words into the literal
palette. The fifteen-tape walk bank precedes the 316-tape palette arena. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 15000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkPaletteSeedCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

def slots : Fin 7 → Fin 331 := ![17,11,12,13,21,22,23]
def source (j : Fin 3) : Fin 331 := ⟨11+j.val,by omega⟩
def target (j : Fin 3) : Fin 331 := ⟨21+j.val,by omega⟩
def machine := RecoveryFocus.machine slots PhysicalTripleCopy.machine
def output (A : Fin 331 → List Bool) :=
  Function.update (Function.update (Function.update A 21 (A 11)) 22 (A 12)) 23 (A 13)

theorem run (R : Nat) (H : Fin 331 → Nat) (A : Fin 331 → List Bool)
    (hh : ∀j,H (slots j)=0) (hw : A 17=UnaryTemplate.tape R)
    (hs : ∀j,(A (source j)).length=R) (ht : ∀j,(A (target j)).length=R) :
    Step machine (6*R+12) H A H (output A) := by
  have h:=PhysicalTripleCopy.run R (fun j=>A (source j)) (fun j=>A (target j)) hs ht
  apply PhysicalFocusBoundary.focus h slots (by decide) H H A (output A)
  · intro i;exact (hh i).symm
  · intro i;fin_cases i <;>first | exact hw.symm | rfl
  · intro i;exact (hh i).symm
  · intro i;fin_cases i <;>
      simp [PhysicalTripleCopy.data,slots,source,output,Function.update,hw]
  · intro i away
    have h21 : i≠21 := by intro he;subst i;exact away 4 rfl
    have h22 : i≠22 := by intro he;subst i;exact away 5 rfl
    have h23 : i≠23 := by intro he;subst i;exact away 6 rfl
    exact ⟨rfl,by simp [output,Function.update,h21,h22,h23]⟩

theorem target_word (A : Fin 331 → List Bool) (j : Fin 3) :
    output A (target j)=A (source j) := by
  fin_cases j <;>simp [output,target,source,Function.update]

theorem resident_target (rank R L : Nat)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code a b : List Bool)
    (palette : Fin 316 → List Bool) (j : Fin 3) :
    output (Fin.addCases (m:=15) (n:=316) (motive:=fun _=>List Bool)
      (WalkSeedResident.output rank R L v code a b) palette) (target j) =
      ZeroPadding.pad R (WalkSeedResident.fields rank v j) := by
  rw [target_word]
  have read : (source j)=(⟨11+j.val,by omega⟩ : Fin 15).castAdd 316 := by
    apply Fin.ext;rfl
  rw [read,Fin.addCases_left]
  exact WalkSeedResident.output_field rank R L v code a b j

end
end Theorem25Completion.WalkPaletteSeedCopy
