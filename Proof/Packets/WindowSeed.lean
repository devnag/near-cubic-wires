import Proof.Packets.WindowSeedClear
import Proof.Packets.WindowSeedBody

/-! Complete physical cold/reentry initialization of the fixed window
bank from actual resident numeric metadata and the common reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def H (driver : Nat) (i : Fin 69) : Nat := if i=61 then driver else 0
def driverSlot : Fin 1→Fin 69 := ![61]
def lower := RecoveryFocus.machine driverSlot (Completion.PhysicalDriverMoves.machine 1 .left)
def raise := RecoveryFocus.machine driverSlot (Completion.PhysicalDriverMoves.machine 1 .right)
def machine := Composition.machine lower (Composition.machine clear (Composition.machine body raise))
def budget (R v u M W : Nat) := 2*R+bodyBudget R v u M W+9

theorem lower_run (A : Fin 69→List Bool) (d : Nat) (hd : d≤1) :
    Step lower 1 (H d) A (fun _=>0) A := by
  have h:=Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>d) (fun _=>A 61)
  have hz:d-1=0:=by omega
  simp only [HeadMove.apply,hz] at h
  apply PhysicalFocusBoundary.focus h driverSlot (by decide) (H d) (fun _=>0) A A
  · intro i;fin_cases i;simp [driverSlot,H]
  · intro i;fin_cases i;rfl
  · intro i;rfl
  · intro i;fin_cases i;rfl
  · intro i away
    have hi:i≠61:=by intro he;subst i;exact away 0 rfl
    exact ⟨by simp [H,hi],rfl⟩

theorem raise_run (A : Fin 69→List Bool) :
    Step raise 1 (fun _=>0) A (H 1) A := by
  apply PhysicalFocusBoundary.focus
    (Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>0) (fun _=>A 61))
    driverSlot (by decide) (fun _=>0) (H 1) A A
  · intro i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;simp [H,driverSlot,HeadMove.apply]
  · intro i;fin_cases i;rfl
  · intro i away
    have hi:i≠61:=by intro he;subst i;exact away 0 rfl
    exact ⟨by simp [H,hi],rfl⟩

theorem cleared_initial (R v u M offset W target : Nat) (A : Fin 69→List Bool)
    (hraw : A 50=List.replicate R true) (hlog : A 51=List.replicate (R+3) false)
    (hmeta : ∀j : Fin 7,A (Fin.natAdd 62 j)=metadata R v u M offset W target j) :
    cleared R A=initial R v u M offset W target := by
  funext i
  fin_cases i <;>simp [cleared,initial,Fin.addCases,hraw,hlog]
  all_goals first | exact hmeta 0 | exact hmeta 1 | exact hmeta 2 | exact hmeta 3 |
    exact hmeta 4 | exact hmeta 5 | exact hmeta 6

theorem run (R v u M offset W target d : Nat) (A : Fin 69→List Bool)
    (hd : d≤1) (hu : 2*u+1≤R) (hv : 2*v+1≤R) (hM : M+1≤R) (hMv : M≤2^v)
    (hraw : A 50=List.replicate R true) (hlog : A 51=List.replicate (R+3) false)
    (hmeta : ∀j : Fin 7,A (Fin.natAdd 62 j)=metadata R v u M offset W target j)
    (hfit : ∀j,(A (privateSlot j)).length≤R) :
    Step machine (budget R v u M W) (H d) A (H 1) (produced R v u M offset W target) := by
  have middle:=clear_run R A hraw hlog hfit
  rw [cleared_initial R v u M offset W target A hraw hlog hmeta] at middle
  have all:=(lower_run A d hd).seq (middle.seq
    ((body_run R v u M offset W target hu hv hM hMv).seq (raise_run _)))
  have fuel : 1+1+((2*R+4)+1+(bodyBudget R v u M W+1+1))=budget R v u M W := by
    unfold budget;omega
  simpa only [machine,fuel] using all

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
