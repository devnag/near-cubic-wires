import Proof.Packets.PhysicalRepeatStep
import Proof.Packets.VectorCounterDecrement

/-! Counted physical loops over an existing arena counter. The chosen counter
is incremented by the machine after every worker call; no separate logical
index is substituted for its resident tape. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalIndexedAt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def H {t : Nat} (port : Fin t) (h : Fin t→Nat) := Function.update h port 1
def A {t : Nat} (port : Fin t) (R index : Nat) (a : Fin t→List Bool) :=
  Function.update a port (ZeroPadding.pad R (CompareMachine.word index))
def advance {t : Nat} (port : Fin t) := RecoveryFocus.machine (fun _ : Fin 1=>port) VectorCounter.increment
def body {t s : Nat} (port : Fin t) (worker : Machine t s) := Composition.machine worker (advance port)
def machine {t s : Nat} (port : Fin t) (worker : Machine t s) := RepeatMachine.machine (body port worker) (fun _ _=>true)

theorem advance_run {t : Nat} (port : Fin t) (R index : Nat) (h : Fin t→Nat) (a : Fin t→List Bool) :
    Step (advance port) (2*index+2) (H port h) (A port R index a)
      (H port h) (A port R (index+1) a) := by
  apply PhysicalFocusBoundary.focus (VectorCounter.increment_padded index R) (fun _ : Fin 1=>port)
    (by intro i j _;exact Subsingleton.elim i j) (H port h) (H port h) _ _
  · intro i;simp only [H,Function.update_self]
  · intro i;simp only [A,Function.update_self]
  · intro i;simp only [H,Function.update_self]
  · intro i;simp only [A,Function.update_self]
  · intro i away
    have hi : i≠port := by intro he;exact away 0 he.symm
    exact ⟨rfl,by simp only [A,Function.update_of_ne hi]⟩

theorem run {t s : Nat} (port : Fin t) (worker : Machine t s) (N E R : Nat)
    (hs : Nat→Fin t→Nat) (as : Nat→Fin t→List Bool)
    (hworker : ∀ i,i<N→Step worker E (H port (hs i)) (A port R i (as i))
      (H port (hs (i+1))) (A port R i (as (i+1)))) :
    Step (machine port worker) (N*(E+2*N+6)+3)
      (Fin.addCases (H port (hs 0)) (fun _ : Fin 1=>1))
      (Fin.addCases (A port R 0 (as 0)) (fun _ : Fin 1=>CompareMachine.word N))
      (Fin.addCases (H port (hs N)) (fun _ : Fin 1=>1))
      (Fin.addCases (A port R N (as N)) (fun _ : Fin 1=>CompareMachine.word N)) := by
  have hb (i : Nat) (hi : i<N) : Step (body port worker) (E+2*N+3)
      (H port (hs i)) (A port R i (as i)) (H port (hs (i+1))) (A port R (i+1) (as (i+1))) := by
    exact ((hworker i hi).seq (advance_run port R i (hs (i+1)) (as (i+1)))).enlarge (by omega)
  have h:=PhysicalRepeatStep.run (body port worker) N (E+2*N+3)
    (fun i=>H port (hs i)) (fun i=>A port R i (as i)) hb
  have fuel : N*((E+2*N+3)+3)+3=N*(E+2*N+6)+3 := by ring
  rw [fuel] at h
  exact h

def retreat {t : Nat} (port : Fin t) := RecoveryFocus.machine (fun _ : Fin 1=>port) VectorCounter.decrement
def downBody {t s : Nat} (port : Fin t) (worker : Machine t s) := Composition.machine (retreat port) worker
def downMachine {t s : Nat} (port : Fin t) (worker : Machine t s) := RepeatMachine.machine (downBody port worker) (fun _ _=>true)

theorem retreat_run {t : Nat} (port : Fin t) (R index : Nat) (h : Fin t→Nat) (a : Fin t→List Bool)
    (hc : index+2≤R) :
    Step (retreat port) (2*index+4) (H port h) (A port R (index+1) a)
      (H port h) (A port R index a) := by
  apply PhysicalFocusBoundary.focus (VectorCounter.decrement_padded index R hc) (fun _ : Fin 1=>port)
    (by intro i j _;exact Subsingleton.elim i j) (H port h) (H port h) _ _
  · intro i;simp only [H,Function.update_self]
  · intro i;simp only [A,Function.update_self]
  · intro i;simp only [H,Function.update_self]
  · intro i;simp only [A,Function.update_self]
  · intro i away
    have hi : i≠port := by intro he;exact away 0 he.symm
    exact ⟨rfl,by simp only [A,Function.update_of_ne hi]⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalIndexedAt
