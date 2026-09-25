import Proof.Packets.PacketsXDescendingWindowInner

/-! The actual descending inner repeat with a retained padded count bank,
including the two paid cursor moves at its head-zero boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def slot : Fin 1→Fin 61 := ![60]
noncomputable def shift (move : HeadMove) := RecoveryFocus.machine slot
  (Completion.PhysicalDriverMoves.machine 1 move)
def H (heads : Fin 60→Nat) (pos : Nat) : Fin 61→Nat := Fin.addCases (m:=60) (n:=1) (motive:=fun _=>Nat) heads (fun _ : Fin 1=>pos)
def A (tapes : Fin 60→List Bool) (d C : Nat) : Fin 61→List Bool :=
  Fin.addCases (m:=60) (n:=1) (motive:=fun _=>List Bool) tapes (fun _ : Fin 1=>ZeroPadding.pad C (CompareMachine.word d))

theorem shift_run (move : HeadMove) (heads : Fin 60→Nat) (tapes : Fin 60→List Bool) (d C pos : Nat) :
    Step (shift move) 1 (H heads pos) (A tapes d C)
      (H heads (HeadMove.apply move pos)) (A tapes d C) := by
  apply PhysicalFocusBoundary.focus (Completion.PhysicalDriverMoves.run move
    (fun _ : Fin 1=>pos) (fun _=>ZeroPadding.pad C (CompareMachine.word d))) slot (by decide)
    (H heads pos) (H heads (HeadMove.apply move pos)) _ _
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i
    refine Fin.addCases (m:=60) (n:=1) (fun _ _=>⟨by simp only [H,Fin.addCases_left],rfl⟩) (fun j away=>?_) i
    fin_cases j
    exact False.elim (away 0 rfl)

noncomputable def machine := Composition.machine
  (Composition.machine (shift .right) DescendingWindow.machine) (shift .left)
def budget (u d C : Nat) := DescendingWindow.budget u d C+4

theorem run (v u M offset d target C old : Nat) (oldNonzero oldGuard : Bool) (out : List Bool)
    (hfit : offset+d<2^u) (hd : d+1<2^u) (ht : target<2^u) (hscalar : 2*u≤C)
    (hMv : M≤2^v) (hmeta : 2*v+d+3≤C)
    (hC : ∀k≤d,CloseoutRowsModeElementary.budget v k M+1≤C) :
    Step machine (budget u d C)
      (H (DescendingWindow.H v M offset d target out 0) 0)
      (A (DescendingWindow.A v u M offset d target C old oldNonzero oldGuard out 0) (d+1) C)
      (H (DescendingWindow.H v M offset d target out (d+1)) 0)
      (A (DescendingWindow.A v u M offset d target C old oldNonzero oldGuard out (d+1)) (d+1) C) := by
  have loop := DescendingWindow.run v u M offset d target C old oldNonzero oldGuard out
    hfit hd ht hscalar hMv hmeta hC
  let caps : Fin 61→Nat := Fin.addCases (m:=60) (n:=1) (motive:=fun _=>Nat) (fun _ : Fin 60=>0) (fun _ : Fin 1=>C)
  have padded := loop.pad caps
  have padded' : Step DescendingWindow.machine (DescendingWindow.budget u d C)
      (H (DescendingWindow.H v M offset d target out 0) 1)
      (A (DescendingWindow.A v u M offset d target C old oldNonzero oldGuard out 0) (d+1) C)
      (H (DescendingWindow.H v M offset d target out (d+1)) 1)
      (A (DescendingWindow.A v u M offset d target C old oldNonzero oldGuard out (d+1)) (d+1) C) := by
    convert padded using 1
    all_goals funext i
    all_goals refine Fin.addCases (m:=60) (n:=1) (fun _=>?_) (fun _=>?_) i
    all_goals simp [caps,A,H]
  have up := shift_run .right (DescendingWindow.H v M offset d target out 0)
    (DescendingWindow.A v u M offset d target C old oldNonzero oldGuard out 0) (d+1) C 0
  have down := shift_run .left (DescendingWindow.H v M offset d target out (d+1))
    (DescendingWindow.A v u M offset d target C old oldNonzero oldGuard out (d+1)) (d+1) C 1
  have whole := (up.seq padded').seq down
  convert whole using 1 <;> first | rfl | (unfold budget;omega)

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowReady
