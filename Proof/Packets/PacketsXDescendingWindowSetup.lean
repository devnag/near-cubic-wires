import Proof.Packets.DescendingWindowPrepare
import Proof.Packets.PacketsXWindowBankFacts

/-! Paid descending-antidiagonal setup docked into the actual retained
sixty-tape elementary/scalar bank, plus its one physical count tape. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowSetup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeWindowLayout

def slots : Fin 5→Fin 61 := ![48,53,60,50,51]
def H (out : List Bool) : Fin 61→Nat := Fin.addCases (m:=60) (n:=1) (motive:=fun _=>Nat) (heads out) (fun _ : Fin 1=>0)
noncomputable def A (v u M a offset b scratch d target C count : Nat)
    (nonzero guard : Bool) (out : List Bool) : Fin 61→List Bool :=
  Fin.addCases (m:=60) (n:=1) (motive:=fun _=>List Bool) (data v u M a offset b scratch d target C nonzero guard out)
    (fun _ : Fin 1=>ZeroPadding.pad C (CompareMachine.word count))
noncomputable def machine := RecoveryFocus.machine slots DescendingWindowPrepare.machine

theorem run (v u M a offset b scratch d target C : Nat) (nonzero guard : Bool) (out : List Bool)
    (ha : a+1≤C) (hd : d+1≤C) (hu : 2*u≤C) :
    Step machine (4*C+4*u+2*d+21) (H out)
      (A v u M a offset b scratch d target C d nonzero guard out) (H out)
      (A v u M d offset 0 scratch d target C (d+1) nonzero guard out) := by
  have localRun := DescendingWindowPrepare.run u (ZeroPadding.pad C (CompareMachine.word a)) b d C
    (by simp [CompareMachine.word,ha]) hd hu
  apply PhysicalFocusBoundary.focus localRun slots (by decide) (H out) (H out) _ _
  · intro i;fin_cases i <;>simp [H,slots,heads,CloseoutRowsModeElementaryLayout.heads,Fin.addCases]
  · intro i;fin_cases i
    · change ZeroPadding.pad C (CompareMachine.word a)=A v u M a offset b scratch d target C d nonzero guard out ((48 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      exact (CloseoutRowsModeWindowCounter.degree_tape v u M a offset b scratch d target C nonzero guard out).symm
    · change ZeroPadding.pad C (frame (SignedSortKey.binary u b))=A v u M a offset b scratch d target C d nonzero guard out ((53 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      rfl
    · change ZeroPadding.pad C (CompareMachine.word d)=A v u M a offset b scratch d target C d nonzero guard out (Fin.natAdd 60 (0 : Fin 1))
      rw [A,Fin.addCases_right]
    · change List.replicate C true=A v u M a offset b scratch d target C d nonzero guard out ((50 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      exact (WindowBankFacts.raw_tape v u M a offset b scratch d target C nonzero guard out).symm
    · change List.replicate (C+1) false=A v u M a offset b scratch d target C d nonzero guard out ((51 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      exact (WindowBankFacts.log_tape v u M a offset b scratch d target C nonzero guard out).symm
  · intro i;fin_cases i <;>simp [H,slots,heads,CloseoutRowsModeElementaryLayout.heads,Fin.addCases]
  · intro i;fin_cases i
    · change ZeroPadding.pad C (CompareMachine.word d)=A v u M d offset 0 scratch d target C (d+1) nonzero guard out ((48 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      exact (CloseoutRowsModeWindowCounter.degree_tape v u M d offset 0 scratch d target C nonzero guard out).symm
    · change ZeroPadding.pad C (frame (SignedSortKey.binary u 0))=A v u M d offset 0 scratch d target C (d+1) nonzero guard out ((53 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      rfl
    · change ZeroPadding.pad C (CompareMachine.word (d+1))=A v u M d offset 0 scratch d target C (d+1) nonzero guard out (Fin.natAdd 60 (0 : Fin 1))
      rw [A,Fin.addCases_right]
    · change List.replicate C true=A v u M d offset 0 scratch d target C (d+1) nonzero guard out ((50 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      exact (WindowBankFacts.raw_tape v u M d offset 0 scratch d target C nonzero guard out).symm
    · change List.replicate (C+1) false=A v u M d offset 0 scratch d target C (d+1) nonzero guard out ((51 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      exact (WindowBankFacts.log_tape v u M d offset 0 scratch d target C nonzero guard out).symm
  · intro i
    refine Fin.addCases (m:=60) (n:=1) (fun j away=>?_) (fun j away=>?_) i
    · refine ⟨rfl,?_⟩
      have hj : j≠48 := by intro he;subst j;exact away 0 rfl
      simp only [A,Fin.addCases_left]
      change data v u M a offset b scratch d target C nonzero guard out j=
        data v u M d offset 0 scratch d target C nonzero guard out j
      rw [CloseoutRowsModeWindowCounter.degree_other v u M a d offset b scratch d target C nonzero guard out j hj]
      exact WindowBankFacts.inner_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ j (by
        intro he;subst j;exact away 1 rfl)
    · fin_cases j
      exact False.elim (away 2 rfl)

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowSetup
