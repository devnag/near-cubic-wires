import Proof.Packets.PacketsXDescendingWindowSetup

/-! Physical advance of the retained outer binary degree. The completed
inner loop's zero unary coordinate is retained and all local heads return. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowDegree
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsModeWindowLayout
open DescendingWindowSetup (H A)
attribute [local irreducible] DescendingWindowCounters.binaryPart

def slots : Fin 3→Fin 61 := ![48,57,51]
noncomputable def machine := RecoveryFocus.machine slots DescendingWindowCounters.binaryPart

theorem run (v u M offset b scratch d target C count : Nat) (nonzero guard : Bool) (out : List Bool)
    (hd : d+1<2^u) (hu : 2*u≤C) :
    Step machine (4*u+2) (H out)
      (A v u M 0 offset b scratch d target C count nonzero guard out) (H out)
      (A v u M 0 offset b scratch (d+1) target C count nonzero guard out) := by
  have localRun := DescendingWindowCounters.binaryPart_run u 0 d C hd hu
  apply PhysicalFocusBoundary.focus localRun slots (by decide) (H out) (H out) _ _
  · intro i;fin_cases i <;>simp [H,slots,heads,CloseoutRowsModeElementaryLayout.heads,Fin.addCases]
  · intro i;fin_cases i
    · change ZeroPadding.pad C (NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word 0)=A v u M 0 offset b scratch d target C count nonzero guard out ((48 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      exact (CloseoutRowsModeWindowCounter.degree_tape v u M 0 offset b scratch d target C nonzero guard out).symm
    · change ZeroPadding.pad C (frame (SignedSortKey.binary u d))=A v u M 0 offset b scratch d target C count nonzero guard out ((57 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      rfl
    · change List.replicate (C+1) false=A v u M 0 offset b scratch d target C count nonzero guard out ((51 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      exact (WindowBankFacts.log_tape v u M 0 offset b scratch d target C nonzero guard out).symm
  · intro i;fin_cases i <;>simp [H,slots,heads,CloseoutRowsModeElementaryLayout.heads,Fin.addCases]
  · intro i;fin_cases i
    · change ZeroPadding.pad C (NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word 0)=A v u M 0 offset b scratch (d+1) target C count nonzero guard out ((48 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      exact (CloseoutRowsModeWindowCounter.degree_tape v u M 0 offset b scratch (d+1) target C nonzero guard out).symm
    · change ZeroPadding.pad C (frame (SignedSortKey.binary u (d+1)))=A v u M 0 offset b scratch (d+1) target C count nonzero guard out ((57 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      rfl
    · change List.replicate (C+1) false=A v u M 0 offset b scratch (d+1) target C count nonzero guard out ((51 : Fin 60).castAdd 1)
      rw [A,Fin.addCases_left]
      exact (WindowBankFacts.log_tape v u M 0 offset b scratch (d+1) target C nonzero guard out).symm
  · intro i
    refine Fin.addCases (m:=60) (n:=1) (fun j away=>?_) (fun _ _=>⟨rfl,by simp only [A,Fin.addCases_right]⟩) i
    refine ⟨rfl,?_⟩
    simp only [A,Fin.addCases_left]
    exact WindowBankFacts.outer_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ j (by
      intro he;subst j;exact away 1 rfl)

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowDegree
