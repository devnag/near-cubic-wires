import Proof.CaseAnalysis.RowsModeWindowCounterLayout

/-! Small retained-bank identities avoid unfolding the completed window
machines while transporting their physical boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowBankFacts
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open CloseoutRowsModeWindowLayout

theorem raw_tape (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) :
    data v u M a offset b scratch degree target C nonzero guard out 50=List.replicate C true := by
  change CloseoutRowsModeElementaryReusable.paddedBlank v a M C out 50=_
  rw [CloseoutRowsModeElementaryReusable.paddedBlank,CloseoutRowsModeElementaryLayout.blank_eq]
  change ZeroPadding.pad 0 (List.replicate C true)=_
  exact ZeroPadding.pad_zero _

theorem log_tape (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) :
    data v u M a offset b scratch degree target C nonzero guard out 51=List.replicate (C+1) false := by
  change CloseoutRowsModeElementaryReusable.paddedBlank v a M C out 51=_
  rw [CloseoutRowsModeElementaryReusable.paddedBlank,CloseoutRowsModeElementaryLayout.blank_eq]
  change ZeroPadding.pad 0 (List.replicate (C+1) false)=_
  exact ZeroPadding.pad_zero _

theorem inner_other (v u M a offset b b' scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) (i : Fin 60) (hi : i≠53) :
    data v u M a offset b scratch degree target C nonzero guard out i=
      data v u M a offset b' scratch degree target C nonzero guard out i := by
  revert hi
  refine Fin.addCases (m:=52) (n:=8) (fun j _=>?_) (fun j away=>?_) i
  · simp only [data,Fin.addCases_left]
  · simp only [data,Fin.addCases_right]
    fin_cases j
    all_goals first
      | exact False.elim (away rfl)
      | simp [extra,scalars,CloseoutRowsModeWindowGuard.data,
          CloseoutRowsModeWindowGuard.extra,CloseoutRowsModeShift.data,Fin.addCases]

theorem outer_other (v u M a offset b scratch degree degree' target C : Nat)
    (nonzero guard : Bool) (out : List Bool) (i : Fin 60) (hi : i≠57) :
    data v u M a offset b scratch degree target C nonzero guard out i=
      data v u M a offset b scratch degree' target C nonzero guard out i := by
  revert hi
  refine Fin.addCases (m:=52) (n:=8) (fun j _=>?_) (fun j away=>?_) i
  · simp only [data,Fin.addCases_left]
  · simp only [data,Fin.addCases_right]
    fin_cases j
    all_goals first
      | exact False.elim (away rfl)
      | simp [extra,scalars,CloseoutRowsModeWindowGuard.data,
          CloseoutRowsModeWindowGuard.extra,CloseoutRowsModeShift.data,Fin.addCases]

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowBankFacts
