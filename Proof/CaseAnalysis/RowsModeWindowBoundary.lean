import Proof.CaseAnalysis.RowsModeWindowConstant

/-! Changing the live raw output changes only tape 44 and its actual cursor;
the original numeric and scalar masters are retained in every branch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowLayout
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_tape (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) :
    data v u M a offset b scratch degree target C nonzero guard out 44=out:=by
  change CloseoutRowsModeElementaryReusable.paddedBlank v a M C out 44=out
  rw [CloseoutRowsModeElementaryReusable.paddedBlank,CloseoutRowsModeElementaryLayout.blank_eq]
  exact ZeroPadding.pad_zero _

theorem flat_other (v a M C : Nat) (out next : List Bool) (i : Fin 52) (hi : i≠44) :
    CloseoutRowsModeElementaryLayout.flatBlank v a M C next i=
      CloseoutRowsModeElementaryLayout.flatBlank v a M C out i:=by
  fin_cases i <;> first | rfl | exact False.elim (hi rfl)

theorem core_other (v a M C : Nat) (out next : List Bool) (i : Fin 52) (hi : i≠44) :
    CloseoutRowsModeElementaryReusable.paddedBlank v a M C next i=
      CloseoutRowsModeElementaryReusable.paddedBlank v a M C out i:=by
  unfold CloseoutRowsModeElementaryReusable.paddedBlank
  rw [CloseoutRowsModeElementaryLayout.blank_eq,CloseoutRowsModeElementaryLayout.blank_eq]
  exact congrArg _ (flat_other v a M C out next i hi)

theorem other_tape (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out next : List Bool) (i : Fin 60) (hi : i≠44) :
    data v u M a offset b scratch degree target C nonzero guard next i=
      data v u M a offset b scratch degree target C nonzero guard out i:=by
  unfold data
  simp only [Fin.addCases]
  split
  · rename_i h
    apply core_other
    intro e
    apply hi
    apply Fin.ext
    exact congrArg (fun x : Fin 52=>x.val) e
  · rfl

theorem output_update (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out next : List Bool) :
    Function.update (data v u M a offset b scratch degree target C nonzero guard out) 44 next=
      data v u M a offset b scratch degree target C nonzero guard next:=by
  funext i
  by_cases hi:i=44
  · subst i;rw [Function.update_self,output_tape]
  · rw [Function.update_of_ne hi]
    exact (other_tape _ _ _ _ _ _ _ _ _ _ _ _ _ _ i hi).symm

theorem heads_update (out next : List Bool) : Function.update (heads out) 44 next.length=heads next:=by
  funext i;fin_cases i <;> simp [heads,CloseoutRowsModeElementaryLayout.heads,Fin.addCases]

theorem constant_run (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) :
    Step CloseoutRowsModeWindowConstant.machine 2 (heads out)
      (data v u M a offset b scratch degree target C nonzero guard out)
      (heads (out++[true,false]))
      (data v u M a offset b scratch degree target C nonzero guard (out++[true,false])):=by
  exact (CloseoutRowsModeWindowConstant.append_run _ _ out (by rfl)
    (output_tape _ _ _ _ _ _ _ _ _ _ _ _ _)).congr (heads_update _ _) (output_update _ _ _ _ _ _ _ _ _ _ _ _ _ _)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowLayout
