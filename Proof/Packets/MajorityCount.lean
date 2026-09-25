import Proof.Rows.CycleCellBitCount

/-! Actual truth-assignment popcount in the sentinel representation consumed
by the unary majority comparator. The assignment and length driver remain
resident, and all heads are returned to their original positions. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open Theorem25Completion.CycleCellBitCount

def boot : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,![.stay,.right,.stay]⟩ else none

theorem boot_run (a : Fin 3→List Bool) :
    Step boot 1 (![0,0,1] : Fin 3→Nat) a (![0,1,1] : Fin 3→Nat) a := by
  have hs : step boot (⟨0,![0,0,1],a⟩ : Configuration 3 2)=some ⟨1,![0,1,1],a⟩ := by
    simp [step,boot]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

noncomputable def core:=Composition.machine boot Theorem25Completion.CycleCellBitCount.machine
noncomputable def machine:=MaskedReset.machine core selected

theorem run (bits : List Bool) (R : Nat) (hR : 4*bits.length+5≤R) :
    Step machine (8*bits.length+12) (![0,0,1,0] : Fin 4→Nat)
      ![ZeroPadding.pad R bits,List.replicate R false,
        ZeroPadding.pad R (CompareMachine.word bits.length),List.replicate R false]
      (![0,0,1,0] : Fin 4→Nat)
      ![ZeroPadding.pad R bits,ZeroPadding.pad R (CompareMachine.word (marks bits).length),
        ZeroPadding.pad R (CompareMachine.word bits.length),List.replicate R false] := by
  have raw:=(boot_run (![bits,[false],CompareMachine.word bits.length] : Fin 3→List Bool)).seq (scan_run bits [false])
  have h:=(raw.pad (fun _ : Fin 3=>R)).mask selected
    (by intro i hi;fin_cases i <;>first | rfl | contradiction) (by omega : 1+1+(4*bits.length+3)≤R)
  rw [show 2*(1+1+(4*bits.length+3))+2=8*bits.length+12 by omega] at h
  have word : [false]++marks bits=CompareMachine.word (marks bits).length:=by
    conv_lhs => rw [marks_eq]
    rfl
  have zero : ZeroPadding.pad R [false]=List.replicate R false:=by
    simp only [ZeroPadding.pad,List.length_singleton,List.singleton_append]
    rw [←List.replicate_succ]
    congr 1
    omega
  rw [word] at h
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>simp [zero,Fin.addCases,selected]

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityCount
