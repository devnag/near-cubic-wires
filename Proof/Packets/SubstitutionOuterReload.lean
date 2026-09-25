import Proof.Packets.SubstitutionOuterData
import Proof.Packets.PhysicalIndexReload

/-! Paid restoration of the literal index between monomials. The resident
common-width template is copied only after lowering the actual index head. -/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def reload := PhysicalIndexReload.machine (31 : Fin 43) 24 35

theorem A_index_outside (C R index index' : Nat) (left right : Packet)
    (atoms source : List Bool) (stored : Packet) (i : Fin 43) (hi : i≠35) :
    A C R index left right atoms source stored i=A C R index' left right atoms source stored i := by
  revert hi
  refine Fin.addCases (m:=34) (n:=9) (fun j=>?_) (fun j=>?_) i
  · intro _;rw [A_core,A_core]
  · intro hi
    rw [A_extra,A_extra]
    fin_cases j
    · rfl
    · exact False.elim (hi rfl)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

theorem reload_data (C R index : Nat) (left right : Packet) (atoms source : List Bool) (stored : Packet)
    (hC : C+2≤R) :
    Function.update (A C R index left right atoms source stored) 35
      (A C R index left right atoms source stored 24)=A C R C left right atoms source stored := by
  funext i
  by_cases hi : i=35
  · subst i
    rw [Function.update_self]
    change ZeroPadding.pad R (UnaryTemplate.tape C)=ZeroPadding.pad R (CompareMachine.word C)
    exact PhysicalIndexReload.padded_unary_index C R hC
  · rw [Function.update_of_ne hi]
    exact A_index_outside C R index C left right atoms source stored i hi

theorem reload_run (C R index position : Nat) (left right : Packet) (atoms source : List Bool) (stored : Packet)
    (hC : C+2≤R) (hi : index+1≤R) :
    Step reload (2*R+6) (H position 1) (A C R index left right atoms source stored)
      (H position 1) (A C R C left right atoms source stored) := by
  have hs : (A C R index left right atoms source stored 24).length=R := by
    change (ZeroPadding.pad R (UnaryTemplate.tape C)).length=R
    rw [ZeroPadding.pad_length,Nat.max_eq_left (by simpa only [UnaryTemplate.tape_length] using hC)]
  have ht : (A C R index left right atoms source stored 35).length=R := by
    change (ZeroPadding.pad R (CompareMachine.word index)).length=R
    rw [ZeroPadding.pad_length,Nat.max_eq_left (by simpa only [CompareMachine.word,List.length_cons,List.length_replicate] using hi)]
  have h:=PhysicalIndexReload.run R (31 : Fin 43) 24 35 (by decide) (by decide) (by decide)
    (H position 1) (A C R index left right atoms source stored) rfl rfl rfl rfl hs ht
  exact h.congr rfl (reload_data C R index left right atoms source stored hC)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
