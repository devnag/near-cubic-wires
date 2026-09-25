import Proof.Packets.WalkTranscriptColumnArena

/-! Frame laws for the sole shared column bank in the 471-tape worker.
They keep the direct extraction/majority/reset proof independent of the
large machines' implementation and private tape expressions. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace Theorem25Completion.WalkTranscriptColumnArena
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
noncomputable section

theorem column_not_majority_private (j : Fin 137) (hj : j≠44) :
    ∀i,columnSlots i≠majoritySlots j := by
  intro i he
  exact hj (source_only_overlap i j he).2

theorem majority_not_column_private (i : Fin 9) (hi : i≠6) :
    ∀j,majoritySlots j≠columnSlots i := by
  intro j he
  exact hi (source_only_overlap i j he.symm).1

theorem column_install_majority_private (A : Fin 471→List Bool) (a : Fin 9→List Bool)
    (j : Fin 137) (hj : j≠44) :
    install columnSlots A a (majoritySlots j)=A (majoritySlots j) :=
  install_other columnSlots A a _ (column_not_majority_private j hj)

theorem majority_install_column_private (A : Fin 471→List Bool) (a : Fin 137→List Bool)
    (i : Fin 9) (hi : i≠6) :
    install majoritySlots A a (columnSlots i)=A (columnSlots i) :=
  install_other majoritySlots A a _ (majority_not_column_private i hi)

theorem majority_install_source (A : Fin 471→List Bool) (a : Fin 137→List Bool) :
    install majoritySlots A a (columnSlots 6)=a 44 := by
  rw [←majority_source,install_slot majoritySlots majority_injective]

theorem majority_keeps_column (A : Fin 471→List Bool) (a : Fin 137→List Bool)
    (hs : a 44=A (columnSlots 6)) (i : Fin 9) :
    install majoritySlots A a (columnSlots i)=A (columnSlots i) := by
  by_cases hi : i=6
  · subst i;rw [majority_install_source,hs]
  · exact majority_install_column_private A a i hi

theorem column_install_result (A : Fin 471→List Bool) (a : Fin 9→List Bool) :
    install columnSlots A a 29=A 29 := install_other _ _ _ _ column_away_result

theorem majority_install_result (A : Fin 471→List Bool) (a : Fin 137→List Bool) :
    install majoritySlots A a 29=A 29 := install_other _ _ _ _ majority_away_result

end
end Theorem25Completion.WalkTranscriptColumnArena
