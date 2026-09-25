import Proof.Packets.PacketsXMajorityCompleteBootstrapLayout

/-! Change the shared source column after a majority reset. Every column
has the same visit count, so the scalar palette and all initialized private
words are literally unchanged; only the raw source-bank tape differs. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option warningAsError true
namespace Theorem25Completion.WalkTranscriptColumnMajoritySource
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open MajorityComplete.Bootstrap
noncomputable section

private theorem install_update_other {t u : Nat} (ports : Fin t→Fin u)
    (A : Fin u→List Bool) (a : Fin t→List Bool) (i : Fin u) (word : List Bool)
    (hi : ∀j,ports j≠i) :
    install ports (Function.update A i word) a=Function.update (install ports A a) i word := by
  funext k
  by_cases hk : k=i
  · subst k;rw [install_other _ _ _ _ hi,Function.update_self,Function.update_self]
  · rw [Function.update_of_ne hk]
    unfold install
    cases RecoveryFocus.pick ports k <;>simp only [Function.update_of_ne hk]

private theorem base_source (S : Nat) (old source : List Bool) :
    base S source=Function.update (base S old) 44 source := by
  funext i
  by_cases hi : i=44
  · subst i;rfl
  · simp only [base,Function.update_of_ne hi,if_neg hi]

theorem data_source (palette : Fin 10→List Bool) (S : Nat) (old source : List Bool)
    (work : Fin 123→List Bool) :
    data palette S source work=Function.update (data palette S old work) 44 source := by
  rw [data,base_source S old source,install_update_other _ _ _ _ _ fanout_not_source]
  rfl

theorem ready_work_same_length (C R S : Nat) (ps qs : List (Ring.Poly Nat))
    (hRS : R+3≤S) (hC : C≤S) (hlen : ps.length=qs.length) :
    readyWork C R S ps=readyWork C R S qs := by
  funext i
  dsimp only [readyWork]
  rw [←MajorityComplete.Palette.private_word C R S ps hRS hC,
    ←MajorityComplete.Palette.private_word C R S qs hRS hC,hlen]

end
end Theorem25Completion.WalkTranscriptColumnMajoritySource
