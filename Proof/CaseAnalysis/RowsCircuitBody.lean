import Proof.CaseAnalysis.RowsCircuitPreparedRun
import Proof.CaseAnalysis.RowsCircuitTraversalCaps

/-! The complete post-top circuit body publishes the native count and top,
traverses the actual bottom list, returns its private cursors, and decides
both original resource bounds. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBody
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CloseoutRowsCircuit CloseoutRowsCircuitBottomDock CloseoutRowsCircuitBottomLoop
open CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (threshold : Bool):=CloseoutRowsGateColdPair.machine
  (CloseoutRowsCircuitPreparedRun.machine threshold) (CloseoutRowsCircuitTraversalCaps.machine threshold) (fun _=>true)

theorem outside_heads (threshold : Bool) (out : List Bool) (D W : ℕ) (i : Fin 1703)
    (outside : ∀ j,bottomSlots j≠i) :
    CloseoutRowsCircuitBottomPosition.output (CloseoutRowsCircuitBottomEntry.heads threshold out D W) i=0:=by
  have ncore:i≠1674:=Ne.symm (outside 1035)
  have nnative:i≠1688:=Ne.symm (outside 1049)
  have ndesc:i≠1689:=Ne.symm (outside 1050)
  have nwire:i≠1690:=Ne.symm (outside 1051)
  have nmember:i≠1692:=Ne.symm (outside 1053)
  have ncount:i≠624:=Ne.symm (outside 1059)
  simp only [CloseoutRowsCircuitBottomPosition.output,Function.update_of_ne ncount,
    Function.update_of_ne nmember,CloseoutRowsCircuitBottomEntry.heads,if_neg ncore,
    if_neg nnative,if_neg ndesc,if_neg nwire,if_neg ncount]

theorem outside_keep (A B : Fin 1703 → List Bool)
    (keep : ∀ i,(i.val<639 ∨ 1687 < i.val ∨ i.val=1674) → i≠1694 → i≠1695 → i≠1688 → i≠1696 → B i=A i)
    (i : Fin 1703) (outside : ∀ j,bottomSlots j≠i) : B i=A i:=by
  apply keep i _ (Ne.symm (outside 1055)) (Ne.symm (outside 1056))
    (Ne.symm (outside 1049)) (Ne.symm (outside 1057))
  by_cases lo:i.val<639
  · exact Or.inl lo
  by_cases hi:1687 < i.val
  · exact Or.inr (Or.inl hi)
  have bad:=outside ⟨i.val-639,by omega⟩
  apply False.elim
  apply bad
  apply Fin.ext
  rw [bottom_val]
  dsimp only
  split_ifs <;> omega



end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBody
