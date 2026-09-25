import Proof.Rows.RowsFrameSymWork
import Proof.Rows.RowsSymLoop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.FrameSymInst
open NearCubicWires NearCubicWires.RepairRepresentation

/-- **RS's SYM loop block** as the typed input of `symSpecOf`. -/
noncomputable def symLoop (a : DecompositionAlgorithm) : RowsInit.FrameSymWork.SymLoopIn a where
  need := RowsInit.SymLoop.need a
  states := _
  machine := RowsInit.SymLoop.machine a
  cost := RowsInit.SymLoop.cost a
  loop_run := fun NI o hNI => RowsInit.SymLoop.loop_run a NI o hNI

/-- **RX's `SymSpec`, closed** (every `NI oB` with `150 ≤ oB`, `oB + needS ≤ NI`). -/
noncomputable def symSpec (a : DecompositionAlgorithm) (NI oB : ℕ) (h : 146 ≤ NI) (hB : 150 ≤ oB)
    (hS : oB + RowsInit.FrameSymWork.needS a (symLoop a) ≤ NI) : RowsInit.WorkPhase.SymSpec a NI oB h :=
  RowsInit.FrameSymWork.symSpecOf a (symLoop a) NI oB h hB hS

end RowsInit.FrameSymInst
