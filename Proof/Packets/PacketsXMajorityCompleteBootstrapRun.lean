import Proof.Packets.PacketsXMajorityCompleteBootstrapLayout
import Proof.Packets.CycleCommonReserve

/-! Actual fanout, head positioning, erasure and reload for the reusable
majority arena. Every reset sweep uses the resident quadratic unary driver. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Bootstrap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open Completion.SourceDock Theorem25Completion
noncomputable section

def erase := RecoveryFocus.machine fanoutSlots
  (PhysicalPrepend.machine 10 (RecoveryScratchErase.resetMachine 123))
def reset := Composition.machine lower (Composition.machine erase (Composition.machine fanout raise))

theorem head_slots_injective : Function.Injective headSlots := by decide

theorem raise_run (A : Fin 137→List Bool) : Step raise 1 baseH A heads A := by
  apply PhysicalFocusBoundary.focus
    (Completion.PhysicalDriverMoves.run .right (fun _ : Fin 10=>0) (fun j=>A (headSlots j)))
    headSlots head_slots_injective
  · intro j;fin_cases j <;>rfl
  · intros;rfl
  · intro j;fin_cases j <;>rfl
  · intros;rfl
  · intro i hi
    refine ⟨?_,rfl⟩
    have all : ∀i:Fin 137,(∀j,headSlots j≠i)→baseH i=heads i := by decide
    exact all i hi

theorem lower_run (A : Fin 137→List Bool) : Step lower 1 heads A baseH A := by
  apply PhysicalFocusBoundary.focus
    (Completion.PhysicalDriverMoves.run .left (fun _ : Fin 10=>1) (fun j=>A (headSlots j)))
    headSlots head_slots_injective
  · intro j;fin_cases j <;>rfl
  · intros;rfl
  · intro j;fin_cases j <;>rfl
  · intros;rfl
  · intro i hi
    refine ⟨?_,rfl⟩
    have all : ∀i:Fin 137,(∀j,headSlots j≠i)→heads i=baseH i := by decide
    exact all i hi

private theorem pack_assoc (palette : Fin 10→List Bool) (S : Nat) (work : Fin 123→List Bool) :
    Fin.append palette (Fin.append (Fin.append work (fun _ : Fin 1=>List.replicate S true))
      (fun _ : Fin 1=>List.replicate (S+1) false))=pack palette S work := by
  funext i
  fin_cases i <;>rfl

private theorem zero_append (e t : Nat) :
    Fin.addCases (m:=e) (n:=t) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)=(fun _=>0) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left]
  · simp only [Fin.addCases_right]

theorem erase_run (palette : Fin 10→List Bool) (S : Nat) (source : List Bool)
    (work : Fin 123→List Bool) (hw : ∀i,(work i).length≤S) :
    Step erase (2*S+4) baseH (data palette S source work)
      baseH (data palette S source (fun _=>List.replicate S false)) := by
  have localRun:=Step.of_ready (RecoveryScratchErase.erase_ready S (S+1) work hw)
  simp only [max_self] at localRun
  have prefixed:=PhysicalPrepend.run localRun (fun _ : Fin 10=>0) palette
  simp only [zero_append] at prefixed
  change Step _ _ _
    (Fin.append palette (Fin.append (Fin.append work (fun _ : Fin 1=>List.replicate S true))
      (fun _ : Fin 1=>List.replicate (S+1) false))) _
    (Fin.append palette (Fin.append (Fin.append (fun _ : Fin 123=>List.replicate S false)
      (fun _ : Fin 1=>List.replicate S true)) (fun _ : Fin 1=>List.replicate (S+1) false))) at prefixed
  simp only [pack_assoc] at prefixed
  have hr:=prefixed.focus fanoutSlots fanout_injective baseH (base S source)
  rw [dock_base_heads] at hr
  exact hr

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Bootstrap
