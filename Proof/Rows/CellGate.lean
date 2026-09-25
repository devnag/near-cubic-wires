import Proof.Rows.CellGatePalette

/-! Actual paid gate call from eight resident masters. Fanout constructs the
entire evaluator bank, the canonical native evaluator appends its verdict,
and a bounded sweep restores the exact cleared bank for the next call. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CellGate
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open NearCubicWires.RepairRepresentation
open PCJ45bee56da9f34d5a_CellGatePalette
noncomputable section
attribute [local irreducible] OffsetSourceGate.machine

def move (up : Bool) := RecoveryFocus.machine gates (HardwireReusable.move up)
def evaluate := RecoveryFocus.machine gates OffsetSourceGate.machine
def wipeSlots (i : Fin 99) : Fin 108 := ⟨8+i.val,by omega⟩
theorem wipe_injective : Function.Injective wipeSlots := by
  intro i j h;apply Fin.ext
  have h:=congrArg Fin.val h
  simp only [wipeSlots] at h
  omega
def wipe := RecoveryFocus.machine wipeSlots (RecoveryScratchErase.resetMachine 97)
def machine := Composition.machine fanout (Composition.machine (move true)
  (Composition.machine evaluate (Composition.machine (move false) wipe)))

theorem dock_heads (out next : List Bool) (a b : Nat) :
    dockH gates (heads out a) (HardwireReusable.heads next b)=heads next b := by
  funext i
  by_cases hi:∃j,gates j=i
  · obtain ⟨j,rfl⟩:=hi
    rw [dockH_slot _ gates_injective,head_gate]
  · rw [dockH_other _ _ _ _ (by simpa using hi)]
    have h107:i≠107 := fun h=>hi ⟨34,h.symm⟩
    have h49:i≠49 := fun h=>hi ⟨42,h.symm⟩
    have h53:i≠53 := fun h=>hi ⟨46,h.symm⟩
    simp [heads,h107,h49,h53]

theorem install_warm (palette : Fin 8→List Bool) (U : Nat) (out next : List Bool)
    (A : Fin 98→List Bool) (ha : ∀j,A j=warm palette U next (gates j)) :
    install gates (warm palette U out) A=warm palette U next := by
  apply HierarchyAllocation.install_eq gates gates_injective
  · intro j;exact (ha j).symm
  · intro i hi
    have h107:i≠107 := fun h=>hi 34 h.symm
    fin_cases i <;>first |rfl |contradiction

theorem move_run (up : Bool) (palette : Fin 8→List Bool) (U : Nat) (out : List Bool) :
    Step (move up) 1 (heads out (if up then 0 else 1)) (warm palette U out)
      (heads out (if up then 1 else 0)) (warm palette U out) := by
  have h := (HardwireReusable.move_run up out (fun j=>warm palette U out (gates j))).dock
    gates gates_injective (heads out (if up then 0 else 1)) (warm palette U out)
    (head_gate out _) (fun _=>rfl)
  exact h.congr (dock_heads _ _ _ _) (install_existing _ _ _ (fun _=>rfl))

theorem wipe_run (palette : Fin 8→List Bool) (U : Nat) (out : List Bool)
    (hU : ∀i,(palette i).length≤U) :
    Step wipe (2*U+4) (heads out 0) (warm palette U out)
      (heads out 0) (cold palette U out) := by
  let dirty : Fin 97→List Bool:=fun i=>ZeroPadding.pad U (NativeFanout.word choice palette i)
  have hd : ∀i,(dirty i).length≤U := by
    intro i
    rw [ZeroPadding.pad_length]
    apply max_le le_rfl
    change ((choice i).elim [] palette).length≤U
    cases choice i with
    | none=>exact Nat.zero_le _
    | some j=>exact hU j
  have base : Step (RecoveryScratchErase.resetMachine 97) (2*U+4) (fun _=>0)
      (PCJ45bee56da9f34d5a_Plan.clearInput U (U+1) dirty) (fun _=>0)
      (PCJ45bee56da9f34d5a_Plan.clearOutput 97 U (U+1)) := by
    unfold PCJ45bee56da9f34d5a_Plan.clearOutput PCJ45bee56da9f34d5a_Plan.clearInput
    simpa only [Nat.max_self] using Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) dirty hd)
  have h:=base.dock wipeSlots wipe_injective (heads out 0) (warm palette U out)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply h.congr
  · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
  · apply HierarchyAllocation.install_eq wipeSlots wipe_injective
    · intro i;fin_cases i <;>rfl
    · intro i hi
      have hr : i.val<8 ∨ i=107 := by
        by_contra hn
        push Not at hn
        have hit : i.val<107 := by omega
        exact hi ⟨i.val-8,by omega⟩ (Fin.ext (by simp only [wipeSlots];omega))
      rcases hr with hr|rfl
      · fin_cases i <;>first |rfl |norm_num at hr
      · rfl

end
end PCJ45bee56da9f34d5a_CellGate
