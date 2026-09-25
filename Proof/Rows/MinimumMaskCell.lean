import Proof.Rows.CircuitCountCopy
import Proof.Rows.MinimumAssignment

/-! One actual minimizing-mask cell reads the native coefficient sign and skips
its magnitude with the paid native field parser. Source and input bits survive. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_MinimumMaskCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey RecoveryExecution Streaming StablePartition.Workspace
noncomputable section

def heads (pos j len : Nat) : Fin 5 → Nat := ![pos,0,j,j,len]
def bank (source scratch live x out : List Bool) : Fin 5 → List Bool := ![source,scratch,live,x,out]
def bit (live x : List Bool) (j : Nat) (z : Int) :=
  if readTapeBit live j then decide (z < 0) else readTapeBit x j

def emit : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q bits => if q.val = 0 then some ⟨1,
    ![none,none,none,none,some (if bits 2 then bits 0 else bits 3)],
    ![.right,.stay,.right,.right,.right]⟩ else none

theorem emit_run (pre tail scratch live x out : List Bool) (j : Nat) (z : Int) :
    Step emit 1 (heads pre.length j out.length) (bank (pre++intWord z++tail) scratch live x out)
      (heads (pre.length+1) (j+1) (out.length+1))
      (bank (pre++intWord z++tail) scratch live x (out++[bit live x j z])) := by
  have hs : step emit (⟨0,heads pre.length j out.length,bank (pre++intWord z++tail) scratch live x out⟩ : Configuration 5 2) =
      some ⟨1,heads (pre.length+1) (j+1) (out.length+1),bank (pre++intWord z++tail) scratch live x (out++[bit live x j z])⟩ := by
    simp only [step,emit]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;> simp [applyAction,bank,heads,Configuration.scanned,intWord,List.append_assoc,read_append,bit,write_append]
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

def slots : Fin 3 → Fin 5 := ![0,1,4]
theorem slots_injective : Function.Injective slots := by decide
theorem pick (i : Fin 5) : RecoveryFocus.pick slots i = ![some 0,some 1,none,none,some 2] i := by
  fin_cases i <;> first
    | exact RecoveryFocus.pick_slot _ slots_injective 0
    | exact RecoveryFocus.pick_slot _ slots_injective 1
    | exact RecoveryFocus.pick_slot _ slots_injective 2
    | decide
def skip := RecoveryFocus.machine slots (PCPPQueryField.machine false)
def machine := Composition.machine emit skip

theorem run (pre tail scratch live x out : List Bool) (j : Nat) (z : Int) :
    Step machine (2*natBitLength z.natAbs+5) (heads pre.length j out.length)
      (bank (pre++intWord z++tail) scratch live x out)
      (heads (pre.length+(intWord z).length) (j+1) (out.length+1))
      (bank (pre++intWord z++tail) (PCJ45bee56da9f34d5a_CircuitCountCopy.scratch z.natAbs scratch)
        live x (out++[bit live x j z])) := by
  have first := emit_run pre tail scratch live x out j z
  have field := PCJ45bee56da9f34d5a_CircuitCountCopy.field_run false (pre++[decide (z<0)]) tail scratch
    (out++[bit live x j z]) z.natAbs
  simp only [PCPPQueryField.selected,Bool.false_eq_true,if_false,List.append_nil] at field
  have source : (pre++[decide (z<0)])++natWord z.natAbs++tail=pre++intWord z++tail := by simp [intWord,List.append_assoc]
  rw [source] at field
  have focused := field.dock slots slots_injective (heads (pre.length+1) (j+1) (out.length+1))
    (bank (pre++intWord z++tail) scratch live x (out++[bit live x j z]))
    (by intro i;fin_cases i <;>simp [slots,heads,PCJ45bee56da9f34d5a_CircuitCountCopy.heads])
    (by intro i;fin_cases i <;>rfl)
  have last : Step skip (2*natBitLength z.natAbs+3)
      (heads (pre.length+1) (j+1) (out.length+1)) (bank (pre++intWord z++tail) scratch live x (out++[bit live x j z]))
      (heads (pre.length+(intWord z).length) (j+1) (out.length+1))
      (bank (pre++intWord z++tail) (PCJ45bee56da9f34d5a_CircuitCountCopy.scratch z.natAbs scratch) live x (out++[bit live x j z])) := by
    apply focused.congr
    · funext i;fin_cases i <;>simp [dockH,pick,heads,PCJ45bee56da9f34d5a_CircuitCountCopy.heads,intWord,List.length_append,Nat.add_assoc];omega
    · funext i;fin_cases i <;>simp [install,pick,bank,PCJ45bee56da9f34d5a_CircuitCountCopy.tapes]
  have all := first.seq last
  unfold machine
  convert all using 1;omega
end
end PCJ45bee56da9f34d5a_MinimumMaskCell
