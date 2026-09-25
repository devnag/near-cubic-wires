import Proof.Packets.NormalizerMaterializeReverse
import Proof.Packets.NormalizerMaterializeFilterInput

/-! An actual fixed ordinary normalizer: keep-last deletion, row reversal,
and coefficient parity filtering execute in sequence on one concrete24-tape bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

def budget (B : Nat) (raw : List (List Bool)) :=
  prefixBudget B raw+1+(4*filterCap B raw.length+6)

/-- No candidate bank, normalized polynomial, supplied transition, or supplied
run appears at entry: both the exact ordered output and its unary count are
computed from the original framed support records and literal input count. -/
theorem run (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∃ r,runFrom machine (budget B raw) (entry B raw)=some r ∧ r.steps≤budget B raw ∧
      r.final.tapes 20=(NormalizerOrder.ordered raw).flatten ∧ r.final.heads 20=0 ∧
      r.final.tapes 21=CompareMachine.word (NormalizerOrder.ordered raw).length ∧ r.final.heads 21=1 := by
  obtain ⟨a,ha,has,a0,ah0,a3,ah3,a14,ah14,a11,ah11,aextra⟩ := prefix_run B raw hw
  have hfits := filter_fits B raw
  obtain ⟨b,hb,hbs,bout,boutHead,bcount,bcountHead,_⟩ := ParityFilter.ready_run B (candidates raw)
    [] [] [] [] [] (records raw) 0 (probeCap B) (scanCap B raw.length)
    (filterCap B raw.length) (countCap B raw.length) false false (candidate_width B raw hw) (probes_fit B raw hw)
    (by simp [records,scanCap]) hfits (by unfold countCap; omega)
  have hh : ∀ j,a.final.heads (filterSlots j)=
      (ParityFilter.readyInput B (candidates raw) [] [] [] [] [] (records raw) 0
        (probeCap B) (scanCap B raw.length) (filterCap B raw.length) (countCap B raw.length) false false).heads j := by
    rw [filter_input_heads]
    intro j; fin_cases j
    · exact ah14
    · exact ah0
    · exact (aextra 3 (by decide)).1
    · exact (aextra 4 (by decide)).1
    · exact (aextra 5 (by decide)).1
    · exact ah3
    · exact (aextra 6 (by decide)).1
    · exact (aextra 7 (by decide)).1
    · exact (aextra 8 (by decide)).1
    · exact ah11
    · exact (aextra 9 (by decide)).1
    · exact (aextra 10 (by decide)).1
  have ht : ∀ j,a.final.tapes (filterSlots j)=
      (ParityFilter.readyInput B (candidates raw) [] [] [] [] [] (records raw) 0
        (probeCap B) (scanCap B raw.length) (filterCap B raw.length) (countCap B raw.length) false false).tapes j := by
    rw [filter_input_tapes]
    intro j; fin_cases j
    · exact a14
    · exact a0
    · exact (aextra 3 (by decide)).2
    · exact (aextra 4 (by decide)).2
    · exact (aextra 5 (by decide)).2
    · exact a3
    · exact (aextra 6 (by decide)).2
    · exact (aextra 7 (by decide)).2
    · exact (aextra 8 (by decide)).2
    · exact a11
    · exact (aextra 9 (by decide)).2
    · exact (aextra 10 (by decide)).2
  obtain ⟨c,hc,_,hcs,hch,hct,_⟩ := RecoveryFocus.dock filterSlots filterSlots_injective
    ParityFilter.readyMachine _ a.final.heads a.final.tapes _ hh ht b hb
  have hj : runFrom filterMachine
      (4*ParityFilter.filterBudget B (records raw).length (candidates raw).length (probeCap B)+6)
      (Composition.restart a.final filterMachine.start)=some c := hc
  have h := Composition.run_join prefixMachine filterMachine _ _ _ a c ha hj
  have htime : prefixBudget B raw+1+
      (4*ParityFilter.filterBudget B (records raw).length (candidates raw).length (probeCap B)+6)≤budget B raw := by
    unfold budget; omega
  have more := runFrom_moreFuel machine _
    (budget B raw-(prefixBudget B raw+1+
      (4*ParityFilter.filterBudget B (records raw).length (candidates raw).length (probeCap B)+6))) _ _ h
  rw [Nat.add_sub_of_le htime] at more
  refine ⟨_,more,?_,?_,?_,?_,?_⟩
  · change a.steps+1+c.steps≤budget B raw
    rw [hcs]
    unfold budget
    omega
  · change c.final.tapes (filterSlots 7)=_
    rw [hct,bout]
    simp only [List.nil_append,selected_eq]
  · change c.final.heads (filterSlots 7)=0
    rw [hch,boutHead]
    rfl
  · change c.final.tapes (filterSlots 8)=_
    rw [hct,bcount]
    simp only [selected_eq,Nat.zero_add]
  · change c.final.heads (filterSlots 8)=1
    rw [hch,bcountHead]

end PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
