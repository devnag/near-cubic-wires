import Proof.CaseAnalysis.RowsDegreeCoefficient
import Proof.Supplier.RowTupleCutList

/-! The fixed-degree call executes one recorded rewind of its reusable
work tapes. Its append cursor is excluded. The coarse capacity concerns
only those work tapes, so accumulated row output never enters this charge. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeReset
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 103) : Bool := decide (i=44 ∨ i=47 ∨ i=48 ∨ 49 ≤ i.val)
def caps (C : ℕ) (i : Fin 103) := if selected i then C else 0
def work (i : Fin 57) : Fin 103 :=
  if i.val=0 then 44 else if i.val=1 then 47 else if i.val=2 then 48
  else ⟨i.val+46,by omega⟩
theorem work_val (i : Fin 57) : (work i).val=
    if i.val=0 then 44 else if i.val=1 then 47 else if i.val=2 then 48 else i.val+46 := by
  unfold work
  split_ifs <;> rfl
theorem work_selected (i : Fin 57) : selected (work i)=true := by
  simp only [work]
  split_ifs
  · rfl
  · rfl
  · rfl
  · apply decide_eq_true
    right; right; right
    dsimp
    omega

noncomputable def machine {s : ℕ} (p : Machine 103 s) := MaskedReset.machine p selected
noncomputable def input {s : ℕ} (c : Configuration 103 s) (C : ℕ) :=
  ZeroPadding.config (Rewind.Workspace.capacities 103 C)
    (Rewind.recording (ZeroPadding.config (caps C) c) 0)
def budget (fuel : ℕ) := 2*fuel+2

theorem reset_run {s : ℕ} (p : Machine 103 s) (c : Configuration 103 s)
    (fuel C : ℕ) (raw : ExecutionReceipt 103 s)
    (hr : runFrom p fuel c=some raw)
    (hh : ∀ i,selected i=true → c.heads i=0)
    (ht : ∀ i,selected i=true → (c.tapes i).length≤C)
    (hc : fuel+1≤C) :
    ∃ actual,runFrom (machine p) (budget fuel) (input c C)=some actual ∧
      (∀ i,actual.final.heads (i.castAdd 1)=if selected i then 0 else raw.final.heads i) ∧
      (∀ i,actual.final.tapes (i.castAdd 1)=ZeroPadding.pad (caps C i) (raw.final.tapes i)) ∧
      actual.final.heads 103=0 ∧ actual.final.tapes 103=List.replicate C false ∧
      (∀ i,selected i=true → (actual.final.tapes (i.castAdd 1)).length=C) ∧
      actual.steps≤budget fuel := by
  have hraw := runFrom_steps_le p fuel c raw hr
  obtain ⟨padded,hp,pf,ps,_⟩ := ZeroPadding.run_config p (caps C) _ _ raw hr
  obtain ⟨actual,ha,af,as,_⟩ := MaskedReset.workspace_run p selected fuel C
    (ZeroPadding.config (caps C) c) padded hp (by intro i hi; exact hh i hi) (by omega)
  have hbound : 2*padded.steps+2≤budget fuel := by unfold budget; omega
  have hmore := runFrom_moreFuel (machine p) _ (budget fuel-(2*padded.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hbound] at hmore
  have ah : ∀ i,actual.final.heads (i.castAdd 1)=if selected i then 0 else raw.final.heads i := by
    intro i
    rw [af,pf]
    simp only [SelectiveReset.finished,Rewind.config,ZeroPadding.config,Fin.addCases_left]
  have atapes : ∀ i,actual.final.tapes (i.castAdd 1)=ZeroPadding.pad (caps C i) (raw.final.tapes i) := by
    intro i
    rw [af,pf]
    simp only [SelectiveReset.finished,Rewind.config,ZeroPadding.config,Fin.addCases_left]
  refine ⟨actual,hmore,ah,atapes,?_,?_,?_,as.le.trans hbound⟩
  · rw [af]
    rfl
  · rw [af]
    rfl
  · intro i hi
    have hs := PCPSerializerReuse.tape_support p fuel c raw hr i C 0
      (by rw [hh i hi]) ((ht i hi).trans (Nat.le_max_left _ _))
    have hsupport : (raw.final.tapes i).length≤C := by
      have hb : max C (0+raw.steps+1)≤C := by omega
      exact hs.trans hb
    rw [atapes]
    simp only [caps,hi,↓reduceIte,ZeroPadding.pad_length,max_eq_left hsupport]

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeReset
