import Proof.Assembly.Rows

/-! The whole support scan returns its source and candidate-score cursors.
The other heads retain their actual mask offset and unary-driver positions.
The reset log may have any physically retained false capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Reset
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan

theorem count_le (mask : Fin 3 → List Bool) (j : Nat) (bs : List Bool) :
    count (Scan.cells mask j bs) ≤ bs.length := by
  induction bs generalizing j with
  | nil => rfl
  | cons b bs ih =>
    have hb : (kept (b,readTapeBit (mask 0) j,readTapeBit (mask 1) j,
        readTapeBit (mask 2) j)).toNat ≤ 1 := by cases kept (b,readTapeBit (mask 0) j,
          readTapeBit (mask 1) j,readTapeBit (mask 2) j) <;> decide
    have hi := ih (j+1)
    simp only [Scan.cells,count,List.length_cons]
    omega

theorem score_le (q : Nat) (mask : Fin 3 → List Bool) (j : Nat)
    (rows : List (List Bool)) (s : Rows.Score) (hlen : ∀ bs ∈ rows, bs.length = q) :
    (rows.foldl (Rows.next mask j) s).1 ≤ s.1+rows.length*q := by
  induction rows generalizing s with
  | nil => simp
  | cons bs rows ih =>
    have hb := count_le mask j bs
    rw [hlen bs (by simp)] at hb
    have hi := ih (Rows.next mask j s bs) (by intro xs hx; exact hlen xs (by simp [hx]))
    simp only [List.foldl_cons,List.length_cons,Rows.next] at hi ⊢
    nlinarith

theorem framed_length (q : Nat) (rows : List (List Bool))
    (hlen : ∀ bs ∈ rows, bs.length = q) :
    (rows.flatMap frame).length = rows.length*(2*q+1) := by
  induction rows with
  | nil => simp
  | cons bs rows ih =>
    have hb := hlen bs (by simp)
    have hi := ih (by intro xs hx; exact hlen xs (by simp [hx]))
    simp only [List.flatMap_cons,List.length_append,frame_length,List.length_cons,hb,hi]
    ring

def selected (i : Fin 9) : Bool := decide (i.val = 0 ∨ i.val = 4)
noncomputable def machine := MaskedReset.machine Rows.machine selected
def fuel (q m : Nat) := m*(4*q+7)+3

noncomputable def initial (q cap : Nat) (rows : List (List Bool))
    (mask : Fin 3 → List Bool) (j : Nat) :=
  ZeroPadding.config (Rewind.Workspace.capacities 9 cap)
    (Rewind.recording
      (RepeatMachine.cfg 0 (Rows.data q [] rows [] mask j (0,false,false)) rows.length 1) 0)

noncomputable def finalData (q : Nat) (rows : List (List Bool))
    (mask : Fin 3 → List Bool) (j : Nat) :=
  RepeatMachine.cfg 3 (Rows.data q (rows.flatMap frame) [] [] mask j
    (rows.foldl (Rows.next mask j) (0,false,false))) rows.length 1

noncomputable def finished (q cap : Nat) (rows : List (List Bool))
    (mask : Fin 3 → List Bool) (j : Nat) :=
  SelectiveReset.finished (s := Fintype.card (RepeatMachine.Control 6))
    (fun i => if selected i then 0 else (finalData q rows mask j).heads i)
    (finalData q rows mask j).tapes (max cap (fuel q rows.length))

theorem reset_run (q cap : Nat) (rows : List (List Bool))
    (mask : Fin 3 → List Bool) (j : Nat) (hlen : ∀ bs ∈ rows, bs.length = q) :
    ∃ r, runFrom machine (2*fuel q rows.length+2) (initial q cap rows mask j) = some r ∧
      r.final = finished q cap rows mask j ∧ r.steps = 2*fuel q rows.length+2 := by
  obtain ⟨s,hs,hf,ht⟩ := Rows.rows_run q rows [] mask j (0,false,false) hlen
  have hc := score_le q mask j rows (0,false,false) hlen
  have hl := framed_length q rows hlen
  have hheads : ∀ i, selected i = true → s.final.heads i ≤ s.steps := by
    intro i hi
    rw [hf,ht]
    fin_cases i <;> simp [selected] at hi
    all_goals
      simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Rows.data,
        Composition.leftConfig,Row.cfg,Fin.addCases]
    · change (rows.flatMap frame).length ≤ rows.length*(4*q+7)+3
      nlinarith
    · change (rows.foldl (Rows.next mask j) (0,false,false)).1+1 ≤ rows.length*(4*q+7)+3
      simp only [Nat.zero_add] at hc
      nlinarith
  obtain ⟨base,hb,hbf,hbt,_⟩ := MaskedReset.reset_run Rows.machine selected _ _ s hs hheads
  obtain ⟨r,hr,hrf,hrt,_⟩ := ZeroPadding.run_config machine
    (Rewind.Workspace.capacities 9 cap) _ _ base hb
  refine ⟨r,?_,?_,?_⟩
  · simpa only [machine,initial,fuel,ht] using hr
  · rw [hrf,hbf,SelectiveReset.padded_finished,hf,ht]
    rfl
  · rw [hrt,hbt,ht]
    rfl

end PCJ93d4cfe17dc847a3.Reset
