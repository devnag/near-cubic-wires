import Proof.Assembly.RowOrdinaryCyclicMaskProduction

/-! Execute the same physical support-row body once per literal m-driver mark.
The source is the original concatenation of framed rows, with multiplicity. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Rows
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan

abbrev Score := Nat × Bool × Bool
def next (mask : Fin 3 → List Bool) (j : Nat) (s : Score) (bs : List Bool) : Score :=
  (s.1+count (Scan.cells mask j bs), s.2.1||(Scan.cells mask j bs).any touched,
    s.2.2||(Scan.cells mask j bs).any current)

def data (q : Nat) (pre : List Bool) (rows : List (List Bool)) (tail : List Bool)
    (mask : Fin 3 → List Bool) (j : Nat) (s : Score) : Configuration 8 6 :=
  Composition.leftConfig 3 (Row.cfg 0 q (pre++rows.flatMap frame++tail)
    pre.length mask j s.1 s.2.1 s.2.2)

noncomputable def machine := CloseoutRowsDegreeLoop.machine Row.machine

theorem remaining_timed (q total pos : Nat) (pre : List Bool)
    (rows : List (List Bool)) (tail : List Bool) (mask : Fin 3 → List Bool)
    (j : Nat) (s : Score) (hlen : ∀ bs ∈ rows, bs.length = q)
    (hpos : pos+rows.length = total) :
    Timed machine (rows.length*(4*q+6)+total+3)
      (RepeatMachine.cfg 0 (data q pre rows tail mask j s) total (pos+1))
      (RepeatMachine.cfg 3
        (data q (pre++rows.flatMap frame) [] tail mask j (rows.foldl (next mask j) s)) total 1) := by
  induction rows generalizing pos pre s with
  | nil =>
    have hp : pos = total := by simpa using hpos
    subst pos
    simpa [machine,CloseoutRowsDegreeLoop.machine] using
      RepeatMachine.exhaust Row.machine (fun _ _ => true) (data q pre [] tail mask j s) total
  | cons bs rows ih =>
    have hbs : bs.length = q := hlen bs (by simp)
    have hrows : ∀ xs ∈ rows, xs.length = q := by
      intro xs hx; exact hlen xs (by simp [hx])
    obtain ⟨r,hr,hf,hs⟩ := Row.row_run pre bs (rows.flatMap frame++tail)
      mask j s.1 s.2.1 s.2.2
    have hr' : runFrom Row.machine (4*q+4) (data q pre (bs::rows) tail mask j s) = some r := by
      simpa [data,List.append_assoc,hbs] using hr
    have hh : r.final.heads = (data q (pre++frame bs) rows tail mask j (next mask j s bs)).heads := by
      rw [hf]
      simp [data,Row.cfg,Composition.leftConfig,Composition.rightConfig,next,Nat.add_assoc]
    have ht : r.final.tapes = (data q (pre++frame bs) rows tail mask j (next mask j s bs)).tapes := by
      rw [hf]
      simp [data,Row.cfg,Composition.leftConfig,Composition.rightConfig,next,List.append_assoc,hbs]
    have first := RepeatMachine.iteration Row.machine (fun _ _ => true)
      (data q pre (bs::rows) tail mask j s) total pos r (by rfl) (by simp at hpos; omega) hr'
    simp only [↓reduceIte] at first
    rw [RowOccurrenceLoop.cfg_eq 0 r.final
      (data q (pre++frame bs) rows tail mask j (next mask j s bs)) total (pos+2) hh ht] at first
    have rest := ih (pos+1) (pre++frame bs) (next mask j s bs) hrows (by simp at hpos; omega)
    rw [show pos+1+1 = pos+2 by omega] at rest
    dsimp only [machine,CloseoutRowsDegreeLoop.machine] at rest
    have whole := first.trans rest
    rw [hs,hbs] at whole
    have htime : (4*q+4+2)+(rows.length*(4*q+6)+total+3) =
        (bs::rows).length*(4*q+6)+total+3 := by simp; ring
    rw [htime] at whole
    simpa only [machine,CloseoutRowsDegreeLoop.machine,List.flatMap_cons,
      List.foldl_cons,List.append_assoc] using whole

theorem rows_run (q : Nat) (rows : List (List Bool)) (tail : List Bool)
    (mask : Fin 3 → List Bool) (j : Nat) (s : Score)
    (hlen : ∀ bs ∈ rows, bs.length = q) :
    ∃ r, runFrom machine (rows.length*(4*q+7)+3)
      (RepeatMachine.cfg 0 (data q [] rows tail mask j s) rows.length 1) = some r ∧
      r.final = RepeatMachine.cfg 3
        (data q (rows.flatMap frame) [] tail mask j (rows.foldl (next mask j) s)) rows.length 1 ∧
      r.steps = rows.length*(4*q+7)+3 := by
  have h := remaining_timed q rows.length 0 [] rows tail mask j s hlen (by omega)
  have ht : rows.length*(4*q+6)+rows.length+3 = rows.length*(4*q+7)+3 := by ring
  rw [ht] at h
  simp only [Nat.zero_add,List.nil_append] at h
  exact h.run (by simp [machine,CloseoutRowsDegreeLoop.machine,RepeatMachine.machine,
    RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end PCJ93d4cfe17dc847a3.Rows
