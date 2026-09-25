import Proof.Packets.PhysicalParityRestore
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
set_option warningAsError true
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
namespace NearCubicWires.RepairSource.ProjectionNormalization

namespace PhysicalParityProbe

theorem compare_run_suffix (left right : Fin 3 → List Bool) (candidatePrefix pre tail candidateSuffix : List Bool) (found : Bool) :
    ∃ r,runFrom compareProgram (ClauseEquality.budget left right)
      (cfg compareProgram.start (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream right++tail)
        candidatePrefix.length pre.length true found)=some r ∧
      r.final=cfg ClauseEquality.finalCode (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream right++tail)
        (candidatePrefix.length+(ClauseEquality.stream left).length) (pre.length+(ClauseEquality.stream right).length)
        (decide (left=right)) found ∧ r.steps=ClauseEquality.budget left right := by
  classical
  obtain ⟨base,hb,hf,hs⟩ := ClauseEquality.clause_run left right candidatePrefix pre candidateSuffix tail true
  simp only [Bool.true_and] at hb hf
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config slots (by decide) ClauseEquality.machine
    (cfg compareProgram.start (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length true found).heads
    (cfg compareProgram.start (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length true found).tapes
    _ _ base hb
  rw [compare_place] at hr
  refine ⟨r,hr,?_,hrs.trans hs⟩
  rw [hrf,hf,compare_place]

theorem raw_run_suffix (left right : Fin 3 → List Bool) (candidatePrefix pre tail candidateSuffix : List Bool) (eq found : Bool) :
    ∃ r,runFrom raw (budget left right)
      (cfg raw.start (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length eq found)=some r ∧
      r.final=cfg rawFinal (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream right++tail)
        (candidatePrefix.length+(ClauseEquality.stream left).length) (pre.length+(ClauseEquality.stream right).length)
        (decide (left=right)) (xor found (decide (left=right))) ∧ r.steps=budget left right := by
  classical
  obtain ⟨a,ha,haf,hat⟩ := boot_run (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length eq found
  obtain ⟨b,hb,hbf,hbt⟩ := compare_run_suffix left right candidatePrefix pre tail candidateSuffix found
  obtain ⟨c,hc,hcf,hct⟩ := finish_run (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream right++tail)
    (candidatePrefix.length+(ClauseEquality.stream left).length) (pre.length+(ClauseEquality.stream right).length) (decide (left=right)) found
  have hb' : runFrom compareProgram (ClauseEquality.budget left right) (Composition.restart a.final compareProgram.start)=some b := by rw [haf]; exact hb
  have hc' : runFrom finish 1 (Composition.restart b.final finish.start)=some c := by rw [hbf]; exact hc
  have hbc := Composition.run_join compareProgram finish _ _ _ b c hb' hc'
  have he : Composition.leftConfig 2 (Composition.restart a.final compareProgram.start)=
      Composition.restart a.final tailProgram.start := rfl
  rw [he] at hbc
  have hall := Composition.run_join boot tailProgram _ _ _ a (Composition.joinedReceipt b c) ha hbc
  have htime : 1+1+(ClauseEquality.budget left right+1+1)=budget left right := by dsimp [budget]; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt a (Composition.joinedReceipt b c),hall,?_,?_⟩
  · change Composition.rightConfig 2 (Composition.rightConfig _ c.final)=_
    rw [hcf]
    rfl
  · change a.steps+1+(b.steps+1+c.steps)=_
    rw [hat,hbt,hct]
    exact htime

theorem probe_run_suffix (left right : Fin 3 → List Bool) (candidatePrefix pre tail candidateSuffix : List Bool) (eq found : Bool) :
    ∃ r delta,runFrom machine (2*budget left right+2)
      (Rewind.recording (cfg raw.start (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream right++tail)
        candidatePrefix.length pre.length eq found) 0)=some r ∧
      delta ≤ budget left right ∧ r.steps=budget left right+delta+2 ∧
      r.final=SelectiveReset.finished (s := 2+((ClauseEquality.size+(ClauseEquality.size+ClauseEquality.size))+2))
        ![candidatePrefix.length,pre.length+(ClauseEquality.stream right).length,0,0]
        ![candidatePrefix++ClauseEquality.stream left++candidateSuffix,pre++ClauseEquality.stream right++tail,
          [decide (left=right)],[xor found (decide (left=right))]] delta := by
  classical
  obtain ⟨base,hb,hf,hs⟩ := raw_run_suffix left right candidatePrefix pre tail candidateSuffix eq found
  obtain ⟨r,delta,hr,hd,ht,hrf⟩ := CursorRestore.restore_run raw 0 (raw_forward 0) _ _ base hb
  rw [hs] at hr hd ht
  refine ⟨r,delta,hr,hd,ht,?_⟩
  rw [hrf,hf]
  congr 1
  funext i; fin_cases i <;> rfl

end PhysicalParityProbe

namespace PhysicalParityReuse

theorem probe_run_suffix (left right : Fin 3 → List Bool) (candidatePrefix pre tail candidateSuffix : List Bool)
    (eq found : Bool) (cap : ℕ) (hcap : PhysicalParityProbe.budget left right ≤ cap) :
    ∃ r,runFrom PhysicalParityProbe.machine (2*PhysicalParityProbe.budget left right+2)
      (cfg PhysicalParityProbe.machine.start (candidatePrefix++ClauseEquality.stream left++candidateSuffix)
        (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length eq found cap)=some r ∧
      r.steps ≤ 2*PhysicalParityProbe.budget left right+2 ∧
      r.final=cfg finalCode (candidatePrefix++ClauseEquality.stream left++candidateSuffix)
        (pre++ClauseEquality.stream right++tail) candidatePrefix.length
        (pre.length+(ClauseEquality.stream right).length) (decide (left=right))
        (xor found (decide (left=right))) cap := by
  classical
  obtain ⟨base,delta,hb,hd,hs,hf⟩ := PhysicalParityProbe.probe_run_suffix left right candidatePrefix pre tail candidateSuffix eq found
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_config PhysicalParityProbe.machine
    (Rewind.Workspace.capacities 4 cap) _ _ base hb
  rw [input_eq] at hr
  refine ⟨r,hr,by omega,?_⟩
  rw [hrf,hf,SelectiveReset.padded_finished,max_eq_left (hd.trans hcap),output_eq]

end PhysicalParityReuse

namespace PhysicalParityScan

theorem remaining_suffix (left : Clause) (candidatePrefix pre : List Bool) (rows : List Clause)
    (suffix candidateSuffix : List Bool) (eq found : Bool) (cap total pos : ℕ) (hn : pos+rows.length=total)
    (hcap : ∀ row∈rows,PhysicalParityProbe.budget left row ≤ cap) :
    ∃ r,runFrom machine (rows.length*(2*cap+4)+total+3)
      (cfg 0 (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++stream rows++suffix)
        candidatePrefix.length pre.length eq found cap total (pos+1))=some r ∧
      r.steps ≤ rows.length*(2*cap+4)+total+3 ∧
      r.final=cfg 3 (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++stream rows++suffix)
        candidatePrefix.length (pre.length+(stream rows).length) (endEq left rows eq)
        (seen left rows found) cap total 1 := by
  classical
  induction rows generalizing pre eq found pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust PhysicalParityProbe.machine (fun _ _ => true)
      (PhysicalParityReuse.cfg PhysicalParityProbe.machine.start (candidatePrefix++ClauseEquality.stream left++candidateSuffix)
        (pre++suffix) candidatePrefix.length pre.length eq found cap) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,cfg,stream_nil,List.length_nil,List.append_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
    · simpa [cfg,endEq,seen] using hf
  | cons row rows ih =>
    have hrow := hcap row (by simp)
    have htail : ∀ r∈rows,PhysicalParityProbe.budget left r ≤ cap := fun r hr => hcap r (by simp [hr])
    obtain ⟨body,hb,hbt,hbf⟩ := PhysicalParityReuse.probe_run_suffix left row candidatePrefix pre (stream rows++suffix) candidateSuffix eq found cap hrow
    have hstep := RepeatMachine.iteration PhysicalParityProbe.machine (fun _ _ => true)
      (PhysicalParityReuse.cfg PhysicalParityProbe.machine.start (candidatePrefix++ClauseEquality.stream left++candidateSuffix)
        (pre++ClauseEquality.stream row++(stream rows++suffix)) candidatePrefix.length pre.length eq found cap)
      total pos body (by rfl) (by simp only [List.length_cons] at hn; omega) hb
    rw [hbf] at hstep
    change Timed machine (body.steps+2)
      (cfg 0 (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream row++(stream rows++suffix))
        candidatePrefix.length pre.length eq found cap total (pos+1))
      (cfg 0 (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++ClauseEquality.stream row++(stream rows++suffix))
        candidatePrefix.length (pre.length+(ClauseEquality.stream row).length) (decide (left=row))
        (xor found (decide (left=row))) cap total (pos+2)) at hstep
    obtain ⟨tail,ht,htt,htf⟩ := ih (pre++ClauseEquality.stream row) (decide (left=row))
      (xor found (decide (left=row))) (pos+1) (by simp only [List.length_cons] at hn; omega) htail
    have hmid : cfg 0 (candidatePrefix++ClauseEquality.stream left++candidateSuffix)
        (pre++ClauseEquality.stream row++(stream rows++suffix)) candidatePrefix.length
        (pre.length+(ClauseEquality.stream row).length) (decide (left=row))
        (xor found (decide (left=row))) cap total (pos+2)=
      cfg 0 (candidatePrefix++ClauseEquality.stream left++candidateSuffix) ((pre++ClauseEquality.stream row)++stream rows++suffix)
        candidatePrefix.length (pre++ClauseEquality.stream row).length (decide (left=row))
        (xor found (decide (left=row))) cap total ((pos+1)+1) := by
      simp only [List.append_assoc,List.length_append,Nat.add_assoc]
    rw [hmid] at hstep
    rcases hstep with ⟨space,hstep⟩
    obtain ⟨result,hr,hf,hs,_⟩ := hstep.followedBy tail ht
    have htime : (body.steps+2)+(rows.length*(2*cap+4)+total+3) ≤
        (row::rows).length*(2*cap+4)+total+3 := by
      simp only [List.length_cons]
      nlinarith
    have hm := runFrom_moreFuel machine _
      ((row::rows).length*(2*cap+4)+total+3-((body.steps+2)+(rows.length*(2*cap+4)+total+3))) _ result hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨result,?_,?_,?_⟩
    · simpa only [stream_cons,List.append_assoc] using hm
    · rw [hs]; omega
    · rw [hf,htf]
      simp only [stream_cons,endEq,seen_cons,List.append_assoc,List.length_append,Nat.add_assoc]

theorem scan_run_suffix (left : Clause) (candidatePrefix pre : List Bool) (rows : List Clause)
    (suffix candidateSuffix : List Bool) (eq found : Bool) (cap : ℕ)
    (hcap : ∀ row∈rows,PhysicalParityProbe.budget left row ≤ cap) :
    ∃ r,runFrom machine (rows.length*(2*cap+5)+3)
      (cfg 0 (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++stream rows++suffix)
        candidatePrefix.length pre.length eq found cap rows.length 1)=some r ∧
      r.steps ≤ rows.length*(2*cap+5)+3 ∧
      r.final=cfg 3 (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++stream rows++suffix)
        candidatePrefix.length (pre.length+(stream rows).length) (endEq left rows eq)
        (seen left rows found) cap rows.length 1 := by
  have h := remaining_suffix left candidatePrefix pre rows suffix candidateSuffix eq found cap rows.length 0 (by omega) hcap
  have he : rows.length*(2*cap+4)+rows.length+3=rows.length*(2*cap+5)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end PhysicalParityScan

namespace PhysicalParityRestore

theorem scan_run_suffix (left : PhysicalParityScan.Clause) (candidatePrefix pre : List Bool) (rows : List PhysicalParityScan.Clause)
    (suffix candidateSuffix : List Bool) (eq found : Bool) (cap : ℕ)
    (hcap : ∀ row∈rows,PhysicalParityProbe.budget left row ≤ cap) :
    ∃ r log,runFrom machine (2*(rows.length*(2*cap+5)+3)+2)
      (Rewind.recording (PhysicalParityScan.cfg 0 (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++PhysicalParityScan.stream rows++suffix)
        candidatePrefix.length pre.length eq found cap rows.length 1) 0)=some r ∧
      log ≤ rows.length*(2*cap+5)+3 ∧ r.steps ≤ 2*(rows.length*(2*cap+5)+3)+2 ∧
      r.final=ending (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++PhysicalParityScan.stream rows++suffix)
        candidatePrefix.length pre.length (PhysicalParityScan.endEq left rows eq) (PhysicalParityScan.seen left rows found)
        cap rows.length log := by
  classical
  obtain ⟨base,hb,hbs,hbf⟩ := PhysicalParityScan.scan_run_suffix left candidatePrefix pre rows suffix candidateSuffix eq found cap hcap
  obtain ⟨r,log,hr,hl,hrs,hf⟩ := CursorRestore.restore_run PhysicalParityScan.machine 1 source_forward _ _ base hb
  have htime : 2*base.steps+2 ≤ 2*(rows.length*(2*cap+5)+3)+2 := by omega
  have hm := runFrom_moreFuel machine _ (2*(rows.length*(2*cap+5)+3)+2-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨r,log,hm,by omega,by omega,?_⟩
  rw [hf,hbf]
  unfold ending
  congr 1
  funext i
  fin_cases i <;>
    simp [PhysicalParityScan.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PhysicalParityReuse.cfg,Fin.addCases]

theorem ready_run_suffix (left : PhysicalParityScan.Clause) (candidatePrefix pre : List Bool)
    (rows : List PhysicalParityScan.Clause) (suffix candidateSuffix : List Bool) (eq found : Bool)
    (cap logCap : Nat)
    (hcap : ∀ row∈rows, PhysicalParityProbe.budget left row ≤ cap)
    (hlog : rows.length*(2*cap+5)+3 ≤ logCap) :
    ∃ r, runFrom machine (2*(rows.length*(2*cap+5)+3)+2)
      (input (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++PhysicalParityScan.stream rows++suffix)
        candidatePrefix.length pre.length eq found cap rows.length logCap)=some r ∧
      r.steps ≤ 2*(rows.length*(2*cap+5)+3)+2 ∧
      r.final=ending (candidatePrefix++ClauseEquality.stream left++candidateSuffix) (pre++PhysicalParityScan.stream rows++suffix)
        candidatePrefix.length pre.length (PhysicalParityScan.endEq left rows eq)
        (PhysicalCoefficientAlgebra.coefficient left rows found) cap rows.length logCap := by
  classical
  obtain ⟨base,log,hb,hl,hs,hf⟩ := scan_run_suffix left candidatePrefix pre rows suffix candidateSuffix eq found cap hcap
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_config machine
    (Rewind.Workspace.capacities 6 logCap) _ _ base hb
  refine ⟨r,hr,hrs.trans_le hs,?_⟩
  rw [hrf,hf]
  unfold ending
  rw [SelectiveReset.padded_finished,max_eq_left (hl.trans hlog)]
  rw [PhysicalParityScan.seen_coefficient]

end PhysicalParityRestore

end NearCubicWires.RepairSource.ProjectionNormalization
