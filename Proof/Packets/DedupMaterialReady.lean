import Proof.PCP.ProjectionNormalizationDedupReady

/-! Cold keep-last deduplication with both retained source and output banks
positioned at their starts, and both actual unary count drivers at position1.
All cursor changes are performed by the concrete reset and advance machines. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DedupMaterialReady
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

theorem cold_run (suffix : List Bool) (rows : List SuffixScan.Clause) :
    ∃ r,runFrom DedupCold.machine (DedupCold.budget (SuffixScan.stream rows++suffix) 0 rows)
      (DedupCold.entry DedupCold.machine.start (SuffixScan.stream rows++suffix) 0 rows.length)=some r ∧
      r.steps≤DedupCold.budget (SuffixScan.stream rows++suffix) 0 rows ∧
      r.final.tapes 0=SuffixScan.stream rows++suffix ∧
      r.final.tapes 2=SuffixScan.stream rows.dedup ∧
      r.final.tapes 3=CompareMachine.word rows.length ∧
      r.final.tapes 11=CompareMachine.word rows.dedup.length := by
  classical
  obtain ⟨base,hb,hbs,hbf⟩ := DedupCold.logical_run [] suffix rows
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_unpad DedupCold.machine (DedupCold.capacities rows) _ _ base hb
  rw [hbf] at hrf
  refine ⟨r,by simpa using hr,hrs.le.trans hbs,?_,?_,?_,?_⟩
  · have h := congrArg (fun c=>c.tapes 0) hrf
    simpa [ZeroPadding.config,DedupCold.capacities,Composition.rightConfig,Dedup.loopCfg,Dedup.cfg,
      Dedup.initialStore] using h
  · have h := congrArg (fun c=>c.tapes 2) hrf
    simpa [ZeroPadding.config,DedupCold.capacities,Composition.rightConfig,Dedup.loopCfg,Dedup.cfg,
      Dedup.process_out,Dedup.initialStore] using h
  · have h := congrArg (fun c=>c.tapes 3) hrf
    simpa [ZeroPadding.config,DedupCold.capacities,Composition.rightConfig,Dedup.loopCfg,Dedup.cfg,
      Dedup.initialStore] using h
  · have h := congrArg (fun c=>c.tapes 11) hrf
    simpa [ZeroPadding.config,DedupCold.capacities,Composition.rightConfig,Dedup.loopCfg,Dedup.cfg,
      Dedup.process_kept,Dedup.initialStore] using h

def nop : Machine 12 1 where
  descriptionBits := 0
  start := 0
  halted := fun _=>true
  rule := fun _ _=>none
noncomputable def stage := Composition.machine DedupCold.machine nop

def selected (i : Fin 12) := decide (i=0 ∨ i=2 ∨ i=3 ∨ i=11)
noncomputable def reset := MaskedReset.machine stage selected

def advance : Machine 13 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun _=>none,fun i=>if i=3 ∨ i=11 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine reset advance
noncomputable def entry (source : List Bool) (count : Nat) :=
  Composition.leftConfig 2 (Rewind.recording
    (Composition.leftConfig 1 (DedupCold.entry DedupCold.machine.start source 0 count)) 0)
def budget (rows : List SuffixScan.Clause) := 128*((SuffixScan.stream rows).length+1)^3+2

theorem advance_run (c : Configuration 13 2) (hc : c.control=0) :
    ∃ r,runFrom advance 1 c=some r ∧ r.final.tapes=c.tapes ∧
      (∀ i,r.final.heads i=if i=3 ∨ i=11 then c.heads i+1 else c.heads i) ∧ r.steps=1 := by
  let f : Configuration 13 2 := ⟨1,(fun i=>if i=3 ∨ i=11 then c.heads i+1 else c.heads i),c.tapes⟩
  have h : step advance c=some f := by
    simp [step,advance,hc]
    apply configuration_ext
    · rfl
    · funext i; by_cases hi : i=3 ∨ i=11 <;> simp [applyAction,HeadMove.apply,f,hi]
    · rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by simp [advance,hc]) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hs⟩

theorem ready_run (suffix : List Bool) (rows : List SuffixScan.Clause) :
    ∃ r,runFrom machine (budget rows) (entry (SuffixScan.stream rows++suffix) rows.length)=some r ∧
      r.steps≤budget rows ∧
      r.final.tapes 0=SuffixScan.stream rows++suffix ∧ r.final.heads 0=0 ∧
      r.final.tapes 2=SuffixScan.stream rows.dedup ∧ r.final.heads 2=0 ∧
      r.final.tapes 3=CompareMachine.word rows.length ∧ r.final.heads 3=1 ∧
      r.final.tapes 11=CompareMachine.word rows.dedup.length ∧ r.final.heads 11=1 := by
  obtain ⟨base,hb,hbs,hsource,hout,hcount,hkept⟩ := cold_run suffix rows
  let stopped : ExecutionReceipt 12 1 := ⟨Composition.restart base.final nop.start,0,base.final.tapeCells⟩
  have hn : runFrom nop 0 (Composition.restart base.final nop.start)=some stopped := rfl
  have hstage := Composition.run_join DedupCold.machine nop _ _ _ base stopped hb hn
  have hhead : ∀ i,selected i=true → (Composition.joinedReceipt base stopped).final.heads i≤
      (Composition.joinedReceipt base stopped).steps := by
    intro i _
    have h := SelectiveReset.prefix_head (prefix_of_run DedupCold.machine _ _ base hb).1 i
    have he : (DedupCold.entry DedupCold.machine.start (SuffixScan.stream rows++suffix) 0 rows.length).heads i≤1 := by
      simp only [DedupCold.entry]
      split
      · omega
      · split <;> omega
    change base.final.heads i≤base.steps+1+0
    omega
  obtain ⟨a,ha,haf,has,_⟩ := MaskedReset.reset_run stage selected _ _ (Composition.joinedReceipt base stopped) hstage hhead
  obtain ⟨b,hb,hbt,hbh,hbs'⟩ := advance_run (Composition.restart a.final advance.start) rfl
  have h := Composition.run_join reset advance _ _ _ a b ha hb
  have hcubic := Dedup.cubic_budget (SuffixScan.stream rows++suffix) 0 rows
  have htime : (2*(Composition.joinedReceipt base stopped).steps+2)+1+1≤budget rows := by
    simp only [Composition.joinedReceipt,stopped] at *
    unfold DedupCold.budget at hbs
    unfold budget
    omega
  have more := runFrom_moreFuel machine _ (budget rows-((2*(Composition.joinedReceipt base stopped).steps+2)+1+1))
    _ (Composition.joinedReceipt a b) h
  rw [Nat.add_sub_of_le htime] at more
  refine ⟨_,more,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps≤budget rows
    rw [has,hbs']
    exact htime
  · change b.final.tapes 0=_
    rw [hbt,haf]
    exact hsource
  · change b.final.heads 0=_
    rw [hbh,haf]
    rfl
  · change b.final.tapes 2=_
    rw [hbt,haf]
    exact hout
  · change b.final.heads 2=_
    rw [hbh,haf]
    rfl
  · change b.final.tapes 3=_
    rw [hbt,haf]
    exact hcount
  · change b.final.heads 3=_
    rw [hbh,haf]
    rfl
  · change b.final.tapes 11=_
    rw [hbt,haf]
    exact hkept
  · change b.final.heads 11=_
    rw [hbh,haf]
    rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.DedupMaterialReady
