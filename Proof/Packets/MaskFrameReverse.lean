import Proof.Packets.MaskFrameLoop
import Proof.Packets.MaskProductOuter

/-! Reverse-order framing without a supplied reversed bank or extra data tape. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def backSlots : Fin 3→Fin 5 := ![0,2,1]
noncomputable def reverseBody := Composition.machine (RecoveryFocus.machine backSlots MaskBack.body)
  (Composition.machine machine (RecoveryFocus.machine backSlots MaskBack.body))
def H (pos : Nat) (out count : List Bool) : Fin 5→Nat := ![1,0,pos,out.length,count.length]
def A (B : Nat) (source out count : List Bool) : Fin 5→List Bool :=
  ![UnaryTemplate.tape B,[],source,out,count]

theorem back_run (B pos : Nat) (source out count : List Bool) :
    Step (RecoveryFocus.machine backSlots MaskBack.body) (2*B+2)
      (H (pos+B) out count) (A B source out count)
      (H pos out count) (A B source out count) := by
  obtain ⟨r,rr,rf,_⟩:=MaskBack.row_run B pos source []
  have rb:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact PhysicalFocusBoundary.focus rb backSlots (by decide)
    (H (pos+B) out count) (H pos out count) (A B source out count) (A B source out count)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))

theorem reverse_body_run (bits pre tail out count : List Bool) :
    Step reverseBody (7*bits.length+12)
      (H (pre.length+bits.length) out count) (A bits.length (pre++bits++tail) out count)
      (H pre.length (out++record bits) (count++[true]))
      (A bits.length (pre++bits++tail) (out++record bits) (count++[true])) := by
  have first:=back_run bits.length pre.length (pre++bits++tail) out count
  obtain ⟨r,rr,rf,_⟩:=row_run bits [] pre tail out count
  have second:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have second' : Step machine (3*bits.length+6)
      (H pre.length out count) (A bits.length (pre++bits++tail) out count)
      (H (pre.length+bits.length) (out++record bits) (count++[true]))
      (A bits.length (pre++bits++tail) (out++record bits) (count++[true])) := by
    simpa only [cfg,MaskProduct.cfg,H,A,record,List.append_assoc] using second
  have h:=first.seq (second'.seq (back_run bits.length pre.length (pre++bits++tail)
    (out++record bits) (count++[true])))
  have fuel : (2*bits.length+2)+1+((3*bits.length+6)+1+(2*bits.length+2))=
      7*bits.length+12 := by omega
  rw [fuel] at h
  exact h

noncomputable def reverseLoop := RepeatMachine.machine reverseBody (fun _ _=>true)
noncomputable def reverseCfg (phase : Fin 5) (B pos : Nat) (source out count : List Bool)
    (total driver : Nat) :=
  RepeatMachine.cfg phase (⟨reverseBody.start,H pos out count,A B source out count⟩) total driver

theorem reverse_remaining (B : Nat) (rows : List (List Bool)) (pre tail out count : List Bool)
    (total done : Nat) (hw : ∀ row∈rows,row.length=B) (hn : done+rows.length=total) :
    ∃ r,runFrom reverseLoop (rows.length*(7*B+14)+total+3)
      (reverseCfg 0 B (pre.length+rows.flatten.length) (pre++rows.flatten++tail)
        out count total (done+1))=some r ∧
      r.final=reverseCfg 3 B pre.length (pre++rows.flatten++tail)
        (out++records rows.reverse) (count++List.replicate rows.length true) total 1 ∧
      r.steps≤rows.length*(7*B+14)+total+3 := by
  induction rows using List.reverseRecOn generalizing tail out count done with
  | nil =>
    have hd : done=total := by simpa using hn
    subst done
    obtain ⟨r,rr,rf,rs⟩:=(RepeatMachine.exhaust reverseBody (fun _ _=>true)
      (⟨reverseBody.start,H pre.length out count,A B (pre++tail) out count⟩) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa [reverseLoop,reverseCfg] using rr
    · simpa [reverseCfg,records] using rf
    · simpa using rs.le
  | append_singleton rows row ih =>
    have hr : row.length=B := hw row (by simp)
    have hrows : ∀ r∈rows,r.length=B := fun r h=>hw r (by simp [h])
    obtain ⟨r,rr,rh,rt,rs⟩:=reverse_body_run row (pre++rows.flatten) tail out count
    have first:=RepeatMachine.iteration reverseBody (fun _ _=>true)
      (⟨reverseBody.start,H ((pre++rows.flatten).length+row.length) out count,
        A row.length ((pre++rows.flatten)++row++tail) out count⟩)
      total done r rfl (by simp only [List.length_append,List.length_singleton] at hn;omega) rr
    simp only [ite_true] at first
    have exit:=MaskProduct.repeat_cfg_eq 0 r.final
      (⟨reverseBody.start,H (pre++rows.flatten).length (out++record row) (count++[true]),
        A row.length ((pre++rows.flatten)++row++tail) (out++record row) (count++[true])⟩)
      total (done+2) rh rt
    rw [exit,hr] at first
    obtain ⟨last,lr,lf,ls⟩:=ih (row++tail) (out++record row) (count++[true]) (done+1)
      hrows (by simp only [List.length_append,List.length_singleton] at hn;omega)
    have lr' : runFrom reverseLoop (rows.length*(7*B+14)+total+3)
        (reverseCfg 0 B (pre++rows.flatten).length ((pre++rows.flatten)++row++tail)
          (out++record row) (count++[true]) total (done+2))=some last := by
      simpa [reverseCfg,List.length_append,List.append_assoc,Nat.add_assoc] using lr
    rcases first with ⟨space,hfirst⟩
    obtain ⟨result,resultRun,resultFinal,resultSteps,_⟩:=hfirst.followedBy last lr'
    have fit : (r.steps+2)+(rows.length*(7*B+14)+total+3)≤
        (rows++[row]).length*(7*B+14)+total+3 := by
      rw [hr] at rs
      simp only [List.length_append,List.length_singleton]
      nlinarith
    have more:=runFrom_moreFuel reverseLoop _
      ((rows++[row]).length*(7*B+14)+total+3-
        ((r.steps+2)+(rows.length*(7*B+14)+total+3))) _ result resultRun
    rw [Nat.add_sub_of_le fit] at more
    refine ⟨result,?_,?_,?_⟩
    · simpa [reverseCfg,List.flatten_append,List.flatten_cons,List.length_append,hr,
        List.append_assoc,Nat.add_assoc] using more
    · rw [resultFinal,lf]
      simp [reverseCfg,records,List.reverse_append,List.flatten_append,List.flatten_cons,
        List.length_append,List.append_assoc,List.replicate_succ]
    · rw [resultSteps]
      rw [hr] at rs
      simp only [List.length_append,List.length_singleton]
      nlinarith

theorem reverse_run (B : Nat) (rows : List (List Bool)) (pre tail out count : List Bool)
    (hw : ∀ row∈rows,row.length=B) :
    ∃ r,runFrom reverseLoop (rows.length*(7*B+15)+3)
      (reverseCfg 0 B (pre.length+rows.flatten.length) (pre++rows.flatten++tail)
        out count rows.length 1)=some r ∧
      r.final=reverseCfg 3 B pre.length (pre++rows.flatten++tail)
        (out++records rows.reverse) (count++List.replicate rows.length true) rows.length 1 ∧
      r.steps≤rows.length*(7*B+15)+3 := by
  have h:=reverse_remaining B rows pre tail out count rows.length 0 hw (by omega)
  have fuel : rows.length*(7*B+14)+rows.length+3=rows.length*(7*B+15)+3 := by ring
  simpa only [fuel,Nat.zero_add] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
