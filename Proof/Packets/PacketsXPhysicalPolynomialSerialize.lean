import Proof.Packets.PacketsXPhysicalMaskRow
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.PhysicalPolynomialSerialize
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch PhysicalMaskIndices

def data (B : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) : Configuration 4 11 :=
  ⟨PhysicalMaskRow.machine.start,![1,sourcePos,1,out.length],
    ![UnaryTemplate.tape B,source,ZeroPadding.pad (B+3) (UnaryTemplate.tape 1),out]⟩
noncomputable def loop := RepeatMachine.machine PhysicalMaskRow.machine (fun _ _=>true)
noncomputable def cfg (B : Nat) (phase : Fin 5) (source : List Bool) (sourcePos : Nat)
    (out : List Bool) (total head : Nat) :=
  RepeatMachine.cfg phase (data B source sourcePos out) total head

def words (rows : List (List Bool)) : List Bool :=
  rows.flatMap (fun row=>ExtIncidence.monomialWord (selectedIndices 0 row))

theorem input_eq (bankPre support suffix out : List Bool) :
    PhysicalMaskRow.input bankPre support suffix out =
      data support.length (bankPre++support++suffix) bankPre.length out := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;>
      simp [PhysicalMaskRow.input,Composition.leftConfig,ZeroPadding.config,PhysicalMaskRow.capacity,
        PhysicalMaskSerialize.Bank.ready,PhysicalMaskSerialize.Bank.cfg,data]

theorem ending_eq (B : Nat) (phase : Fin 5) (source : List Bool) (sourcePos : Nat)
    (out : List Bool) (total head : Nat) :
    RepeatMachine.cfg phase (PhysicalMaskRow.ending B source sourcePos out) total head=
      cfg B phase source sourcePos out total head := rfl

theorem remaining (B : Nat) (pre : List Bool) (rows : List (List Bool)) (suffix out : List Bool)
    (total pos : Nat) (hn : pos+rows.length=total) (hw : ∀ row∈rows,row.length=B) :
    Timed loop (rows.length*(B^2+8*B+8)+total+3)
      (cfg B 0 (pre++rows.flatten++suffix) pre.length out total (pos+1))
      (cfg B 3 (pre++rows.flatten++suffix) (pre.length+rows.flatten.length)
        (out++words rows) total 1) := by
  induction rows generalizing pre out pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    simpa [loop,cfg,words] using RepeatMachine.exhaust PhysicalMaskRow.machine (fun _ _=>true)
      (data B (pre++suffix) pre.length out) total
  | cons row rows ih =>
    have hrow := hw row (by simp)
    have htail : ∀ row∈rows,row.length=B := fun row hr=>hw row (by simp [hr])
    obtain ⟨body,hb,hbf,hbs⟩ := PhysicalMaskRow.row_run pre row (rows.flatten++suffix) out
    have first := RepeatMachine.iteration PhysicalMaskRow.machine (fun _ _=>true)
      (PhysicalMaskRow.input pre row (rows.flatten++suffix) out) total pos body (by rfl)
      (by simp only [List.length_cons] at hn; omega) hb
    rw [input_eq,hbf,hbs,ending_eq,hrow] at first
    change Timed loop (B^2+8*B+6+2)
      (cfg B 0 (pre++row++(rows.flatten++suffix)) pre.length out total (pos+1))
      (cfg B 0 (pre++row++(rows.flatten++suffix)) (pre.length+B)
        (out++ExtIncidence.monomialWord (selectedIndices 0 row)) total (pos+2)) at first
    have tail := ih (pre++row) (out++ExtIncidence.monomialWord (selectedIndices 0 row)) (pos+1)
      (by simp only [List.length_cons] at hn; omega) htail
    have h := first.trans (by simpa [List.length_append,List.append_assoc,hrow] using tail)
    have time : B^2+8*B+6+2+(rows.length*(B^2+8*B+8)+total+3)=
      (rows.length+1)*(B^2+8*B+8)+total+3 := by ring
    rw [time] at h
    simpa [words,List.flatten_cons,List.append_assoc,List.length_append,hrow,Nat.add_assoc] using h

theorem loop_run (B : Nat) (pre : List Bool) (rows : List (List Bool)) (suffix out : List Bool)
    (hw : ∀ row∈rows,row.length=B) :
    ∃ r, runFrom loop (rows.length*(B^2+8*B+9)+3)
      (cfg B 0 (pre++rows.flatten++suffix) pre.length out rows.length 1)=some r ∧
      r.final=cfg B 3 (pre++rows.flatten++suffix) (pre.length+rows.flatten.length)
        (out++words rows) rows.length 1 ∧
      r.steps=rows.length*(B^2+8*B+9)+3 := by
  have h := remaining B pre rows suffix out rows.length 0 (by omega) hw
  have time : rows.length*(B^2+8*B+8)+rows.length+3=rows.length*(B^2+8*B+9)+3 := by ring
  rw [time] at h
  exact h.run (by simp [loop,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

def close : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,![none,none,none,some false,none],![.stay,.stay,.stay,.right,.stay]⟩ else none

def closedCfg (q : Fin 2) (B : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool)
    (total : Nat) : Configuration 5 2 :=
  ⟨q,![1,sourcePos,1,out.length,1],
    ![UnaryTemplate.tape B,source,ZeroPadding.pad (B+3) (UnaryTemplate.tape 1),out,CompareMachine.word total]⟩

theorem close_step (B : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) (total : Nat) :
    step close (closedCfg 0 B source sourcePos out total)=
      some (closedCfg 1 B source sourcePos (out++[false]) total) := by
  simp [step,close,closedCfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

noncomputable def machine := Composition.machine loop close
noncomputable def input (B : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) (total : Nat) :=
  Composition.leftConfig 2 (cfg B 0 source sourcePos out total 1)
def ending (B : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) (total : Nat) :=
  Composition.rightConfig (Fintype.card (RepeatMachine.Control 11)) (closedCfg 1 B source sourcePos out total)

theorem close_boundary (B : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) (total : Nat) :
    Composition.restart (cfg B 3 source sourcePos out total 1) close.start=
      closedCfg 0 B source sourcePos out total := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;>
      simp [Composition.restart,cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,data,closedCfg,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [Composition.restart,cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,data,closedCfg,Fin.addCases]

/-- A complete native polynomial stream is generated from resident support
rows by one fixed five-tape machine. All row resets and driver rewinds are paid. -/
theorem stream_run (B : Nat) (pre : List Bool) (rows : List (List Bool)) (suffix out : List Bool)
    (hw : ∀ row∈rows,row.length=B) :
    ∃ r, runFrom machine (rows.length*(B^2+8*B+9)+5)
      (input B (pre++rows.flatten++suffix) pre.length out rows.length)=some r ∧
      r.final=ending B (pre++rows.flatten++suffix) (pre.length+rows.flatten.length)
        (out++ExtIncidence.stream (rows.map (selectedIndices 0))) rows.length ∧
      r.steps=rows.length*(B^2+8*B+9)+5 := by
  obtain ⟨a,ha,haf,has⟩ := loop_run B pre rows suffix out hw
  obtain ⟨b,hb,hbf,hbs⟩ := (Timed.single (by rfl)
    (close_step B (pre++rows.flatten++suffix) (pre.length+rows.flatten.length) (out++words rows) rows.length)).run (by rfl)
  have join : runFrom close 1 (Composition.restart a.final close.start)=some b := by
    rw [haf,close_boundary]
    exact hb
  have h := Composition.run_join loop close _ _ _ a b ha join
  have time : rows.length*(B^2+8*B+9)+3+1+1=rows.length*(B^2+8*B+9)+5 := by omega
  rw [time] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_⟩
  · simp only [Composition.joinedReceipt,hbf,ending]
    congr 2
    simp [ExtIncidence.stream,words,List.flatMap_map,List.append_assoc]
  · simp only [Composition.joinedReceipt,has,hbs]

/-- The ordinary Step interface with no supplied execution premise. -/
theorem stream_step (B : Nat) (pre : List Bool) (rows : List (List Bool)) (suffix out : List Bool)
    (hw : ∀ row∈rows,row.length=B) :
    Step machine (rows.length*(B^2+8*B+9)+5)
      (input B (pre++rows.flatten++suffix) pre.length out rows.length).heads
      (input B (pre++rows.flatten++suffix) pre.length out rows.length).tapes
      (ending B (pre++rows.flatten++suffix) (pre.length+rows.flatten.length)
        (out++ExtIncidence.stream (rows.map (selectedIndices 0))) rows.length).heads
      (ending B (pre++rows.flatten++suffix) (pre.length+rows.flatten.length)
        (out++ExtIncidence.stream (rows.map (selectedIndices 0))) rows.length).tapes := by
  obtain ⟨r,hr,hf,hs⟩ := stream_run B pre rows suffix out hw
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs.le⟩

end PCJ9eff70d512234a4c_Fixed.PhysicalPolynomialSerialize
