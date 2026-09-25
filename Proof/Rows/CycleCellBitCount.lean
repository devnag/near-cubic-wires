import Proof.Rows.CycleResidualScatter

/-! Physically sum one circuit's emitted C bits. The retained unary driver
counts the actual circuit occurrences; this machine appends one unary mark
for each true bit and pays to return both source and result cursors. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleCellBitCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding

def marks (bits : List Bool) : List Bool := bits.filter id

def body : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>decide (q=1)
  rule := fun q scan=>if q=0 then some ⟨1,![none,if scan 0 then some true else none],
    ![.right,if scan 0 then .right else .stay]⟩ else none

def cfg {s : Nat} (state : Fin s) (pos : Nat) (source out : List Bool) : Configuration 2 s :=
  ⟨state,![pos,out.length],![source,out]⟩

theorem bit_run (pre tail out : List Bool) (bit : Bool) :
    Step body 1 (![pre.length,out.length] : Fin 2→Nat) ![pre++bit::tail,out]
      (![pre.length+1,(out++marks [bit]).length] : Fin 2→Nat)
      ![pre++bit::tail,out++marks [bit]] := by
  have hs : step body (cfg 0 pre.length (pre++bit::tail) out)=
      some (cfg 1 (pre.length+1) (pre++bit::tail) (out++marks [bit])) := by
    cases bit <;> simp [step,body,cfg,Configuration.scanned,Streaming.read_append,marks]
    all_goals apply configuration_ext
    all_goals first | rfl | (funext i;fin_cases i <;> simp [applyAction,HeadMove.apply,
      Streaming.write_append])
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)
noncomputable def state (phase : Fin 5) (pos : Nat) (source out : List Bool) (total driver : Nat) :=
  RepeatMachine.cfg phase (cfg body.start pos source out) total driver

theorem remaining (bits pre tail out : List Bool) (total pos : Nat)
    (hn : pos+bits.length=total) :
    ∃ time≤3*bits.length+total+3, Timed machine time
      (state 0 pre.length (pre++bits++tail) out total (pos+1))
      (state 3 (pre.length+bits.length) (pre++bits++tail) (out++marks bits) total 1) := by
  induction bits generalizing pre out pos with
  | nil =>
    have hp : pos=total:=by simpa using hn
    subst pos
    refine ⟨total+3,by simp,?_⟩
    simpa [machine,state,marks] using RepeatMachine.exhaust body (fun _ _=>true)
      (cfg body.start pre.length (pre++tail) out) total
  | cons bit bits ih =>
    obtain ⟨r,hr,rh,rt,rs⟩:=bit_run pre (bits++tail) out bit
    have one:=RepeatMachine.iteration body (fun _ _=>true)
      (cfg body.start pre.length (pre++bit::(bits++tail)) out) total pos r rfl
      (by simp only [List.length_cons] at hn;omega) hr
    simp only [if_true] at one
    rw [CycleResidualScatter.cfg_eq 0 r.final
      (cfg body.start (pre.length+1) (pre++bit::(bits++tail)) (out++marks [bit]))
      total (pos+2) rh rt] at one
    obtain ⟨t,ht,rest⟩:=ih (pre++[bit]) (out++marks [bit]) (pos+1)
      (by simp only [List.length_cons] at hn;omega)
    have hm : marks (bit::bits)=marks [bit]++marks bits:=by
      simp only [marks,List.filter_cons,List.filter_nil]
      cases bit <;>rfl
    simp only [List.length_append,List.length_singleton,List.append_assoc,
      List.singleton_append,show pos+1+1=pos+2 by omega] at rest
    simp only [List.cons_append] at one rest
    have all:=one.trans rest
    refine ⟨r.steps+2+t,by simp only [List.length_cons] at ⊢;omega,?_⟩
    simpa only [machine,state,hm,List.length_cons,List.cons_append,List.append_assoc,
      List.length_append,Nat.add_assoc,Nat.add_comm 1 bits.length] using all

theorem scan_run (bits out : List Bool) :
    Step machine (4*bits.length+3) (![0,out.length,1] : Fin 3→Nat)
      ![bits,out,CompareMachine.word bits.length]
      (![bits.length,(out++marks bits).length,1] : Fin 3→Nat)
      ![bits,out++marks bits,CompareMachine.word bits.length] := by
  obtain ⟨time,ht,trace⟩:=remaining bits [] [] out bits.length 0 (by omega)
  obtain ⟨r,hr,hf,_⟩:=trace.run (by simp [machine,state,RepeatMachine.machine,
    RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have h:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).enlarge
    (show time≤4*bits.length+3 by omega)
  simp only [state,cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at h
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>rfl

def selected (i : Fin 3) : Bool := decide (i.val<2)

theorem marks_eq (bits : List Bool) : marks bits=List.replicate (marks bits).length true := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;>simpa [marks,List.replicate_succ] using ih

end Theorem25Completion.CycleCellBitCount
