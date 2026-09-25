import Proof.Packets.VectorTransferBlock

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorTransfer
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

abbrev Packet := List Bool×List Bool
abbrev Pair := Packet×Packet
def sourceBytes (rows : List Pair) := rows.flatMap (fun row=>row.1.1++row.1.2)
def targetBytes (rows : List Pair) := rows.flatMap (fun row=>row.2.1++row.2.2)
def Fits (R : Nat) (rows : List Pair) : Prop :=
  ∀ row∈rows,row.1.1.length=R ∧ row.1.2.length=R ∧ row.2.1.length=R ∧ row.2.2.length=R
abbrev loop := RepeatMachine.machine packet (fun _ _=>true)
def loopCfg (phase : Fin 5) (R spos tpos : Nat) (source target : List Bool) (total driver : Nat) :=
  RepeatMachine.cfg phase (⟨packet.start,H spos tpos,A R source target⟩) total driver

private theorem cfg_eq {t s : Nat} (phase : Fin 5) (c d : Configuration t s)
    (total driver : Nat) (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem remaining (R : Nat) (rows : List Pair) (spre spost tpre tpost : List Bool)
    (total done : Nat) (hf : Fits R rows) (hn : done+rows.length=total) :
    ∃ r,runFrom loop (rows.length*(16*R+25)+total+3)
      (loopCfg 0 R spre.length tpre.length (spre++sourceBytes rows++spost)
        (tpre++targetBytes rows++tpost) total (done+1))=some r ∧
      r.final=loopCfg 3 R (spre.length+rows.length*(2*R)) (tpre.length+rows.length*(2*R))
        (spre++List.replicate (rows.length*(2*R)) false++spost)
        (tpre++sourceBytes rows++tpost) total 1 ∧
      r.steps≤rows.length*(16*R+25)+total+3 := by
  induction rows generalizing spre tpre done with
  | nil =>
    have hd : done=total := by simpa using hn
    subst done
    obtain ⟨r,rr,rf,rs⟩:=(RepeatMachine.exhaust packet (fun _ _=>true)
      (⟨packet.start,H spre.length tpre.length,A R (spre++spost) (tpre++tpost)⟩) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa [loop,loopCfg,sourceBytes,targetBytes] using rr
    · simpa [loopCfg,sourceBytes] using rf
    · simpa using rs.le
  | cons row rows ih =>
    rcases row with ⟨⟨payload,count⟩,⟨oldPayload,oldCount⟩⟩
    obtain ⟨hp,hc,hop,hoc⟩:=hf ((payload,count),(oldPayload,oldCount)) (by simp)
    have hrows : Fits R rows := fun row h=>hf row (by simp [h])
    obtain ⟨r,rr,rh,rt,rs⟩:=packet_run R spre payload count (sourceBytes rows++spost)
      tpre oldPayload oldCount (targetBytes rows++tpost) hp hc hop hoc
    have first:=RepeatMachine.iteration packet (fun _ _=>true)
      (⟨packet.start,H spre.length tpre.length,
        A R (spre++payload++count++(sourceBytes rows++spost))
          (tpre++oldPayload++oldCount++(targetBytes rows++tpost))⟩)
      total done r rfl (by simp only [List.length_cons] at hn;omega) rr
    simp only [ite_true] at first
    have exit:=cfg_eq 0 r.final
      (⟨packet.start,H (spre.length+2*R) (tpre.length+2*R),
        A R (spre++List.replicate (2*R) false++(sourceBytes rows++spost))
          (tpre++payload++count++(targetBytes rows++tpost))⟩)
      total (done+2) rh rt
    rw [exit] at first
    obtain ⟨last,lr,lf,ls⟩:=ih (spre++List.replicate (2*R) false) (tpre++payload++count)
      (done+1) hrows (by simp only [List.length_cons] at hn;omega)
    have lr' : runFrom loop (rows.length*(16*R+25)+total+3)
        (loopCfg 0 R (spre.length+2*R) (tpre.length+2*R)
          (spre++List.replicate (2*R) false++(sourceBytes rows++spost))
          (tpre++payload++count++(targetBytes rows++tpost)) total (done+2))=some last := by
      have he : tpre.length+(R+R)=tpre.length+2*R := by omega
      simpa only [loopCfg,List.length_append,List.length_replicate,hp,hc,he,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using lr
    rcases first with ⟨space,hfirst⟩
    obtain ⟨result,resultRun,resultFinal,resultSteps,_⟩:=hfirst.followedBy last lr'
    have fit : (r.steps+2)+(rows.length*(16*R+25)+total+3)≤
        (rows.length+1)*(16*R+25)+total+3 := by nlinarith
    have more:=runFrom_moreFuel loop _
      ((rows.length+1)*(16*R+25)+total+3-((r.steps+2)+(rows.length*(16*R+25)+total+3)))
      _ result resultRun
    rw [Nat.add_sub_of_le fit] at more
    refine ⟨result,?_,?_,?_⟩
    · simpa [loopCfg,sourceBytes,targetBytes,List.append_assoc] using more
    · rw [resultFinal,lf]
      have zeros : List.replicate (2*R) false++List.replicate (rows.length*(2*R)) false=
          List.replicate ((rows.length+1)*(2*R)) false := by
        rw [←List.replicate_add,show 2*R+rows.length*(2*R)=(rows.length+1)*(2*R) by ring]
      have hs : spre.length+2*R+rows.length*(2*R)=spre.length+(rows.length+1)*(2*R) := by ring
      have ht : tpre.length+(R+R)+rows.length*(2*R)=tpre.length+(rows.length+1)*(2*R) := by ring
      simp only [loopCfg,sourceBytes,List.flatMap_cons,List.length_cons,List.length_append,
        List.length_replicate,hp,hc,hs,ht,List.append_assoc]
      rw [←List.append_assoc (List.replicate (2*R) false),zeros]
    · rw [resultSteps]
      simp only [List.length_cons]
      nlinarith

theorem loop_run (R : Nat) (rows : List Pair) (spre spost tpre tpost : List Bool) (hf : Fits R rows) :
    ∃ r,runFrom loop (rows.length*(16*R+26)+3)
      (loopCfg 0 R spre.length tpre.length (spre++sourceBytes rows++spost)
        (tpre++targetBytes rows++tpost) rows.length 1)=some r ∧
      r.final=loopCfg 3 R (spre.length+rows.length*(2*R)) (tpre.length+rows.length*(2*R))
        (spre++List.replicate (rows.length*(2*R)) false++spost)
        (tpre++sourceBytes rows++tpost) rows.length 1 ∧
      r.steps≤rows.length*(16*R+26)+3 := by
  have h:=remaining R rows spre spost tpre tpost rows.length 0 hf (by omega)
  have fuel : rows.length*(16*R+25)+rows.length+3=rows.length*(16*R+26)+3 := by ring
  simpa only [fuel,Nat.zero_add] using h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorTransfer
