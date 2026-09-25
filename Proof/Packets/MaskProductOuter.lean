import Proof.Rows.MaskProductBody

/-! Actual left-major traversal of the Cartesian support product. Every
right-minor pass restores its right cursor before the next left row. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def outer := RepeatMachine.machine body (fun _ _=>true)
def products (left right : List (List Bool)) := left.flatMap (fun mask=>records mask right)
noncomputable def outerCfg (phase : Fin 5) (B N mh pos : Nat)
    (left right out count : List Bool) (total driver : Nat) :=
  RepeatMachine.cfg phase (⟨body.start,H mh pos out count,A B N left right out count⟩) total driver

 theorem repeat_cfg_eq {t s : Nat} (phase : Fin 5) (c d : Configuration t s)
    (total driver : Nat) (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

 theorem outer_remaining (B : Nat) (left right : List (List Bool))
    (mpre mtail pre tail out count : List Bool) (total done : Nat)
    (hl : ∀ row∈left,row.length=B) (hr : ∀ row∈right,row.length=B)
    (hn : done+left.length=total) :
    ∃ r,runFrom outer (left.length*(budget B right.length+2)+total+3)
      (outerCfg 0 B right.length mpre.length pre.length (mpre++left.flatten++mtail)
        (pre++right.flatten++tail) out count total (done+1))=some r ∧
      r.final=outerCfg 3 B right.length (mpre.length+left.flatten.length) pre.length
        (mpre++left.flatten++mtail) (pre++right.flatten++tail)
        (out++products left right) (count++List.replicate (left.length*right.length) true) total 1 ∧
      r.steps≤left.length*(budget B right.length+2)+total+3 := by
  induction left generalizing mpre out count done with
  | nil =>
    have hd : done=total := by simpa using hn
    subst done
    obtain ⟨r,rr,rf,rs⟩:=(RepeatMachine.exhaust body (fun _ _=>true)
      (⟨body.start,H mpre.length pre.length out count,
        A B right.length (mpre++mtail) (pre++right.flatten++tail) out count⟩) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa [outer,outerCfg] using rr
    · simpa [outerCfg,products] using rf
    · simpa using rs.le
  | cons mask left ih =>
    have hm : mask.length=B := hl mask (by simp)
    have hleft : ∀ row∈left,row.length=B := fun row h=>hl row (by simp [h])
    obtain ⟨r,rr,rh,rt,rs⟩:=body_run B mask right mpre (left.flatten++mtail)
      pre tail out count hm hr
    have first:=RepeatMachine.iteration body (fun _ _=>true)
      (⟨body.start,H mpre.length pre.length out count,
        A B right.length (mpre++mask++(left.flatten++mtail)) (pre++right.flatten++tail) out count⟩)
      total done r rfl (by simp only [List.length_cons] at hn;omega) rr
    simp only [ite_true] at first
    have exit:=repeat_cfg_eq 0 r.final
      (⟨body.start,H (mpre.length+B) pre.length (out++records mask right)
          (count++List.replicate right.length true),
        A B right.length (mpre++mask++(left.flatten++mtail)) (pre++right.flatten++tail)
          (out++records mask right) (count++List.replicate right.length true)⟩)
      total (done+2) rh rt
    rw [exit] at first
    obtain ⟨last,lr,lf,ls⟩:=ih (mpre++mask) (out++records mask right)
      (count++List.replicate right.length true) (done+1) hleft
      (by simp only [List.length_cons] at hn;omega)
    have lr' : runFrom outer (left.length*(budget B right.length+2)+total+3)
        (outerCfg 0 B right.length (mpre.length+B) pre.length
          (mpre++mask++(left.flatten++mtail)) (pre++right.flatten++tail)
          (out++records mask right) (count++List.replicate right.length true) total (done+2))=some last := by
      simpa [outerCfg,List.length_append,hm,List.append_assoc,Nat.add_assoc] using lr
    rcases first with ⟨space,hfirst⟩
    obtain ⟨result,resultRun,resultFinal,resultSteps,_⟩:=hfirst.followedBy last lr'
    have fit : (r.steps+2)+(left.length*(budget B right.length+2)+total+3)≤
        (mask::left).length*(budget B right.length+2)+total+3 := by
      simp only [List.length_cons]
      nlinarith
    have more:=runFrom_moreFuel outer _
      ((mask::left).length*(budget B right.length+2)+total+3-
        ((r.steps+2)+(left.length*(budget B right.length+2)+total+3))) _ result resultRun
    rw [Nat.add_sub_of_le fit] at more
    refine ⟨result,?_,?_,?_⟩
    · simpa [outerCfg,List.flatten_cons,List.append_assoc] using more
    · rw [resultFinal,lf]
      have countEq : (count++List.replicate right.length true)++
          List.replicate (left.length*right.length) true=
          count++List.replicate ((mask::left).length*right.length) true := by
        rw [List.append_assoc,←List.replicate_add]
        congr 2
        simp only [List.length_cons]
        ring
      rw [countEq]
      simp [outerCfg,products,List.flatten_cons,List.length_append,hm,List.append_assoc,Nat.add_assoc]
    · rw [resultSteps]
      simp only [List.length_cons]
      nlinarith

 theorem outer_run (B : Nat) (left right : List (List Bool))
    (mpre mtail pre tail out count : List Bool)
    (hl : ∀ row∈left,row.length=B) (hr : ∀ row∈right,row.length=B) :
    ∃ r,runFrom outer (left.length*(budget B right.length+3)+3)
      (outerCfg 0 B right.length mpre.length pre.length (mpre++left.flatten++mtail)
        (pre++right.flatten++tail) out count left.length 1)=some r ∧
      r.final=outerCfg 3 B right.length (mpre.length+left.flatten.length) pre.length
        (mpre++left.flatten++mtail) (pre++right.flatten++tail)
        (out++products left right) (count++List.replicate (left.length*right.length) true) left.length 1 ∧
      r.steps≤left.length*(budget B right.length+3)+3 := by
  have h:=outer_remaining B left right mpre mtail pre tail out count left.length 0 hl hr (by omega)
  have fuel : left.length*(budget B right.length+2)+left.length+3=
      left.length*(budget B right.length+3)+3 := by ring
  simpa only [fuel,Nat.zero_add] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
