import Proof.Packets.PhysicalZeroBank
import Proof.Packets.MaskConstantOverwrite

/-! The same fixed zero-bank machine resets an existing dense table. Every
old bit is overwritten and the cursor is physically returned. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch

attribute [local irreducible] chunk packet loop machine

theorem overwrite_chunk (R : Nat) (pre old post : List Bool) (hlen : old.length=R) :
    Step chunk (4*R+5) (H pre.length) (A R (pre++old++post))
      (H (pre.length+R)) (A R (pre++List.replicate R false++post)) := by
  have first:=PhysicalFocusBoundary.focus (MaskConstant.overwrite_run R pre old post hlen)
    zeroSlots (by decide) (H pre.length) (H pre.length)
    (A R (pre++old++post)) (A R (pre++List.replicate R false++post))
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
    (by intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))
  obtain ⟨r,rr,rf,_⟩:=MaskSeek.row_run R pre.length (pre++List.replicate R false++post) []
  have second:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have h:=first.seq second
  have fuel : (2*R+2)+1+(2*R+2)=4*R+5:=by omega
  have result : Step (Composition.machine (RecoveryFocus.machine zeroSlots MaskConstant.maskMachine) MaskSeek.body)
      ((2*R+2)+1+(2*R+2)) (H pre.length) (A R (pre++old++post))
      (H (pre.length+R)) (A R (pre++List.replicate R false++post)) :=
    h.congr (by funext i;fin_cases i <;>rfl) (by funext i;fin_cases i <;>rfl)
  simpa only [chunk,zero,fuel] using result

theorem overwrite_packet (R : Nat) (pre old post : List Bool) (hlen : old.length=2*R) :
    Step packet (8*R+11) (H pre.length) (A R (pre++old++post))
      (H (pre.length+2*R)) (A R (pre++List.replicate (2*R) false++post)) := by
  have htake : (old.take R).length=R:=by simp [List.length_take,hlen];omega
  have hdrop : (old.drop R).length=R:=by simp [List.length_drop,hlen];omega
  have first:=overwrite_chunk R pre (old.take R) (old.drop R++post) htake
  have last:=overwrite_chunk R (pre++List.replicate R false) (old.drop R) post hdrop
  simp only [List.length_append,List.length_replicate] at last
  have h:=first.seq (by simpa only [List.append_assoc] using last)
  have bank : pre++old.take R++(old.drop R++post)=pre++old++post := by
    calc
      _=pre++((old.take R++old.drop R)++post):=by simp only [List.append_assoc]
      _=pre++old++post:=by rw [List.take_append_drop,List.append_assoc]
  have zeros : List.replicate R false++List.replicate R false=List.replicate (2*R) false := by
    rw [←List.replicate_add,show R+R=2*R by omega]
  have out : pre++(List.replicate R false++(List.replicate R false++post))=pre++List.replicate (2*R) false++post := by
    rw [←List.append_assoc (List.replicate R false),zeros,List.append_assoc]
  have pos : pre.length+R+R=pre.length+2*R:=by omega
  have fuel : (4*R+5)+1+(4*R+5)=8*R+11:=by omega
  simpa only [packet,bank,out,pos,fuel] using h

def resetState (R j : Nat) (old : List Bool) := List.replicate (j*(2*R)) false++old.drop (j*(2*R))

theorem overwrite_loop (R N : Nat) (old : List Bool) (hlen : old.length=N*(2*R)) :
    Step loop (N*(8*R+14)+3) (heads 0) (tapes R N old)
      (heads (N*(2*R))) (tapes R N (List.replicate (N*(2*R)) false)) := by
  have body (i : Nat) (hi:i<N) : Step packet (8*R+11)
      (H (i*(2*R))) (A R (resetState R i old))
      (H ((i+1)*(2*R))) (A R (resetState R (i+1) old)) := by
    have hf : i*(2*R)+2*R≤old.length:=by rw [hlen];nlinarith
    let rest:=old.drop (i*(2*R))
    have restlen : 2*R≤rest.length:=by simp only [rest,List.length_drop];omega
    have ht : (rest.take (2*R)).length=2*R:=by simp [List.length_take,Nat.min_eq_left restlen]
    have h:=overwrite_packet R (List.replicate (i*(2*R)) false)
      (rest.take (2*R)) (rest.drop (2*R)) ht
    have he : i*(2*R)+2*R=(i+1)*(2*R):=by ring
    have input : List.replicate (i*(2*R)) false++rest.take (2*R)++rest.drop (2*R)=resetState R i old := by
      rw [List.append_assoc,List.take_append_drop]
      rfl
    have output : List.replicate (i*(2*R)) false++List.replicate (2*R) false++rest.drop (2*R)=resetState R (i+1) old := by
      simp only [rest,resetState,←List.replicate_add,List.drop_drop,he]
    simpa only [List.length_replicate,input,output,he] using h
  have all:=PhysicalRepeatStep.run packet N (8*R+11)
    (fun i=>H (i*(2*R))) (fun i=>A R (resetState R i old)) body
  have fuel : N*((8*R+11)+3)+3=N*(8*R+14)+3:=by ring
  have first : resetState R 0 old=old:=by simp [resetState]
  have last : resetState R N old=List.replicate (N*(2*R)) false:=by
    simp only [resetState,←hlen,List.drop_length,List.append_nil]
  rw [fuel] at all
  simp only [Nat.zero_mul,first,last] at all
  unfold loop
  convert all using 1
  all_goals first | rfl | (funext i;fin_cases i <;>rfl)

theorem overwrite_run (R N : Nat) (old : List Bool) (hlen : old.length=N*(2*R)) :
    Step machine (budget R N) (heads 0) (tapes R N old)
      (heads 0) (tapes R N (List.replicate (N*(2*R)) false)) := by
  have first:=overwrite_loop R N old hlen
  have second:=back_run R N (N*R) (List.replicate (N*(2*R)) false)
  have third:=back_run R N 0 (List.replicate (N*(2*R)) false)
  have he : N*R+N*R=N*(2*R):=by ring
  rw [he] at second
  simp only [Nat.zero_add] at third
  have h:=first.seq (second.seq third)
  have fuel : (N*(8*R+14)+3)+1+((N*(2*R+5)+3)+1+(N*(2*R+5)+3))=budget R N:=by unfold budget;ring
  simpa only [machine,fuel] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroBank
