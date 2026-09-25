import Proof.Packets.MaskProductReady
import Proof.MachineModel.Encoding

/-! The literal's unchanged natural-number code is recovered from its actual
native singleton pair record. The source cursor advances over the record;
the produced unary index is returned to head one. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeLiteralCode
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding

def word (code : Nat) := [true,true]++List.replicate code true++[false,false,false,false]
def machine : Machine 2 7 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==6
  rule:=fun q scan=>
    if q.val=0 then some ⟨1,![none,some false],![.right,.right]⟩
    else if q.val=1 then some ⟨2,fun _=>none,![.right,.stay]⟩
    else if q.val=2 then some (if scan 0 then ⟨2,![none,some true],![.right,.right]⟩
      else ⟨3,fun _=>none,![.right,.stay]⟩)
    else if q.val=3 then some ⟨4,fun _=>none,![.right,.stay]⟩
    else if q.val=4 then some ⟨5,fun _=>none,![.right,.stay]⟩
    else if q.val=5 then some ⟨6,fun _=>none,![.right,.stay]⟩
    else none

def cfg (q : Fin 7) (pos : Nat) (source out : List Bool) : Configuration 2 7 :=
  ⟨q,![pos,out.length],![source,out]⟩

theorem first (pos : Nat) (source : List Bool) :
    step machine (cfg 0 pos source [])=some (cfg 1 (pos+1) source [false]) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> rfl

theorem advance (q q' : Fin 7) (hq : (q,q')∈[(1,2),(3,4),(4,5),(5,6)])
    (pos : Nat) (source out : List Bool) :
    step machine (cfg q pos source out)=some (cfg q' (pos+1) source out) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hq
  rcases hq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals
    simp [step,machine,cfg]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
    · rfl

theorem copy_step (pre tail out : List Bool) :
    step machine (cfg 2 pre.length (pre++true::tail) out)=
      some (cfg 2 (pre++[true]).length (pre++true::tail) (out++[true])) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem stop_step (pre tail out : List Bool) :
    step machine (cfg 2 pre.length (pre++false::tail) out)=
      some (cfg 3 (pre.length+1) (pre++false::tail) out) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem copy (n : Nat) (pre tail out : List Bool) :
    Timed machine n (cfg 2 pre.length (pre++List.replicate n true++tail) out)
      (cfg 2 (pre++List.replicate n true).length
        (pre++List.replicate n true++tail) (out++List.replicate n true)) := by
  induction n generalizing pre out with
  | zero => simpa using Timed.refl machine (cfg 2 pre.length (pre++tail) out)
  | succ n ih =>
    have first:=Timed.single (by rfl) (copy_step pre (List.replicate n true++tail) out)
    have rest:=ih (pre++[true]) (out++[true])
    have all:=first.trans (by simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using rest)
    simpa [List.replicate_succ,List.append_assoc,Nat.add_comm] using all

theorem parse (code : Nat) (pre post : List Bool) :
    Step machine (code+6) (![pre.length,0]) (![pre++word code++post,[]])
      (![pre.length+code+6,code+1])
      (![pre++word code++post,CompareMachine.word code]) := by
  let source:=pre++word code++post
  have first:=Timed.single (by rfl) (first pre.length source)
  have second:=Timed.single (by rfl) (advance 1 2 (by simp) (pre.length+1) source [false])
  have third:=copy code (pre++[true,true]) ([false,false,false,false]++post) [false]
  have fourth:=Timed.single (by rfl) (stop_step ((pre++[true,true])++List.replicate code true)
    ([false,false,false]++post) ([false]++List.replicate code true))
  have a:=Timed.single (by rfl) (advance 3 4 (by simp) (pre.length+code+3) source (CompareMachine.word code))
  have b:=Timed.single (by rfl) (advance 4 5 (by simp) (pre.length+code+4) source (CompareMachine.word code))
  have c:=Timed.single (by rfl) (advance 5 6 (by simp) (pre.length+code+5) source (CompareMachine.word code))
  have tail:=a.trans (by simpa [Nat.add_assoc] using b.trans (by simpa [Nat.add_assoc] using c))
  have endpart:=fourth.trans (by simpa [source,word,CompareMachine.word,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail)
  have main:=third.trans endpart
  have start:=first.trans second
  have all:=start.trans (by simpa [source,word,List.append_assoc,Nat.add_assoc] using main)
  obtain ⟨r,rr,rf,_⟩:=all.run (by rfl)
  have rs:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  simpa [cfg,source,word,CompareMachine.word,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rs

def returnSlot : Fin 1→Fin 2 := ![1]
noncomputable def readyMachine := Composition.machine machine
  (RecoveryFocus.machine returnSlot PairCountReady.machine)

theorem ready_run (code : Nat) (pre post : List Bool) :
    Step readyMachine (2*code+9) (![pre.length,0]) (![pre++word code++post,[]])
      (![pre.length+code+6,1])
      (![pre++word code++post,CompareMachine.word code]) := by
  obtain ⟨r,rr,rf,_⟩:=PairCountReady.run code
  have small:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have back : Step (RecoveryFocus.machine returnSlot PairCountReady.machine) (code+2)
      (![pre.length+code+6,code+1]) (![pre++word code++post,CompareMachine.word code])
      (![pre.length+code+6,1]) (![pre++word code++post,CompareMachine.word code]) := by
    apply PhysicalFocusBoundary.focus small returnSlot (by decide)
      (![pre.length+code+6,code+1]) (![pre.length+code+6,1])
      (![pre++word code++post,CompareMachine.word code])
      (![pre++word code++post,CompareMachine.word code])
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i away;fin_cases i
      · exact ⟨rfl,rfl⟩
      · exact False.elim (away 0 rfl)
  have all:=(parse code pre post).seq back
  have fuel : code+6+1+(code+2)=2*code+9 := by omega
  simpa only [fuel,readyMachine] using all

theorem padded_run (R code : Nat) (pre post : List Bool) :
    Step readyMachine (2*code+9) (![pre.length,0])
      (![pre++word code++post,List.replicate R false])
      (![pre.length+code+6,1])
      (![pre++word code++post,ZeroPadding.pad R (CompareMachine.word code)]) := by
  have h:=(ready_run code pre post).pad (![0,R] : Fin 2→Nat)
  exact (h.congr_in rfl (by funext i;fin_cases i <;>simp [ZeroPadding.pad])).congr rfl
    (by funext i;fin_cases i <;>simp)

theorem word_native (code : Nat) : word code=
    ExtIncidence.stream [[code]]++ExtIncidence.stream [] := by
  simp [word,ExtIncidence.stream,ExtIncidence.monomialWord,ExtIncidence.block,
    List.replicate_succ,List.append_assoc]

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeLiteralCode
