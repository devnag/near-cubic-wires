import Proof.Rows.NativeGateLoop

/-! A target or final-offset coefficient has actual flag true. Emit it and
its unary count unit in one paid transition, retaining every other port. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_TrueFlagCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_FramedGateBank
noncomputable section

def heads (pos : Nat) (out : List Bool) (Q : Nat) :=
 PCJ45bee56da9f34d5a_CountedGateCell.heads (PCJ45bee56da9f34d5a_FramedGateBank.heads pos out) Q
def bank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U : Nat)
 (source fields framed out : List Bool) (Q : Nat) :=
 PCJ45bee56da9f34d5a_CountedGateCell.bank
   (PCJ45bee56da9f34d5a_FramedGateBank.bank live x w H R U source fields framed out) Q

def machine : Machine 123 2 where
 descriptionBits:=0
 start:=0
 halted:=fun q=>q.val==1
 rule:=fun q _=>if q.val=0 then some ⟨1,fun i=>if i=107 ∨ i=122 then some true else none,
  fun i=>if i=107 ∨ i=122 then .right else .stay⟩ else none

theorem heads_away (pos Q Q' : Nat) (out out' : List Bool) (i : Fin 123) (h1 : i≠107) (h2 : i≠122) :
 heads pos out Q i=heads pos out' Q' i := by
 fin_cases i <;>first | contradiction | rfl

theorem bank_away {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U Q Q' : Nat)
 (source fields framed out out' : List Bool) (i : Fin 123) (h1 : i≠107) (h2 : i≠122) :
 bank live x w H R U source fields framed out Q i=bank live x w H R U source fields framed out' Q' i := by
 revert h1 h2
 refine Fin.addCases (m:=122) (n:=1) (fun a ha _=>?_) (fun a _ ha=>?_) i
 · revert ha
   refine Fin.addCases (m:=114) (n:=8) (fun b hb=>?_) (fun _ _=>?_) a
   · revert hb
     refine Fin.addCases (m:=108) (n:=6) (fun c hc=>?_) (fun _ _=>?_) b
     · revert hc
       refine Fin.addCases (m:=107) (n:=1) (fun _ _=>?_) (fun d hd=>?_) c
       · simp only [bank,PCJ45bee56da9f34d5a_CountedGateCell.bank,
           PCJ45bee56da9f34d5a_FramedGateBank.bank,coreBank,
           PCJ45bee56da9f34d5a_CellGatePalette.cold,Fin.addCases_left]
       · fin_cases d;exact False.elim (hd rfl)
     · simp only [bank,PCJ45bee56da9f34d5a_CountedGateCell.bank,
         PCJ45bee56da9f34d5a_FramedGateBank.bank,coreBank,Fin.addCases_left,Fin.addCases_right]
   · simp only [bank,PCJ45bee56da9f34d5a_CountedGateCell.bank,
       PCJ45bee56da9f34d5a_FramedGateBank.bank,Fin.addCases_left,Fin.addCases_right]
 · fin_cases a;exact False.elim (ha rfl)

theorem run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U pos Q : Nat)
 (source fields framed out : List Bool) :
 Step machine 1 (heads pos out Q) (bank live x w H R U source fields framed out Q)
  (heads pos (out++[true]) (Q+1)) (bank live x w H R U source fields framed (out++[true]) (Q+1)) := by
 have hl : (CompareMachine.word Q).length=Q+1 := by simp [CompareMachine.word]
 have ht : CompareMachine.word Q++[true]=CompareMachine.word (Q+1) := by
  simp only [CompareMachine.word,List.replicate_add,List.replicate_one,List.cons_append]
 have hs : step machine (⟨0,heads pos out Q,bank live x w H R U source fields framed out Q⟩ : Configuration 123 2)=
  some ⟨1,heads pos (out++[true]) (Q+1),bank live x w H R U source fields framed (out++[true]) (Q+1)⟩ := by
  simp only [step,machine]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi:i=107
    · subst i;change out.length+1=(out++[true]).length;simp
    by_cases hj:i=122
    · subst i;rfl
    simp only [applyAction,if_neg (not_or_intro hi hj),HeadMove.apply]
    exact heads_away pos Q (Q+1) out (out++[true]) i hi hj
  · funext i
    by_cases hi:i=107
    · subst i;exact Streaming.write_append out true
    by_cases hj:i=122
    · subst i
      change writeTapeBit (CompareMachine.word Q) (Q+1) true=CompareMachine.word (Q+1)
      have he : writeTapeBit (CompareMachine.word Q) (Q+1) true=CompareMachine.word Q++[true] := by
       simpa only [hl] using Streaming.write_append (CompareMachine.word Q) true
      exact he.trans ht
    simp only [applyAction,if_neg (not_or_intro hi hj)]
    exact bank_away live x w H R U Q (Q+1) source fields framed out (out++[true]) i hi hj
 obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
 exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
end
end PCJ45bee56da9f34d5a_TrueFlagCell
