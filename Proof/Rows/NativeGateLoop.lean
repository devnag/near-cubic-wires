import Proof.Rows.NativeGateWidth

/-! Counted traversal of actual original native gate frames. Each iteration
consumes the checked reusable framed-gate/count cell, including zero arity. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeGateLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_FramedGateBank PCJ45bee56da9f34d5a_UniformMinimumBounds
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CountedGateCell.machine

def zero (q : Nat) : NormalizedThresholdGate q := {weight:=fun _=>0,threshold:=0}
def word {q : Nat} (g : NormalizedThresholdGate q) := frame (PoolEntryLoad.word (strict g))
def stream {q : Nat} (gs : List (NormalizedThresholdGate q)) :=gs.flatMap word
def output {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q) (j : Nat) :=
 (gs.take j).map (fun g=>residualConstant g live x)
def heads {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre out : List Bool) (Q j : Nat) :=
 PCJ45bee56da9f34d5a_CountedGateCell.heads
  (PCJ45bee56da9f34d5a_FramedGateBank.heads (pre.length+(stream (gs.take j)).length) (out++output gs live x j)) (Q+j)
def tapes {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre tail out : List Bool) (B Q j : Nat) :=
 PCJ45bee56da9f34d5a_CountedGateCell.bank
  (bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1)) (pre++stream gs++tail)
    (List.replicate (H B q (B+1)) false) (List.replicate (H B q (B+1)) false) (out++output gs live x j)) (Q+j)

theorem round {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre tail out : List Bool) (B Q j : Nat) (hj : j<gs.length)
 (hb : ∀g∈gs,(PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B) :
 Step PCJ45bee56da9f34d5a_CountedGateCell.machine (PCJ45bee56da9f34d5a_CountedGateCell.cost B q (B+1))
  (heads gs live x pre out Q j) (tapes gs live x pre tail out B Q j)
  (heads gs live x pre out Q (j+1)) (tapes gs live x pre tail out B Q (j+1)) := by
 have hg : gs.getD j (zero q)∈gs := by rw [List.getD_eq_getElem gs (zero q) hj];exact List.getElem_mem hj
 let before:=pre++stream (gs.take j)
 let after:=stream (gs.drop (j+1))++tail
 let acc:=out++output gs live x j
 have h:=PCJ45bee56da9f34d5a_CountedGateCell.run (gs.getD j (zero q)) live x B (B+1) (Q+j)
   before after acc (by omega) (hb _ hg) (PCJ45bee56da9f34d5a_NativeGateWidth.magnitude _ B (B+1) (hb _ hg) (by omega))
 have hs : before++frame (PoolEntryLoad.word (strict (gs.getD j (zero q))))++after=pre++stream gs++tail := by
  rw [stream,CloseoutRowsFamilyLoop.split_word gs (zero q) word j hj]
  simp only [before,after,stream,word,List.append_assoc]
 have hp:=CloseoutRowsFamilyLoop.next_word gs (zero q) word j hj
 have ho : output gs live x (j+1)=output gs live x j++[residualConstant (gs.getD j (zero q)) live x] := by
  unfold output
  rw [List.take_succ_eq_append_getElem hj,List.map_append]
  simp only [List.map_cons,List.map_nil,List.getD_eq_getElem gs (zero q) hj]
 rw [hs] at h
 refine (h.congr_in ?_ rfl).congr ?_ ?_
 · simp only [heads,before,acc,List.length_append]
 · simp only [heads,before,acc,List.length_append,stream,hp,word,ho,List.append_assoc,Nat.add_assoc]
 · simp only [tapes,acc,ho,List.append_assoc,Nat.add_assoc]

def machine := RepeatMachine.machine PCJ45bee56da9f34d5a_CountedGateCell.machine (fun _ _=>true)
def budget (N B q : Nat) :=N*(PCJ45bee56da9f34d5a_CountedGateCell.cost B q (B+1)+3)+3

theorem run {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre tail out : List Bool) (B Q : Nat)
 (hb : ∀g∈gs,(PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B) :
 Step machine (budget gs.length B q)
  (Fin.addCases (m:=123) (n:=1) (motive:=fun _=>Nat)
    (PCJ45bee56da9f34d5a_CountedGateCell.heads (PCJ45bee56da9f34d5a_FramedGateBank.heads pre.length out) Q) (fun _=>1))
  (Fin.addCases (m:=123) (n:=1) (motive:=fun _=>List Bool)
    (PCJ45bee56da9f34d5a_CountedGateCell.bank (bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1))
      (pre++stream gs++tail) (List.replicate (H B q (B+1)) false) (List.replicate (H B q (B+1)) false) out) Q)
    (fun _=>CompareMachine.word gs.length))
  (Fin.addCases (m:=123) (n:=1) (motive:=fun _=>Nat)
    (PCJ45bee56da9f34d5a_CountedGateCell.heads (PCJ45bee56da9f34d5a_FramedGateBank.heads (pre.length+(stream gs).length)
      (out++gs.map (fun g=>residualConstant g live x))) (Q+gs.length)) (fun _=>1))
  (Fin.addCases (m:=123) (n:=1) (motive:=fun _=>List Bool)
    (PCJ45bee56da9f34d5a_CountedGateCell.bank (bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1))
      (pre++stream gs++tail) (List.replicate (H B q (B+1)) false) (List.replicate (H B q (B+1)) false)
      (out++gs.map (fun g=>residualConstant g live x))) (Q+gs.length))
    (fun _=>CompareMachine.word gs.length)) := by
 have h:=CloseoutRowsOriginalClauseLoop.run PCJ45bee56da9f34d5a_CountedGateCell.machine gs.length
  (PCJ45bee56da9f34d5a_CountedGateCell.cost B q (B+1)) (heads gs live x pre out Q)
  (tapes gs live x pre tail out B Q) (fun j hj=>round gs live x pre tail out B Q j hj hb)
 simpa only [machine,budget,heads,tapes,output,List.take_zero,List.take_length,List.map_nil,
   stream,List.flatMap_nil,List.length_nil,List.append_nil,Nat.add_zero] using h
end
end PCJ45bee56da9f34d5a_NativeGateLoop
