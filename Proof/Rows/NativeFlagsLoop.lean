import Proof.Rows.CircuitFlagCost

/-! The actual reusable circuit callback traverses the native framed circuit
list. Its invariant co-counts all produced gate and target flags. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeFlagsLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds PCJ45bee56da9f34d5a_CircuitFlagBank
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload flags)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitFlagRun.machine

abbrev Circuit (q : Nat) :=List (NormalizedThresholdGate q)×List Bool
def word {q : Nat} (c : Circuit q) :=frame (payload c.1 c.2)
def stream {q : Nat} (cs : List (Circuit q)):=cs.flatMap word
def output {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q) (j : Nat) :=
 (cs.take j).flatMap (fun c=>flags c.1 live x)
def heads {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre out : List Bool) (Q j : Nat) :=PCJ45bee56da9f34d5a_CircuitFlagBank.heads
  0 (pre.length+(stream (cs.take j)).length) (out++output cs live x j) (Q+(output cs live x j).length) 0
def tapes {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre tail out : List Bool) (B Q j : Nat) :=bank live x B (pre++stream cs++tail) [] []
  (out++output cs live x j) (List.replicate (U B q (B+1)) false) (Q+(output cs live x j).length)

theorem round {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre tail out : List Bool) (B Q j : Nat) (hj : j<cs.length)
 (hb : ∀c∈cs,(payload c.1 c.2).length≤B) :
 Step PCJ45bee56da9f34d5a_CircuitFlagRun.machine (PCJ45bee56da9f34d5a_CircuitFlagCost.uniform B q)
  (heads cs live x pre out Q j) (tapes cs live x pre tail out B Q j)
  (heads cs live x pre out Q (j+1)) (tapes cs live x pre tail out B Q (j+1)) :=by
 let c:=cs.getD j ([],[])
 have hc:c∈cs:=by dsimp [c];rw [List.getD_eq_getElem cs ([],[]) hj];exact List.getElem_mem hj
 let before:=pre++stream (cs.take j)
 let after:=stream (cs.drop (j+1))++tail
 let acc:=out++output cs live x j
 have h:=PCJ45bee56da9f34d5a_CircuitFlagCost.run c.1 live x before c.2 after acc B
  (Q+(output cs live x j).length) (hb c hc)
 have hs : before++frame (payload c.1 c.2)++after=pre++stream cs++tail :=by
  rw [stream,CloseoutRowsFamilyLoop.split_word cs ([],[]) word j hj]
  simp only [before,after,stream,word,c,List.append_assoc]
 have hp:=CloseoutRowsFamilyLoop.next_word cs ([],[]) word j hj
 have ho : output cs live x (j+1)=output cs live x j++flags c.1 live x :=by
  unfold output
  rw [List.take_succ_eq_append_getElem hj,List.flatMap_append]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,c,List.getD_eq_getElem cs ([],[]) hj]
 have hl : (flags c.1 live x).length=c.1.length+1:=by simp [PCJ45bee56da9f34d5a_NativeCircuitFlags.flags]
 rw [hs] at h
 refine (h.congr_in ?_ rfl).congr ?_ ?_
 · simp only [heads,before,acc,List.length_append]
 · simp only [heads,before,acc,List.length_append,stream,hp,word,ho,hl,List.append_assoc,Nat.add_assoc,c]
 · simp only [tapes,acc,ho,List.length_append,hl,List.append_assoc,Nat.add_assoc]

def machine:=RepeatMachine.machine PCJ45bee56da9f34d5a_CircuitFlagRun.machine (fun _ _=>true)
def budget (N B q : Nat) :=N*(PCJ45bee56da9f34d5a_CircuitFlagCost.uniform B q+3)+3

def runHeads (cursor : Nat) (out : List Bool) (Q : Nat) :=
 Fin.addCases (m:=127) (n:=1) (motive:=fun _=>Nat)
  (PCJ45bee56da9f34d5a_CircuitFlagBank.heads 0 cursor out Q 0) (fun _=>1)
def runBank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q N : Nat) (source out : List Bool) :=
 Fin.addCases (m:=127) (n:=1) (motive:=fun _=>List Bool)
  (bank live x B source [] [] out (List.replicate (U B q (B+1)) false) Q) (fun _=>CompareMachine.word N)

theorem run {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre tail out : List Bool) (B Q : Nat) (hb : ∀c∈cs,(payload c.1 c.2).length≤B) :
 Step machine (budget cs.length B q)
  (runHeads pre.length out Q) (runBank live x B Q cs.length (pre++stream cs++tail) out)
  (runHeads (pre.length+(stream cs).length) (out++output cs live x cs.length) (Q+(output cs live x cs.length).length))
  (runBank live x B (Q+(output cs live x cs.length).length) cs.length (pre++stream cs++tail) (out++output cs live x cs.length)) :=by
 have h:=CloseoutRowsOriginalClauseLoop.run PCJ45bee56da9f34d5a_CircuitFlagRun.machine cs.length
  (PCJ45bee56da9f34d5a_CircuitFlagCost.uniform B q) (heads cs live x pre out Q)
  (tapes cs live x pre tail out B Q) (fun j hj=>round cs live x pre tail out B Q j hj hb)
 simpa only [machine,budget,heads,tapes,output,List.take_zero,List.take_length,
  stream,List.flatMap_nil,List.length_nil,List.append_nil,Nat.add_zero,runHeads,runBank] using h
end
end PCJ45bee56da9f34d5a_NativeFlagsLoop
