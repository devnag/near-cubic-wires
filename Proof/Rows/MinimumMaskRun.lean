import Proof.Rows.MinimumMaskCell

/-! The actual q-counted native-sign pass builds the minimizing assignment.
Every weight is read in native order; the target suffix is never consumed. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_MinimumMaskRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
open PCJ45bee56da9f34d5a_MinimumMaskCell
noncomputable section

def stream (zs : List Int) := zs.flatMap intWord
def output (zs : List Int) (live x : List Bool) (j : Nat) :=
  (List.range j).map (fun i => bit live x i (zs.getD i 0))
def scratch (zs : List Int) (backing : List Bool) (j : Nat) :=
  (zs.take j).foldl (fun b z => PCJ45bee56da9f34d5a_CircuitCountCopy.scratch z.natAbs b) backing

def heads (pre : List Bool) (zs : List Int) (out : List Bool) (j : Nat) :=
  PCJ45bee56da9f34d5a_MinimumMaskCell.heads (pre.length+(stream (zs.take j)).length) j (out.length+j)
def tapes (pre tail : List Bool) (zs : List Int) (backing live x out : List Bool) (j : Nat) :=
  bank (pre++stream zs++tail) (scratch zs backing j) live x (out++output zs live x j)

theorem round (pre tail : List Bool) (zs : List Int) (backing live x out : List Bool) (F j : Nat)
    (hj : j < zs.length) (hF : ∀z∈zs,2*natBitLength z.natAbs+5 ≤ F) :
    Step PCJ45bee56da9f34d5a_MinimumMaskCell.machine F
      (heads pre zs out j) (tapes pre tail zs backing live x out j)
      (heads pre zs out (j+1)) (tapes pre tail zs backing live x out (j+1)) := by
  have hz : zs.getD j 0∈zs := by rw [List.getD_eq_getElem zs 0 hj];exact List.getElem_mem hj
  let before := pre++stream (zs.take j)
  let after := stream (zs.drop (j+1))++tail
  let acc := out++output zs live x j
  have h := (PCJ45bee56da9f34d5a_MinimumMaskCell.run before after (scratch zs backing j) live x acc j (zs.getD j 0)).enlarge (hF _ hz)
  have source : before++intWord (zs.getD j 0)++after=pre++stream zs++tail := by
    rw [stream,CloseoutRowsFamilyLoop.split_word zs 0 intWord j hj]
    simp only [before,after,stream,List.append_assoc]
  have pos := CloseoutRowsFamilyLoop.next_word zs 0 intWord j hj
  have snoc : output zs live x (j+1)=output zs live x j++[bit live x j (zs.getD j 0)] := by
    simp [output,List.range_succ,List.map_append]
  have sc : scratch zs backing (j+1)=PCJ45bee56da9f34d5a_CircuitCountCopy.scratch (zs.getD j 0).natAbs (scratch zs backing j) := by
    unfold scratch
    rw [List.take_succ_eq_append_getElem hj,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,List.getD_eq_getElem zs 0 hj]
  rw [source] at h
  refine (h.congr_in ?_ rfl).congr ?_ ?_
  · simp [heads,before,acc,output]
  · simp only [heads,before,acc,List.length_append,output,List.length_map,List.length_range,stream,pos,Nat.add_assoc]
  · simp only [tapes,sc,snoc,List.append_assoc,acc]

def machine := RepeatMachine.machine PCJ45bee56da9f34d5a_MinimumMaskCell.machine (fun _ _ => true)
def budget (q F : Nat) := q*(F+3)+3

theorem run (pre tail : List Bool) (zs : List Int) (backing live x out : List Bool) (F : Nat)
    (hF : ∀z∈zs,2*natBitLength z.natAbs+5 ≤ F) :
    Step machine (budget zs.length F)
      (Fin.addCases (PCJ45bee56da9f34d5a_MinimumMaskCell.heads pre.length 0 out.length) (fun _ : Fin 1=>1))
      (Fin.addCases (bank (pre++stream zs++tail) backing live x out) (fun _ : Fin 1=>CompareMachine.word zs.length))
      (Fin.addCases (PCJ45bee56da9f34d5a_MinimumMaskCell.heads (pre.length+(stream zs).length) zs.length (out.length+zs.length)) (fun _ : Fin 1=>1))
      (Fin.addCases (bank (pre++stream zs++tail) (scratch zs backing zs.length) live x (out++output zs live x zs.length)) (fun _ : Fin 1=>CompareMachine.word zs.length)) := by
  have h := CloseoutRowsOriginalClauseLoop.run PCJ45bee56da9f34d5a_MinimumMaskCell.machine zs.length F
    (heads pre zs out) (tapes pre tail zs backing live x out) (fun j hj=>round pre tail zs backing live x out F j hj hF)
  simpa only [machine,budget,heads,tapes,List.take_zero,List.take_length,stream,List.flatMap_nil,
    List.length_nil,Nat.add_zero,output,List.range_zero,List.map_nil,List.append_nil,scratch,List.foldl_nil] using h
end
end PCJ45bee56da9f34d5a_MinimumMaskRun
