import Proof.CaseAnalysis.RowsCircuitGuarded
import Proof.CaseAnalysis.RowsCircuitBottomReturned
import Proof.CaseAnalysis.RowsCircuitResourceRun

/-! The actual complete bottom loop is followed by the original resource
verdict only when every supported gate passed. Malformed bottoms stop with
the still-false circuit flag, before threshold subtraction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTraversalCaps
open LocalBitMultitape RecoveryRootRound CanonicalWitnessCodec RadixSemantics
open CloseoutRowsCircuit CloseoutRowsCircuitBottomDock CloseoutRowsCircuitBottomLoop
open CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (threshold : Bool):=CloseoutRowsGateColdPair.machine
  (CloseoutRowsCircuitBottomReturned.machine threshold) (CloseoutRowsCircuitResourceRun.machine threshold) (fun b=>b 1693)

theorem description_lower (core D : ℕ) (words : List (List Bool))
    (good : validity core true words words.length=true) : words.length+D ≤ descriptions core words D words.length:=by
  have every:=(validity_true core words).mp good
  have each (i : Fin words.length) : 1 ≤ descriptionCost core (words.getD i.val []):=by
    have mem:words.getD i.val []∈words:=by
      rw [List.getD_eq_getElem words [] i.isLt]
      exact List.getElem_mem i.isLt
    obtain ⟨g,hg⟩:=Option.isSome_iff_exists.mp (every _ mem)
    rw [descriptionCost,hg]
    change 1 ≤ descriptionBytes g
    unfold descriptionBytes
    rw [CloseoutRowsGateWeightLength.gate_description g]
    omega
  have sum:words.length ≤ ∑ i : Fin words.length,descriptionCost core (words.getD i.val []):=by
    have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>each i)
    simpa using hs
  rw [descriptions,total_fin]
  omega

theorem blank (C core n : ℕ) (out source members : List Bool) (D W : ℕ) (flag : Bool)
    (A : Fin 1703 → List Bool) (hc : 1 ≤ C)
    (ht : ∀ j,A (bottomSlots j)=localTapes C core n out source members D W flag j)
    (i : Fin 1703) (hi : 639 ≤ i.val ∧ i.val ≤ 664) : A i=List.replicate C false:=by
  let j:Fin 1049:=⟨i.val-639,by omega⟩
  have he:bottomSlots (j.castAdd 11)=i:=by
    apply Fin.ext
    rw [bottom_val]
    dsimp only [j,Fin.val_castAdd]
    split_ifs <;> omega
  rw [←he,ht]
  have cast: j.castAdd 11=(j.castAdd 10).castAdd 1:=Fin.ext rfl
  rw [cast]
  simp only [localTapes,Fin.addCases_left,CloseoutRowsCircuitBottom.data,CloseoutRowsGateBank.input,
    CloseoutRowsGateBank.padded,CloseoutRowsGateBank.input_eq,CloseoutRowsGateBank.pads]
  have notCore:j.val≠1035:=by dsimp only [j];omega
  rw [if_neg notCore,if_neg notCore]
  by_cases h1:j.val=1
  · rw [if_pos h1]
    change ZeroPadding.pad C [false]=List.replicate C false
    cases C
    · omega
    · simp [ZeroPadding.pad,List.replicate_succ]
  · rw [if_neg h1];simp [ZeroPadding.pad]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTraversalCaps
