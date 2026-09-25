import Proof.Rows.FourfoldPowerRun
import Proof.Rows.PowerMeaning

/-! Identify the physically emitted four-call stream with the canonical
mixed-radix coefficient blocks, including all target summands. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FourfoldPowerMeaning
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ45bee56da9f34d5a_FourfoldBaseData (Data)
open PCJ45bee56da9f34d5a_FourfoldPowerData
open PCJ45bee56da9f34d5a_SelectedPowerBody (equation)
noncomputable section

theorem factor_eq (d :Data) (B p j :Nat) (hj :j≤d.count):
 factor d B p j=PCJ45bee56da9f34d5a_PowerMeaning.factor B p j :=by
 induction j with
 | zero=>rfl
 | succ j ih=>
   have h:j<d.count:=by omega
   simp only [factor,if_pos h,PCJ45bee56da9f34d5a_PowerMeaning.factor,ih (by omega)]

def chunk (d :Data) (B p w :Nat) (i :Fin d.count):=
 PCJ45bee56da9f34d5a_NativeScaleEquation.result (PCJ45bee56da9f34d5a_PowerMeaning.factor B p i.val)
  p w (equation ((d.gates i).get (d.selected i)))

theorem stream_take (d :Data) (B p w j :Nat):
 stream d B p w j=((List.ofFn (fun i :Fin d.count=>i)).take j).flatMap (chunk d B p w) :=by
 induction j with
 | zero=>rfl
 | succ j ih=>
   by_cases hj:j<d.count
   · rw [stream,dif_pos hj,ih,List.take_succ_eq_append_getElem (by simpa using hj),List.flatMap_append]
     simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.getElem_ofFn]
     rw [factor_eq d B p j (by omega)]
     rfl
   · rw [stream,dif_neg hj,ih]
     rw [List.take_of_length_le (by simp;omega),List.take_of_length_le (by simp;omega)]

theorem stream_four (d :Data) (B p w :Nat):
 stream d B p w 4=(List.ofFn (fun i :Fin d.count=>i)).flatMap (chunk d B p w) :=by
 rw [stream_take,List.take_of_length_le (by simpa using d.count_le)]

theorem blocks (d :Data) (B p w :Nat) (bits :(i :Fin d.count)→Fin (d.arity i)→Bool) (hp :0<p):
 stream d B p w 4=
 ((List.ofFn (fun i :Fin d.count=>i)).flatMap (fun i=>
  PCJ45bee56da9f34d5a_ExpandedThresholdStream.block ((d.gates i).get (d.selected i)) (bits i) ((B :Int)^i.val))).flatMap
  (fun t=>frame (binary w (FinalPrimeReduce.intResidue p t.1))) :=by
 rw [stream_four,List.flatMap_assoc]
 apply List.flatMap_congr
 intro i _
 exact PCJ45bee56da9f34d5a_PowerMeaning.block_exact B p w i.val ((d.gates i).get (d.selected i)) (bits i) hp
end
end PCJ45bee56da9f34d5a_FourfoldPowerMeaning
