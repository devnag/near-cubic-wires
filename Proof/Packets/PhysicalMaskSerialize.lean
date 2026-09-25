import Proof.MachineModel.Encoding
import Proof.MachineModel.Runs
import Proof.Packets.PhysicalMaskIndicesDefs
import Proof.Packets.PhysicalSupportReturn

/-! A fixed ordinary machine serializing an incidence mask into the exact
native monomial-word codec. The unary counter grows physically and is rewound
for every input bit; this paid implementation takes B² + 6B + 2 steps. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.PhysicalMaskSerialize
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch PhysicalMaskIndices

def scanState (selected : Bool) : Fin 7 := if selected then 2 else 3
def emitted (selected : Bool) (word : List Bool) : List Bool := if selected then word else []
def grown (count : Nat) : List Bool := false :: List.replicate (count+1) true

def machine : Machine 4 7 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==6
  rule := fun q bits => if q.val=0 then
      some ⟨1, ![none,none,none,some true], ![.stay,.stay,.stay,.right]⟩
    else if q.val=1 then some (if bits 0 then
      ⟨scanState (bits 1), fun _=>none, fun _=>.stay⟩ else
      ⟨6, ![none,none,none,some false], ![.stay,.stay,.stay,.right]⟩)
    else if q.val=2 ∨ q.val=3 then some (if bits 2 then
      ⟨q, ![none,none,none,if q.val=2 then some true else none],
        ![.stay,.stay,.right,if q.val=2 then .right else .stay]⟩ else
      ⟨4, ![none,none,some true,if q.val=2 then some false else none],
        ![.stay,.stay,.right,if q.val=2 then .right else .stay]⟩)
    else if q.val=4 then
      some ⟨5, ![none,none,some false,none], ![.stay,.stay,.left,.stay]⟩
    else if q.val=5 then some (if bits 2 then
      ⟨5, fun _=>none, ![.stay,.stay,.left,.stay]⟩ else
      ⟨1, fun _=>none, ![.right,.right,.right,.stay]⟩)
    else none

theorem write_last (pre : List Bool) (before after : Bool) :
    writeTapeBit (pre++[before]) pre.length after = pre++[after] := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simp [writeTapeBit,ih]

theorem grow_end (count : Nat) :
    writeTapeBit (UnaryTemplate.tape count) (count+1) true = grown count := by
  simpa [UnaryTemplate.tape,grown,List.replicate_succ'] using
    write_last (false::List.replicate count true) false true

end PCJ9eff70d512234a4c_Fixed.PhysicalMaskSerialize
