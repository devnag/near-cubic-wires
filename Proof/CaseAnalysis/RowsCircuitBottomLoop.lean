import Proof.CaseAnalysis.RowsCircuitBottomRound

/-! The actual serialized bottom count drives the complete reusable worker.
Every original field is parsed once; only retained fields emit native words,
and the source, membership, output and resource cursors remain explicit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomLoop
open LocalBitMultitape RadixSemantics CloseoutRowsCircuitBottom CloseoutRowsFamilyLoop
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def total (cost : ℕ→ℕ) (initial j : ℕ):=initial+((List.range j).map cost).sum
theorem total_succ (cost : ℕ→ℕ) (initial j : ℕ) :
    total cost initial (j+1)=total cost initial j+cost j:=by
  simp [total,List.range_succ,Nat.add_assoc]
def validity (core : ℕ) (flag : Bool) (words : List (List Bool)) (j : ℕ):=
  flag && (List.range j).all (fun k=>passed core (words.getD k []))
theorem validity_succ (core : ℕ) (flag : Bool) (words : List (List Bool)) (j : ℕ) :
    validity core flag words (j+1)=(validity core flag words j && passed core (words.getD j [])):=by
  simp [validity,List.range_succ,Bool.and_assoc]
def choose (threshold : Bool) (membership : List Bool) (memberPos j : ℕ):=
  kept threshold membership (memberPos+2*j)
def outputs (threshold : Bool) (core memberPos : ℕ) (membership : List Bool)
    (words : List (List Bool)) (j : ℕ):=
  emitted core (choose threshold membership memberPos j) (words.getD j [])
def descriptions (core : ℕ) (words : List (List Bool)) (initial j : ℕ):=
  total (fun k=>descriptionCost core (words.getD k [])) initial j
def wires (threshold : Bool) (core memberPos : ℕ) (membership : List Bool)
    (words : List (List Bool)) (initial j : ℕ):=
  total (fun k=>wireCost core (choose threshold membership memberPos k) (words.getD k [])) initial j
noncomputable def machine (threshold : Bool):=CloseoutRowsDegreeLoop.machine (round threshold)

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomLoop
