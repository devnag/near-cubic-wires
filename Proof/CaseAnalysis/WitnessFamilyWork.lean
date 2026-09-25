import Proof.CaseAnalysis.WitnessFamilyReader

/-! The actual outer count enters its sentinel with one paid move and
then drives the unchanged complete family loop. Header workspace stays
outside the loop; its existing allocation is neither scanned nor copied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyWork
open LocalBitMultitape RecoveryRootRound
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def heads {s : ℕ} (source : Configuration 3063 s) (driver : ℕ) : Fin 3241 → ℕ:=
  Fin.addCases (m:=3064) (n:=177) (motive:=fun _=>ℕ)
    (Fin.addCases (m:=3063) (n:=1) (motive:=fun _=>ℕ) source.heads (fun _=>driver)) (fun _=>0)
def tapes {s : ℕ} (H total : ℕ) (source : Configuration 3063 s) (extra : Fin 177 → List Bool) : Fin 3241 → List Bool:=
  Fin.addCases (m:=3064) (n:=177) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=3063) (n:=1) (motive:=fun _=>List Bool) source.tapes
      (fun _=>ZeroPadding.pad H (CompareMachine.word total))) extra
def directions (i : Fin 3241) : HeadMove:=if i=3063 then .right else .stay
def move:=DecompositionCountPosition.move directions
def budget (cost total : ℕ):=total*(cost+3)+5

private theorem move_heads {s : ℕ} (source : Configuration 3063 s) :
    (fun i=>(directions i).apply (heads source 0 i))=heads source 1 := by
  funext i
  refine Fin.addCases (m:=3064) (n:=177) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=3063) (n:=1) ?_ ?_ j
    · intro j
      have hj:(j.castAdd 1).castAdd 177≠(3063 : Fin 3241):=by
        intro h;have hv:=congrArg Fin.val h;change j.val=3063 at hv;omega
      simp only [directions,if_neg hj,HeadMove.apply,heads,Fin.addCases_left]
    · intro j;fin_cases j;rfl
  · intro j
    have hj:j.natAdd 3064≠(3063 : Fin 3241):=by
      intro h;have hv:=congrArg Fin.val h;change 3064+j.val=3063 at hv;omega
    simp only [directions,if_neg hj,HeadMove.apply,heads,Fin.addCases_right]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyWork
