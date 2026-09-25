import Proof.Packets.GradedWindowMachine

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def raise := PhysicalIndexReload.move (7 : Fin 13) .right
def lower := PhysicalIndexReload.move (7 : Fin 13) .left
def machine := Composition.machine copyRoot (Composition.machine floor (Composition.machine raise
  (Composition.machine halves (Composition.machine lower (Composition.machine offset
    (Composition.machine clearValue clearQuotient))))))
def window (root level : Nat) := 64+GradedHalveRound.halve^[level/3] root
def budget (R root level : Nat) :=
  6*R+2*level+(level/3)*(8*R+22)+2*(GradedHalveRound.halve^[level/3] root)+164

theorem raise_run (R root level value Q out : Nat) :
    Step raise 1 (H 1 0) (A R root level value Q out) (H 1 1) (A R root level value Q out) := by
  have h:=PhysicalIndexReload.move_run (7 : Fin 13) .right (H 1 0) (A R root level value Q out)
  exact h.congr (by funext i;fin_cases i <;>rfl) rfl

theorem lower_run (R root level value Q out : Nat) :
    Step lower 1 (H 1 1) (A R root level value Q out) (H 1 0) (A R root level value Q out) := by
  have h:=PhysicalIndexReload.move_run (7 : Fin 13) .left (H 1 1) (A R root level value Q out)
  exact h.congr (by funext i;fin_cases i <;>rfl) rfl

theorem run (R root level : Nat) (hroot : root+67≤R) (hlevel : level+2≤R) :
    Step machine (budget R root level) (H 1 0) (A R root level 0 0 0)
      (H 1 0) (A R root level 0 0 (window root level)) := by
  let Q:=level/3
  let value:=GradedHalveRound.halve^[Q] root
  have hv : value≤root := GradedHalveRound.halve_iterate_le root Q
  have hQ : Q+1≤R := by dsimp [Q];omega
  have last:=(clear_value R root level value Q (64+value) (by omega)).seq
    (clear_quotient R root level 0 Q (64+value) hQ)
  have write:=(offset_run R root level value Q (by omega)).seq last
  have down:=(lower_run R root level value Q 0).seq write
  have halve:=(halves_run R root level root Q 0 (by omega)).seq down
  have up:=(raise_run R root level root Q 0).seq halve
  have quotient:=(floor_run R root level root 0 hlevel).seq up
  have whole:=(copy_root R root level (by omega)).seq quotient
  have hf : (2*R+2)+1+((2*level+10)+1+(1+1+(GradedHalveLoop.budget R Q+1+
      (1+1+((2*value+136)+1+((2*R+2)+1+(2*R+2)))))))=budget R root level := by
    unfold GradedHalveLoop.budget budget
    dsimp [Q,value]
    ring
  rw [hf] at whole
  exact whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
