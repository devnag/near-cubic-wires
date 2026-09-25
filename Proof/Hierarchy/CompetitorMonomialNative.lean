import Proof.Hierarchy.CompetitorMonomialPrepare

/-! Exact docking of the paid monomial-record preparation to the accepted
native multiplication/widening/append run, retaining both ambient cursors
and the next iteration's physical scratch-support bound. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlot (i : Fin 79) : Fin 88 := i.castAdd 9
noncomputable def nativeProgram := RecoveryFocus.machine nativeSlot CompetitorMonomialTarget.machine

theorem native_injective : Function.Injective nativeSlot := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 88 => a.val) h)
theorem native_other (j : Fin 79) (i : Fin 88) (hi : 79 ≤ i.val) : nativeSlot j≠i := by
  intro h
  have hv := congrArg Fin.val h
  change j.val=i.val at hv
  omega

theorem native_heads {s : ℕ} (q : Fin s) (oldOutput output : List Bool) (pos : ℕ)
    (ambient : Fin 88 → List Bool) (localTapes : Fin 79 → List Bool) :
    (RecoveryFocus.config nativeSlot (heads oldOutput.length pos) ambient
      (⟨q,CompetitorMonomialTarget.targetHeads output,localTapes⟩ : Configuration 79 s)).heads=heads output.length pos := by
  funext i
  by_cases hi : i.val<79
  · let j : Fin 79 := ⟨i.val,hi⟩
    have he : nativeSlot j=i := Fin.ext rfl
    have hp : RecoveryFocus.pick nativeSlot i=some j := he ▸ RecoveryFocus.pick_slot nativeSlot native_injective j
    simp only [RecoveryFocus.config,hp]
    change (if j.val=74 then output.length else 0)=heads output.length pos i
    have hn79 : i.val≠79 := by omega
    simp [heads,hn79,j]
  · have hn : ¬∃ j,nativeSlot j=i := by rintro ⟨j,hj⟩; exact native_other j i (by omega) hj
    simp only [RecoveryFocus.config,RecoveryFocus.pick,hn,↓reduceDIte]
    simp [heads,show i.val≠74 by omega]

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
