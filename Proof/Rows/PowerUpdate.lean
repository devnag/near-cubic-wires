import Proof.Rows.PowerMoves
import Proof.Rows.PowerCleanup

/-! Actual in-place modular power update in the live coefficient-mapper bank.
The full binary B stays resident; no separate reduction or width narrowing is needed. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_PowerUpdate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey PCJ45bee56da9f34d5a_PowerBank
noncomputable section

def machine := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  PCJ45bee56da9f34d5a_PowerMoves.loadBase PCJ45bee56da9f34d5a_PowerProduct.machine)
  PCJ45bee56da9f34d5a_PowerCleanup.rewind) PCJ45bee56da9f34d5a_PowerMoves.replaceFactor)
  PCJ45bee56da9f34d5a_PowerCleanup.erase

theorem run (a B p w F U q pos : Nat) (source out : List Bool)
    (hp : 0 < p) (hpw : 2*p ≤ 2^w) (ha : a < 2^w) (hB : B < 2^w)
    (hU : 1024*(w+1)^2+2 ≤ U) :
    Step machine (1024*(w+1)^2+10*U+18*w+45) (heads pos out.length 0)
      (bank a B p w F U q source out (List.replicate U false) [])
      (heads pos out.length 0)
      (bank ((a*B)%p) B p w F U q source out (List.replicate U false) []) := by
  have hw : 4*w+3 ≤ U := by nlinarith
  have hframe : (frame (binary w ((a*B)%p))).length ≤ U := by
    simp only [frame_length,binary_length];omega
  have hcoef : (ZeroPadding.pad U (frame (binary w B))).length ≤ U := by
    simp only [ZeroPadding.pad_length,frame_length,binary_length];omega
  have load := PCJ45bee56da9f34d5a_PowerMoves.load_run a B p w F U q pos source out hw
  have product := PCJ45bee56da9f34d5a_PowerProduct.run a B p w F U q pos source out hp hpw ha hB hU
  have rewind := PCJ45bee56da9f34d5a_PowerCleanup.rewind_run a B p w F U q pos source out
    (ZeroPadding.pad U (frame (binary w B))) (frame (binary w ((a*B)%p))) hframe
  simp only [frame_length,binary_length] at rewind
  have replace := PCJ45bee56da9f34d5a_PowerMoves.replace_run a ((a*B)%p) B p w F U q pos source out
    (ZeroPadding.pad U (frame (binary w B))) hw
  have erase := PCJ45bee56da9f34d5a_PowerCleanup.erase_run ((a*B)%p) B p w F U q pos source out
    (ZeroPadding.pad U (frame (binary w B))) (frame (binary w ((a*B)%p))) hcoef hframe
  have all := (((load.seq product).seq rewind).seq replace).seq erase
  unfold machine
  convert all using 1;omega
end
end PCJ45bee56da9f34d5a_PowerUpdate
