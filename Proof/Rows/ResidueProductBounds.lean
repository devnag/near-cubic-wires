import Proof.Rows.ResidueProductReady

/-! A complete width-only cost/cap specialization of the physical modular
product producer, including its paid left-factor widening. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ResidueProductBounds
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.CloseoutFinal
open SignedSortKey RadixSemantics
noncomputable section

def resetCap (w : Nat):=32*(w+1)^2

theorem run_fits (a b p w : Nat) (hp : 0<p) (hpw : 2*p≤2^w) (ha : a<2^w) (hb : b<2^w) :
    ∃ output : Fin 31→List Bool,
      Step PCJ45bee56da9f34d5a_ResidueProductReady.machine (1024*(w+1)^2)
        PCJ45bee56da9f34d5a_ResidueProductReady.heads
        (PCJ45bee56da9f34d5a_ResidueProductReady.input (2*w+1) a p w (2*w+2)
          (resetCap w) (binary w b))
        PCJ45bee56da9f34d5a_ResidueProductReady.heads output ∧
      output 19=frame (binary w ((a*b)%p)) :=by
  have ha' : a<2^w:=ha
  have hb' : b<2^w:=hb
  have hfit : a*2^(binary w b).length<2^(2*w+1) :=by
    rw [binary_length,show 2*w+1=w+w+1 by omega,pow_succ,pow_add]
    have h:=Nat.mul_lt_mul_of_pos_right ha' (by positivity : 0<2^w)
    omega
  obtain ⟨out,h,hout⟩:=PCJ45bee56da9f34d5a_ResidueProductReady.run
    (2*w+1) a p w (2*w+2) (resetCap w) (binary w b) (by omega) ha' hfit hp hpw
    (by unfold resetCap;nlinarith) le_rfl
    (by rw [FinalPrimeResidue.fuel_value];unfold resetCap;nlinarith)
    (by unfold resetCap;nlinarith)
  refine ⟨out,h.enlarge ?_,?_⟩
  · unfold HierarchyMultiplyEntry.budget C10NativeSignedResidue.budget
    rw [binary_length,FinalPrimeResidue.fuel_value]
    nlinarith
  · simpa only [binary_value w b hb'] using hout

end
end PCJ45bee56da9f34d5a_ResidueProductBounds
