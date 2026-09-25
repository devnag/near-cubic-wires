import Proof.Rows.ResidueProduct

/-! Paid width conversion closes the product consumer's wider-left-operand seam.
Both factors enter as their actual original framed binary words. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ResidueProductReady
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey RadixSemantics
noncomputable section

def slots : Fin 5→Fin 31:=![9,28,8,29,30]
def heads : Fin 31→Nat:=Fin.addCases (m:=28) (n:=3) (motive:=fun _=>Nat)
  PCJ45bee56da9f34d5a_ResidueProduct.heads (fun _=>0)
def input (W a p w cap D : Nat) (bits : List Bool) : Fin 31→List Bool:=
  Fin.addCases (m:=28) (n:=3) (motive:=fun _=>List Bool)
    (Function.update (PCJ45bee56da9f34d5a_ResidueProduct.input W a p w cap D bits) 8 [])
    (![frame (binary w a),[],[]] : Fin 3→List Bool)
def widen:=RecoveryFocus.machine slots ClockNormalize.machine
def product:=TapeEmbedding.machine 3 PCJ45bee56da9f34d5a_ResidueProduct.machine
def machine:=Composition.machine widen product

theorem run (W a p w cap D : Nat) (bits : List Bool) (hwidth : w≤W) (ha : a<2^w)
    (hfit : a*2^bits.length<2^W) (hp : 0<p) (hpw : 2*p≤2^w)
    (hprep : 4*W+2≤D) (hc : 2*w+2≤cap)
    (hD : FinalPrimeResidue.fuel w (2*W)≤D) (hs : 2*w+2≤D) :
    ∃ output : Fin 31→List Bool,
      Step machine (4*W+4+1+(HierarchyMultiplyEntry.budget W bits+1+(16*W+9)+1+
          C10NativeSignedResidue.budget w (2*W))) heads (input W a p w cap D bits)
        heads output ∧ output 19=frame (binary w ((a*value bits)%p)) :=by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,_⟩:=ClockScalarFields.scalar_run W (binary w a)
    (by simpa only [binary_length] using hwidth)
  rw [binary_value w a ha] at h2
  have ht : r.final.tapes=![List.replicate W true,frame (binary w a),frame (binary W a),
      [true],List.replicate (2*W+1) false] :=by
    funext i;fin_cases i <;>assumption
  have raw:=(Step.of_run hr (funext hh) ht).dock slots (by decide) heads
    (input W a p w cap D bits) (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  let extra : Fin 3→List Bool:=![frame (binary w a),[true],List.replicate (2*W+1) false]
  let A : Fin 31→List Bool:=Fin.addCases (m:=28) (n:=3) (motive:=fun _=>List Bool)
    (PCJ45bee56da9f34d5a_ResidueProduct.input W a p w cap D bits) extra
  have first : Step widen (4*W+4) heads (input W a p w cap D bits) heads A :=by
    apply raw.congr (dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl))
    funext i;fin_cases i <;>first
      | exact install_slot slots (by decide) _ _ 0
      | exact install_slot slots (by decide) _ _ 1
      | exact install_slot slots (by decide) _ _ 2
      | exact install_slot slots (by decide) _ _ 3
      | exact install_slot slots (by decide) _ _ 4
      | exact (install_other slots _ _ _ (by decide)).trans rfl
  obtain ⟨out,h,hout⟩:=PCJ45bee56da9f34d5a_ResidueProduct.run W a p w cap D bits
    hfit hp hpw hprep hc hD hs
  have last:=h.embed (fun _ : Fin 3=>0) extra
  refine ⟨_,first.seq last,?_⟩
  exact hout

end
end PCJ45bee56da9f34d5a_ResidueProductReady
