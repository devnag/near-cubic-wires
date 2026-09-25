import Proof.Packets.PacketVectorAppend
import Proof.Packets.PacketsXVectorLiteralPaletteBoot

/-! The physical coordinate-bank collector shares the literal-vector
workspace. Its only outside tape is the ordered time transcript. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
noncomputable section

def collectSlots : Fin 6 → Fin 317 := ![46,272,316,278,276,312]
def collectMachine := RecoveryFocus.machine collectSlots PacketVectorAppend.machine
def collectHeads (position : Nat) : Fin 317 → Nat :=
  Fin.addCases (m:=316) (n:=1) (motive:=fun _=>Nat)
    (paletteHeads VectorNumericArena.heads) (fun _=>position)
def collectOutput (S : Nat) (A : Fin 317 → List Bool) (transcript : List Bool) :=
  Function.update (Function.update A 272 (List.replicate S false)) 316 transcript

theorem collect_run (R S : Nat) (packets : List PacketVector.Packet) (pre rest : List Bool)
    (A : Fin 317 → List Bool)
    (hR : 1 ≤ R) (hRS : R ≤ S) (hpackets : ∀P∈packets,PacketVector.Fits R P)
    (hbank : (PacketVector.bank R packets).length ≤ S)
    (hpin : ∀j,A (collectSlots j)=PacketVectorAppend.paddedTapes R packets.length S
      (ZeroPadding.pad S (PacketVector.bank R packets))
      (pre++List.replicate (packets.length*(2*R)) false++rest) j) :
    Step collectMachine (PacketVectorAppend.budget R packets.length) (collectHeads pre.length) A
      (collectHeads (pre.length+packets.length*(2*R)))
      (collectOutput S A (pre++PacketVector.bank R packets++rest)) := by
  have run:=PacketVectorAppend.padded_run R S packets pre rest hR hRS hpackets hbank
  apply PhysicalFocusBoundary.focus run collectSlots (by decide)
    (collectHeads pre.length) (collectHeads (pre.length+packets.length*(2*R))) A
    (collectOutput S A (pre++PacketVector.bank R packets++rest))
  · intro j;fin_cases j <;>rfl
  · exact fun j=>(hpin j).symm
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j
    · simpa [collectOutput,collectSlots,PacketVectorAppend.paddedTapes] using (hpin 0).symm
    · rfl
    · rfl
    · simpa [collectOutput,collectSlots,PacketVectorAppend.paddedTapes] using (hpin 3).symm
    · simpa [collectOutput,collectSlots,PacketVectorAppend.paddedTapes] using (hpin 4).symm
    · simpa [collectOutput,collectSlots,PacketVectorAppend.paddedTapes] using (hpin 5).symm
  · intro i away
    have hs : i≠272 := by intro he;exact away 1 he.symm
    have ht : i≠316 := by intro he;exact away 2 he.symm
    constructor
    · revert ht
      refine Fin.addCases (m:=316) (n:=1) (fun j=>?_) (fun j=>?_) i
      · intro _;simp only [collectHeads,Fin.addCases_left]
      · fin_cases j;intro ht;exact False.elim (ht rfl)
    · simp only [collectOutput,Function.update_of_ne hs,Function.update_of_ne ht]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
