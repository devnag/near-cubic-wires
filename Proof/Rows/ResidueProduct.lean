import Proof.Rows.FinalNativeResidueInput
import Proof.Rows.FinalNativeSignedResidue
import Proof.Rows.Plan

/-! A paid framed-binary product followed by physical MSB conversion and
modular reduction. The left operand has the actual product width; a caller
must pay ClockScalarFields to widen a shorter residue before this boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ResidueProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey RadixSemantics
noncomputable section

def prepareSlots : Fin 6→Fin 28:=![3,14,15,16,17,18]
def reduceSlots : Fin 10→Fin 28:=![19,20,21,22,17,23,24,25,26,27]
def heads : Fin 28→Nat:=fun i=>if i=24 then 1 else 0
def extraHeads : Fin 14→Nat:=fun i=>if i=10 then 1 else 0
def extras (W p w cap D : Nat) : Fin 14→List Bool:=
  ![[],[],List.replicate D false,[],[],frame (binary w 0),frame (binary w 0),
    frame (binary w p),[false],List.replicate cap false,CompareMachine.word (2*W),
    frame (binary w 0),[false],List.replicate D false]
def input (W a p w cap D : Nat) (bits : List Bool) : Fin 28→List Bool:=
  Fin.addCases (m:=14) (n:=14) (motive:=fun _=>List Bool)
    (HierarchyMultiplyEntry.input14 W a bits) (extras W p w cap D)
def multiply:=TapeEmbedding.machine 14 HierarchyMultiplyEntry.machine
def preparation:=Composition.machine (TapeEmbedding.machine 2
    (MaskedReset.machine RecoveryRadixInput.machine (fun _=>true)))
    (RecoveryFocus.machine (![1,4,5] : Fin 3→Fin 6) Streaming.machine)
def prepare:=RecoveryFocus.machine prepareSlots preparation
def reduce:=RecoveryFocus.machine reduceSlots C10NativeSignedResidue.machine
def machine:=Composition.machine (Composition.machine multiply prepare) reduce

/-- The computed product is consumed directly by the reducer. No native-int
recoding or externally supplied product/residue appears in the input. -/
theorem run (W a p w cap D : Nat) (bits : List Bool)
    (hfit : a*2^bits.length<2^W) (hp : 0<p) (hpw : 2*p≤2^w)
    (hprep : 4*W+2≤D) (hc : 2*w+2≤cap)
    (hD : FinalPrimeResidue.fuel w (2*W)≤D) (hs : 2*w+2≤D) :
    ∃ output : Fin 28→List Bool,
      Step machine (HierarchyMultiplyEntry.budget W bits+1+(16*W+9)+1+
          C10NativeSignedResidue.budget w (2*W)) heads (input W a p w cap D bits)
        heads output ∧
      output 19=frame (binary w ((a*value bits)%p)) :=by
  obtain ⟨r,hr,hproduct,_,_,_,_,hh,_⟩:=HierarchyMultiplyEntry.multiply_run W a bits hfit
  have first:=(Step.of_run hr (funext hh) rfl).embed extraHeads (extras W p w cap D)
  let A : Fin 28→List Bool:=Fin.addCases (m:=14) (n:=14) (motive:=fun _=>List Bool)
    r.final.tapes (extras W p w cap D)
  have first' : Step multiply (HierarchyMultiplyEntry.budget W bits) heads
      (input W a p w cap D bits) heads A :=by
    refine (first.congr_in ?_ rfl).congr ?_ rfl
    all_goals funext i;fin_cases i <;>rfl
  let product:=binary W (a*value bits)
  have product_len : product.length=W:=binary_length _ _
  have prep:=(C10NativeResidueInput.prepare_unwrap product D (by simpa only [product_len] using hprep)).dock
    prepareSlots (by decide) heads A (by intro i;fin_cases i <;>rfl) (by
      intro i;fin_cases i
      · exact hproduct
      all_goals rfl)
  let prepared : Fin 6→List Bool:=![frame product,frame (RecoveryRadixInput.prepared product),
    List.replicate (2*W) false,List.replicate D false,RecoveryRadixInput.prepared product,
    List.replicate (2*W) false]
  let B:=install prepareSlots A prepared
  have prep' : Step prepare (16*W+9) heads A heads B :=by
    rw [product_len] at prep
    exact prep.congr (dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)) rfl
  obtain ⟨reduced,red,word,_,_⟩:=C10NativeSignedResidue.run p w cap (2*W) D
    (RecoveryRadixInput.prepared product) false hc hD hs
  have last:=red.dock reduceSlots (by decide) heads B
    (by intro i;fin_cases i <;>rfl) (by
      intro i;fin_cases i <;>first
        | exact install_slot prepareSlots (by decide) _ _ 4
        | exact (install_other prepareSlots _ _ _ (by decide)).trans rfl)
  have last':=last.congr (dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)) rfl
  have whole:=(first'.seq prep').seq last'
  refine ⟨_,whole,?_⟩
  have hword:=C10NativeSignedResidue.word_eq p w (2*W) (RecoveryRadixInput.prepared product) false hp hpw
  simp only [Bool.false_eq_true,↓reduceIte] at word hword
  have hhword:=C10NativeResidueInput.prepared_horner product
  rw [product_len] at hhword
  have hval : value product=a*value bits:=binary_value _ _
    (lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_lt (value_lt bits))) hfit)
  rw [hhword,hval] at hword
  exact (install_slot reduceSlots (by decide) _ _ 0).trans (word.trans (congrArg frame hword))

end
end PCJ45bee56da9f34d5a_ResidueProduct
