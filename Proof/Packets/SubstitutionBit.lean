import Proof.Packets.SubstitutionAtom
import Proof.Packets.PhysicalBitCall
import Proof.Packets.VectorCounterDecrement

/-! One literal-mask position is consumed backwards. The actual unary code
counter is decremented, the source cursor moves left, and its actual bit
controls the atom lookup/multiplication call. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionBit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def H (position : Nat) : Fin 38→Nat := Fin.addCases (m:=37) (n:=1)
  (ArithmeticLookup.H 0) (fun _=>position)
def A (B R index : Nat) (left accumulator : List (List Bool))
    (atoms source : List Bool) : Fin 38→List Bool := Fin.addCases (m:=37) (n:=1)
  (ArithmeticLookup.A B R index left accumulator atoms) (fun _=>source)
def counterSlot : Fin 1→Fin 38 := ![35]
def sourceSlot : Fin 1→Fin 38 := ![37]
noncomputable def decrement := RecoveryFocus.machine counterSlot VectorCounter.decrement
noncomputable def sourceLeft := RecoveryFocus.machine sourceSlot (Completion.PhysicalDriverMoves.machine 1 .left)
noncomputable def atom := TapeEmbedding.machine 1 SubstitutionAtom.machine
noncomputable def conditional := PhysicalBitCall.machine (37 : Fin 38) atom
noncomputable def machine := Composition.machine decrement (Composition.machine sourceLeft conditional)
def budget (B R index : Nat) (selected accumulator : List (List Bool)) :=
  2*index+SubstitutionAtom.budget B R index selected accumulator+10

theorem decrement_run (B R index position : Nat) (left accumulator : List (List Bool))
    (atoms source : List Bool) (hR : index+2≤R) :
    Step decrement (2*index+4) (H position) (A B R (index+1) left accumulator atoms source)
      (H position) (A B R index left accumulator atoms source) := by
  have h := VectorCounter.decrement_padded index R hR
  apply PhysicalFocusBoundary.focus h counterSlot (by decide) (H position) (H position) _ _
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i away
    refine ⟨rfl,?_⟩
    fin_cases i <;> first | rfl | exact False.elim (away 0 rfl)

theorem sourceLeft_run (position : Nat) (a : Fin 38→List Bool) :
    Step sourceLeft 1 (H (position+1)) a (H position) a := by
  have h := Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>position+1) (fun _=>a 37)
  apply PhysicalFocusBoundary.focus h sourceSlot (by decide) (H (position+1)) (H position) a a
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;simp [sourceSlot,H,Fin.addCases,HeadMove.apply]
  · intro i;fin_cases i;rfl
  · intro i away
    refine ⟨?_,rfl⟩
    fin_cases i <;> first | rfl | exact False.elim (away 0 rfl)

theorem atom_run (B R index position : Nat) (left selected accumulator : List (List Bool))
    (pre post source : List Bool) (hpre : pre.length=2*index*R)
    (hleft : left.flatten.length≤R) (hleftCount : left.length+1≤R)
    (hselected : selected.flatten.length≤R) (hselectedCount : selected.length+1≤R)
    (hSelected : ∀ bits∈selected,bits.length=B) (hAcc : ∀ bits∈accumulator,bits.length=B)
    (ha : ∀ i,(ReusableArithmetic.data B selected accumulator i).length≤R)
    (hcap : NormalizedMultiply.budget B selected accumulator+3≤R) :
    let atoms := pre++ZeroPadding.pad R selected.flatten++
      ZeroPadding.pad R (CompareMachine.word selected.length)++post
    Step atom (SubstitutionAtom.budget B R index selected accumulator)
      (H position) (A B R index left accumulator atoms source)
      (H position) (A B R index selected (NormalizerOrder.ordered (MaskProduct.unions selected accumulator)) atoms source) :=
  (SubstitutionAtom.run B R index left selected accumulator pre post hpre hleft hleftCount
    hselected hselectedCount hSelected hAcc ha hcap).embed (fun _ : Fin 1=>position) (fun _=>source)

theorem run (B R index position : Nat) (left selected accumulator : List (List Bool))
    (pre post source : List Bool) (hpre : pre.length=2*index*R)
    (hleft : left.flatten.length≤R) (hleftCount : left.length+1≤R)
    (hselected : selected.flatten.length≤R) (hselectedCount : selected.length+1≤R)
    (hSelected : ∀ bits∈selected,bits.length=B) (hAcc : ∀ bits∈accumulator,bits.length=B)
    (ha : ∀ i,(ReusableArithmetic.data B selected accumulator i).length≤R)
    (hcap : NormalizedMultiply.budget B selected accumulator+3≤R) (hR : index+2≤R) :
    let atoms := pre++ZeroPadding.pad R selected.flatten++
      ZeroPadding.pad R (CompareMachine.word selected.length)++post
    let bit := readTapeBit source position
    Step machine (budget B R index selected accumulator)
      (H (position+1)) (A B R (index+1) left accumulator atoms source)
      (H position) (A B R index (if bit then selected else left)
        (if bit then NormalizerOrder.ordered (MaskProduct.unions selected accumulator) else accumulator) atoms source) := by
  dsimp only
  let atoms := pre++ZeroPadding.pad R selected.flatten++
      ZeroPadding.pad R (CompareMachine.word selected.length)++post
  have first := decrement_run B R index (position+1) left accumulator atoms source hR
  have second := sourceLeft_run position (A B R index left accumulator atoms source)
  have third : Step conditional (SubstitutionAtom.budget B R index selected accumulator+3)
      (H position) (A B R index left accumulator atoms source) (H position)
      (A B R index (if readTapeBit source position then selected else left)
        (if readTapeBit source position then NormalizerOrder.ordered (MaskProduct.unions selected accumulator)
          else accumulator) atoms source) := by
    cases hb : readTapeBit source position
    · simp only [Bool.false_eq_true,↓reduceIte]
      apply (PhysicalBitCall.run_false (p:=atom) (37 : Fin 38) (H position)
        (A B R index left accumulator atoms source) hb).enlarge
      omega
    · simp only [↓reduceIte]
      exact PhysicalBitCall.run_true (37 : Fin 38) hb
        (atom_run B R index position left selected accumulator pre post source hpre
          hleft hleftCount hselected hselectedCount hSelected hAcc ha hcap)
  have all := first.seq (second.seq third)
  convert all using 1 <;> first | rfl | (unfold budget;omega)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionBit
