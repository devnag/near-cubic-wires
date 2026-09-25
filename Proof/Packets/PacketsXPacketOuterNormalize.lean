import Proof.Packets.PacketsXReusableArithmeticNat
import Proof.Packets.PacketsXSubstitutionCensus
import Proof.Packets.PhysicalEraseInto

/-! The final packet's outer normalization is executed literally. Even a
normal input must be normalized again: this reverses its monomial list.
The old left operand is physically cleared before the existing addition
worker folds the right operand into zero. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketOuterNormalize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
open ReusableArithmetic (heads state natState)
attribute [local irreducible] ReusableArithmetic.machine NormalizedAddition.machine PhysicalEraseInto.machine

def clearSlots : Fin 4→Fin 34 := ![25,28,32,33]
noncomputable def clearLeft := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
attribute [local irreducible] clearLeft

theorem clear_left (C R : Nat) (left right : List (List Bool))
    (hR : 1≤R) (hl : left.flatten.length≤R) (hn : left.length+1≤R) :
    Step clearLeft (2*R+4) heads (state C R left right) heads (state C R [] right) := by
  have hl' : (ZeroPadding.pad R left.flatten).length≤R := by
    rw [ZeroPadding.pad_length,Nat.max_eq_left hl]
  have hn' : (ZeroPadding.pad R (CompareMachine.word left.length)).length≤R := by
    rw [ZeroPadding.pad_length,Nat.max_eq_left (by simpa [CompareMachine.word] using hn)]
  have hz : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := by
    change ZeroPadding.pad R (List.replicate 1 false)=_
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hR]
  obtain ⟨r,hr,ht,hh,hs⟩:=RecoveryScratchErase.erase_ready R (R+3)
    (![ZeroPadding.pad R left.flatten,ZeroPadding.pad R (CompareMachine.word left.length)] : Fin 2→List Bool)
    (by intro i;fin_cases i;exact hl';exact hn')
  have small : Step (RecoveryScratchErase.resetMachine 2) (2*R+4) (fun _=>0) _ (fun _=>0) _ :=
    ⟨r,hr,funext hh,ht,hs.le⟩
  unfold clearLeft
  apply PhysicalFocusBoundary.focus small clearSlots (by decide) heads heads
    (state C R left right) (state C R [] right)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i
    · rfl
    · exact hz.symm
    · rfl
    · change List.replicate (max (R+3) (R+1)) false=List.replicate (R+3) false
      rw [Nat.max_eq_left (by omega : R+1≤R+3)]
  · intro i away
    have h25 : i≠25 := by intro he;exact away 0 he.symm
    have h28 : i≠28 := by intro he;exact away 1 he.symm
    have he:=VectorAccumulator.tapes_left_outside C R left right [] [] (i.castAdd 2)
      (fun h=>h25 (Fin.ext (congrArg (fun j : Fin 36=>j.val) h)))
      (fun h=>h28 (Fin.ext (congrArg (fun j : Fin 36=>j.val) h)))
    exact ⟨rfl,by simpa only [VectorAccumulator.tapes_engine] using he⟩


attribute [local irreducible] ReusableArithmetic.state

theorem add_zero_eq_norm (P : Ring.Poly Nat) (hP : Ring.Normal P) : Ring.add [] P=Ring.norm P := by
  symm
  simpa only [List.reverse_nil,List.nil_append] using
    NormalizerOrder.add_raw [] P (by simp [Ring.Normal]) hP

noncomputable def machine := Composition.machine clearLeft (ReusableArithmetic.machine NormalizedAddition.machine)
def budget (C R : Nat) (P : Ring.Poly Nat) :=
  2*R+5+ReusableArithmetic.budget (NormalizedAddition.budget C [] (P.map (maskNat C))) R
attribute [local irreducible] machine

theorem run (C w : Nat) (left P : Ring.Poly Nat)
    (hw : 1≤w) (hP : Ring.Normal P) (hf : Fits C P)
    (hl : left.length≤2^w) (hc : P.length≤2^w) :
    Step machine (budget C (commonReserve C w) P)
      heads (natState C (commonReserve C w) left P)
      heads (natState C (commonReserve C w) [] (Ring.norm P)) := by
  have hleft:=SubstitutionCensus.packet_fits C w (left.map (maskNat C))
    (SubstitutionCensus.mask_width C left) (by simpa only [List.length_map] using hl)
  have ha:=arithmetic_input_reserve C w [] (P.map (maskNat C)) (by simp)
    (SubstitutionCensus.mask_width C P) (by simp) (by simpa only [List.length_map] using hc)
  have hcap:=normalized_addition_reserve C w [] (P.map (maskNat C)) (by simp)
    (SubstitutionCensus.mask_width C P) (by simp) (by simpa only [List.length_map] using hc) hw
  have first:=clear_left C (commonReserve C w) (left.map (maskNat C)) (P.map (maskNat C))
    (by have h:=hleft.2.2;omega) hleft.2.1 hleft.2.2
  have second:=ReusableArithmetic.nat_add C (commonReserve C w) [] P (by simp [Fits]) hf ha
    (by simp [Ring.Normal]) hP hcap
  rw [add_zero_eq_norm P hP] at second
  have all:=first.seq second
  have he : (2*commonReserve C w+4)+1+
      ReusableArithmetic.budget (NormalizedAddition.budget C [] (P.map (maskNat C)))
        (commonReserve C w)=budget C (commonReserve C w) P := by
    unfold budget
    omega
  simp only [List.map_nil] at all
  rw [he] at all
  unfold machine
  exact all

end PCJ9eff70d512234a4c_Fixed.Materializer.PacketOuterNormalize
