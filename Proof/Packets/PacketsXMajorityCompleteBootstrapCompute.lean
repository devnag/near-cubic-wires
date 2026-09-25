import Proof.Packets.PacketsXMajorityCompleteBootstrapLayout
import Proof.Packets.PacketsXMajorityCompleteHeads
import Proof.Packets.PacketsXMajorityCompleteRun

/-! Dock the complete packet-majority program into its reusable arena. The
scalar masters, reset drivers and input column remain resident. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Bootstrap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning
open Completion.SourceDock
noncomputable section

def compute := RecoveryFocus.machine arenaSlots MajorityComplete.machine
def caps (S : Nat) (i : Fin 125) : Nat := if i=34∨i=124 then 0 else S
def finalWork (C R S : Nat) (ps : List Poly) (i : Fin 123) :=
  ZeroPadding.pad S (MajorityComplete.final C R ps (Palette.privatePort i))
def finalData (C R S : Nat) (ps : List Poly) :=
  data (Palette.words C R ps.length) S (OrderedPacketStep.bank C R ps) (finalWork C R S ps)

theorem source_final (C R : Nat) (ps : List Poly) :
    MajorityComplete.final C R ps 34=OrderedPacketStep.bank C R ps := by
  have hf : ∀j,foldSlots j≠34 := by decide
  have he : ∀j,enumSlots j≠34 := by decide
  rw [MajorityComplete.final,install_other foldSlots _ _ _ hf,
    enumerated,install_other enumSlots _ _ _ he]
  rfl

theorem square_final (C R : Nat) (ps : List Poly) :
    MajorityComplete.final C R ps 124=UnaryTemplate.tape (R^2) := by
  have hf : ∀j,foldSlots j≠124 := by decide
  have he : ∀j,enumSlots j≠124 := by decide
  rw [MajorityComplete.final,install_other foldSlots _ _ _ hf,
    enumerated,install_other enumSlots _ _ _ he]
  rfl

theorem ready_arena (C R : Nat) (ps : List Poly) (i : Fin 125) :
    readyData C R (R^2) ps (arenaSlots i)=ZeroPadding.pad (caps (R^2) i) (input C R ps i) := by
  by_cases hs : i=34
  · subst i
    rw [show arenaSlots 34=44 from rfl,readyData,source_data]
    simp only [caps,true_or,or_true,or_false,ite_true,ZeroPadding.pad_zero]
    rfl
  by_cases hw : i=124
  · subst i
    rw [show arenaSlots 124=134 from rfl,readyData,width_data]
    simp only [caps,or_true,ite_true,ZeroPadding.pad_zero]
    rfl
  obtain ⟨j,rfl⟩:=private_cover i hs hw
  rw [readyData,private_data]
  simp only [readyWork,caps,Palette.private_not_source,Palette.private_not_width,
    or_self,ite_false]

theorem final_arena (C R : Nat) (ps : List Poly) (i : Fin 125) :
    finalData C R (R^2) ps (arenaSlots i)=ZeroPadding.pad (caps (R^2) i)
      (MajorityComplete.final C R ps i) := by
  by_cases hs : i=34
  · subst i
    rw [show arenaSlots 34=44 from rfl,finalData,source_data]
    simp only [caps,true_or,or_true,or_false,ite_true,ZeroPadding.pad_zero,source_final]
  by_cases hw : i=124
  · subst i
    rw [show arenaSlots 124=134 from rfl,finalData,width_data]
    simp only [caps,or_true,ite_true,ZeroPadding.pad_zero,square_final]
  obtain ⟨j,rfl⟩:=private_cover i hs hw
  rw [finalData,private_data]
  simp only [finalWork,caps,Palette.private_not_source,Palette.private_not_width,
    or_self,ite_false]

theorem data_outside (palette : Fin 10→List Bool) (S : Nat) (source : List Bool)
    (work work' : Fin 123→List Bool) (i : Fin 137) (hi : ∀j,arenaSlots j≠i) :
    data palette S source work i=data palette S source work' i := by
  by_cases hsmall : i.val<10
  · let j : Fin 10:=⟨i.val,hsmall⟩
    have hj : j.castAdd 127=i:=Fin.ext rfl
    rw [←hj,master_data,master_data]
  have hlarge : (135 : Nat) ≤ i.val := by
    by_contra h
    have hv : i.val<135:=by omega
    let j : Fin 125:=⟨i.val-10,by omega⟩
    apply hi j
    apply Fin.ext
    simp only [arenaSlots,j,Fin.val_mk]
    omega
  have ha : i=135∨i=136 := by
    have hh:=i.isLt
    rcases (by omega : i.val=135∨i.val=136) with h|h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases ha with rfl|rfl
  · change install fanoutSlots _ _ (fanoutSlots 133)=install fanoutSlots _ _ (fanoutSlots 133)
    rw [install_slot fanoutSlots fanout_injective,install_slot fanoutSlots fanout_injective]
    rfl
  · change install fanoutSlots _ _ (fanoutSlots 134)=install fanoutSlots _ _ (fanoutSlots 134)
    rw [install_slot fanoutSlots fanout_injective,install_slot fanoutSlots fanout_injective]
    rfl

theorem payload_output (C R S : Nat) (ps : List Poly) :
    finalData C R S ps 122=ZeroPadding.pad S
      (PacketVector.payload R ((majority ps).map (maskNat C))) := by
  change finalData C R S ps (arenaSlots (Palette.privatePort 111))=_
  rw [finalData,private_data]
  change ZeroPadding.pad S (MajorityComplete.final C R ps 112)=_
  rw [output_payload]
theorem count_output (C R S : Nat) (ps : List Poly) :
    finalData C R S ps 123=ZeroPadding.pad S
      (PacketVector.count R ((majority ps).map (maskNat C))) := by
  change finalData C R S ps (arenaSlots (Palette.privatePort 112))=_
  rw [finalData,private_data]
  change ZeroPadding.pad S (MajorityComplete.final C R ps 113)=_
  rw [output_count]
theorem width_output (C R S : Nat) (ps : List Poly) :
    finalData C R S ps 127=ZeroPadding.pad S (UnaryTemplate.tape R) := by
  change finalData C R S ps (arenaSlots (Palette.privatePort 116))=_
  rw [finalData,private_data]
  change ZeroPadding.pad S (install foldSlots _ _ (foldSlots 31))=_
  rw [install_slot foldSlots fold_injective]
  rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Bootstrap
