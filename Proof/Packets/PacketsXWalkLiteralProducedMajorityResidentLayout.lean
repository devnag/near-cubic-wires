import Proof.Packets.PacketsXWalkLiteralProducedMajorityColumn

/-! Abstract finite column-layout fact, kept independent of the large walk
output expressions so kernel reduction does not expand their computations. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedMajority
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section
attribute [local irreducible] MajorityComplete.Cold.scalarOutput

theorem pad_compare_zero (S : Nat) (hs : 1≤S) :
    List.replicate S false=ZeroPadding.pad S (CompareMachine.word 0) := by
  have hn : 1+(S-1)=S := by omega
  simp only [ZeroPadding.pad,CompareMachine.word,List.replicate_zero,List.length_singleton]
  rw [←List.replicate_one (a:=false),←List.replicate_add,hn]

theorem scalar_zero_column (C R S N n : Nat) (A : Fin 742→List Bool) (source payload count : List Bool)
    (hs : 1≤S)
    (pin : ∀i : Fin 6,A (columnSlots (i.castAdd 3))=
      TranscriptColumn.residentTapes R N (n+1) 0 S source payload count [] (i.castAdd 3)) :
    ∀i,scalarBank C R n (zeroBank S A) (columnSlots i)=
      TranscriptColumn.residentTapes R N (n+1) 0 S source payload count [] i := by
  have outside (i : Fin 9) (h6:i≠6) (h7:i≠7) (h8:i≠8) :
      scalarBank C R n (zeroBank S A) (columnSlots i)=A (columnSlots i) := by
    have hc : ∀j,coldSlots j≠columnSlots i := by
      intro j he
      rcases column_cold_overlap i j he.symm with hp|hp
      · exact h6 hp.1
      · exact h7 hp.1
    have hz : ∀j,zeroSlots j≠columnSlots i := by
      have all : ∀i j,zeroSlots j=columnSlots i→i=8 := by decide
      intro j he
      exact h8 (all i j he)
    rw [scalarBank,install_other _ _ _ _ hc,zeroBank,install_other _ _ _ _ hz]
  intro i;fin_cases i
  · exact (outside 0 (by decide) (by decide) (by decide)).trans (pin 0)
  · exact (outside 1 (by decide) (by decide) (by decide)).trans (pin 1)
  · exact (outside 2 (by decide) (by decide) (by decide)).trans (pin 2)
  · exact (outside 3 (by decide) (by decide) (by decide)).trans (pin 3)
  · exact (outside 4 (by decide) (by decide) (by decide)).trans (pin 4)
  · exact (outside 5 (by decide) (by decide) (by decide)).trans (pin 5)
  · exact (install_slot coldSlots cold_injective (zeroBank S A) (MajorityComplete.Cold.afterScalar C R n []) 44).trans
      (cold_scalar_source C R n [])
  · exact (install_slot coldSlots cold_injective (zeroBank S A) (MajorityComplete.Cold.afterScalar C R n []) 146).trans
      (MajorityComplete.Cold.afterScalar_count C R n [])
  · have hc:=install_other coldSlots (zeroBank S A) (MajorityComplete.Cold.afterScalar C R n [])
      (567 : Fin 742) (by decide)
    have hz:=install_slot zeroSlots (by decide) A (zeroWords S) 0
    exact (hc.trans hz).trans (pad_compare_zero S hs)

theorem six_column_pin (R S N n : Nat) (A : Fin 742→List Bool) (source payload count : List Bool)
    (h0 : A 156=ZeroPadding.pad S (UnaryTemplate.tape R)) (h1 : A 426=source)
    (h2 : A 382=ZeroPadding.pad S payload) (h3 : A 388=ZeroPadding.pad S count)
    (h4 : A 422=ZeroPadding.pad S (CompareMachine.word N)) (h5 : A 386=List.replicate S false) :
    ∀i : Fin 6,A (columnSlots (i.castAdd 3))=
      TranscriptColumn.residentTapes R N (n+1) 0 S source payload count [] (i.castAdd 3) := by
  intro i;fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end
end Theorem25Completion.WalkLiteralProducedMajority
