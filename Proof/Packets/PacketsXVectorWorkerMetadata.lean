import Proof.Packets.PacketsXVectorWorkerCleanup
import Proof.Packets.PacketsXVectorWorkerReuse

/-! Full retained-master contract for repeated numeric work in the296-port
child worker. This records all five physical masters, not just output frames. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open RecoveryRootRound
noncomputable section

theorem metadata_run_full (R u n w parent child : Nat) (A : Fin 296→List Bool)
    (hin : ∀j,A (metadataSlots j)=DeltaScalarFields.input R u n w parent child j)
    (hn : n<2^u) (hsum : min n w+parent<2^u) (hc : 2*child<2^u) (hw : 2*w<2^u)
    (hR : DeltaTargetGuard.budget u+1≤R) (hN : n+2≤R) :
    ∃ T,Step metadataMachine (DeltaMetadata.budget u n w parent child) heads A heads T ∧
      (∀j : Fin 5,T (metadataSlots (j.castAdd 20))=A (metadataSlots (j.castAdd 20))) ∧
      T 180=DeltaScalarFields.fw R u (n-w) ∧ T 181=DeltaScalarFields.fw R u (2*w) ∧
      T 182=DeltaScalarFields.fw R u
        (CompetitorSignedResidue.residue u u (min n w+parent) (2*child)) ∧
      T 276=ZeroPadding.pad R [decide (2*child≤ min n w+parent)] ∧
      T 279=ZeroPadding.pad R [decide (CompetitorSignedResidue.residue u u (min n w+parent) (2*child)≤2*w)] ∧
      (∀i,(∀j,metadataSlots j≠i)→T i=A i) := by
  obtain ⟨B,hb,hkept,h11,h12,h19,h21,h23,_hlen⟩:=DeltaMetadata.run R u n w parent child hn hsum hc hw hR hN
  have run:=hb.dock metadataSlots (by decide) heads A
    (by intro j;fin_cases j <;>rfl) hin
  rw [dockH_existing metadataSlots heads DeltaScalarFields.heads (by intro j;fin_cases j <;>rfl)] at run
  refine ⟨install metadataSlots A B,run,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    have hj : (j.castAdd 20 : Fin 25)≤7 := by change j.val≤7;omega
    have old:=hkept (j.castAdd 20) hj
    have retained : B (j.castAdd 20)=DeltaScalarFields.input R u n w parent child (j.castAdd 20) := by
      fin_cases j <;>simpa [DeltaScalarFields.splitData,Function.update] using old
    exact (install_slot metadataSlots (by decide) A B (j.castAdd 20)).trans
      (retained.trans (hin (j.castAdd 20)).symm)
  · exact (install_slot metadataSlots (by decide) A B 11).trans h11
  · exact (install_slot metadataSlots (by decide) A B 12).trans h12
  · exact (install_slot metadataSlots (by decide) A B 21).trans h21
  · exact (install_slot metadataSlots (by decide) A B 19).trans h19
  · exact (install_slot metadataSlots (by decide) A B 23).trans h23
  · intro i away;exact install_other metadataSlots A B i away

/-- Every numeric private word fits the next physical erase sweep. -/
theorem private_fit {s fuel R : Nat} {p : Machine 296 s} {A B : Fin 296→List Bool}
    (hp : Step p fuel heads A heads B) (ha : ∀j,(A (scratch j)).length≤R)
    (hr : fuel+1≤R) : ∀j,(B (scratch j)).length≤R := by
  intro j
  apply P1Closure.LocalSupport.step_fits hp (scratch j) R (ha j)
  rw [scratch_head];omega

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
