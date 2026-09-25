import Proof.Packets.PacketsXVectorWorkerBranch

/-! The physical validity bits drive precisely the original optional delta
target. Invalid coordinates take the actual zero branch. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
noncomputable section

theorem flags_of_some (R u n w parent child target : Nat) (A : Fin 296→List Bool)
    (hsum : min n w+parent<2^u)
    (hlo : A 276=ZeroPadding.pad R [decide (2*child≤ min n w+parent)])
    (hhi : A 279=ZeroPadding.pad R [decide (CompetitorSignedResidue.residue u u (min n w+parent) (2*child)≤2*w)])
    (ht : SupplierListPolynomial.deltaTarget? n w parent child=some target) :
    readTapeBit (A 276) 0=true ∧ readTapeBit (A 279) 0=true ∧
      CompetitorSignedResidue.residue u u (min n w+parent) (2*child)=target := by
  have htarget:=ht
  rw [C10ThresholdOneHotTargetArithmetic.target_option] at htarget
  split_ifs at htarget with hl hh
  · have he : min n w+parent-2*child=target := Option.some.inj htarget
    have hr:=C10ThresholdOneHotTargetArithmetic.residue_of_le u _ _ hsum hl
    refine ⟨?_,?_,hr.trans he⟩
    · rw [hlo,ZeroPadding.read_pad];simp [readTapeBit,List.getD,hl]
    · rw [hhi,ZeroPadding.read_pad];simp [readTapeBit,List.getD,hr,hh]

theorem flags_of_none (R u n w parent child : Nat) (A : Fin 296→List Bool)
    (hsum : min n w+parent<2^u)
    (hlo : A 276=ZeroPadding.pad R [decide (2*child≤ min n w+parent)])
    (hhi : A 279=ZeroPadding.pad R [decide (CompetitorSignedResidue.residue u u (min n w+parent) (2*child)≤2*w)])
    (ht : SupplierListPolynomial.deltaTarget? n w parent child=none) :
    readTapeBit (A 276) 0=false ∨ readTapeBit (A 279) 0=false := by
  by_cases hl:2*child≤ min n w+parent
  · right
    have hh:¬CompetitorSignedResidue.residue u u (min n w+parent) (2*child)≤2*w := by
      intro hh
      have bad:=(DeltaTargetGuard.flags_exact u n w parent child hsum).mp ⟨hl,hh⟩
      rw [ht] at bad
      contradiction
    rw [hhi,ZeroPadding.read_pad];simp [readTapeBit,List.getD,hh]
  · left;rw [hlo,ZeroPadding.read_pad];simp [readTapeBit,List.getD,hl]

theorem branch_none {s : Nat} (p : Machine 296 s) (R u n w parent child : Nat) (A : Fin 296→List Bool)
    (hw : A 31=UnaryTemplate.tape R) (hz : A 0=List.replicate R false)
    (hp : (A 26).length=R) (hc : (A 27).length=R)
    (hsum : min n w+parent<2^u)
    (hlo : A 276=ZeroPadding.pad R [decide (2*child≤ min n w+parent)])
    (hhi : A 279=ZeroPadding.pad R [decide (CompetitorSignedResidue.residue u u (min n w+parent) (2*child)≤2*w)])
    (ht : SupplierListPolynomial.deltaTarget? n w parent child=none) :
    Step (deltaBranch p) (4*R+11) heads A heads (rightZero R A) :=
  branch_invalid p R A hw hz hp hc (flags_of_none R u n w parent child A hsum hlo hhi ht)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
