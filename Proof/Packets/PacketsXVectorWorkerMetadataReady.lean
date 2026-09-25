import Proof.Packets.PacketsXVectorWorkerMetadata

/-! Repeated metadata calls accept the previous three scalar frames, clear
them with actual R-bit copies, and regenerate the exact next fields. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem reusable_metadata_run (R u n w parent child : Nat) (A : Fin 296→List Bool)
    (hwidth : A 31=UnaryTemplate.tape R) (hzero : A 0=List.replicate R false)
    (h180 : (A 180).length=R) (h181 : (A 181).length=R) (h182 : (A 182).length=R)
    (hin : ∀j,j≠11→j≠12→j≠21→A (metadataSlots j)=DeltaScalarFields.input R u n w parent child j)
    (hn : n<2^u) (hsum : min n w+parent<2^u) (hc : 2*child<2^u) (hw : 2*w<2^u)
    (hR : DeltaTargetGuard.budget u+1≤R) (hN : n+2≤R)
    (hbudget : DeltaMetadata.budget u n w parent child+1≤R) :
    ∃ T,Step reusableMetadata (6*R+9+DeltaMetadata.budget u n w parent child) heads A heads T ∧
      T 180=DeltaScalarFields.fw R u (n-w) ∧ T 181=DeltaScalarFields.fw R u (2*w) ∧
      T 182=DeltaScalarFields.fw R u
        (CompetitorSignedResidue.residue u u (min n w+parent) (2*child)) ∧
      T 276=ZeroPadding.pad R [decide (2*child≤ min n w+parent)] ∧
      T 279=ZeroPadding.pad R [decide (CompetitorSignedResidue.residue u u (min n w+parent) (2*child)≤2*w)] ∧
      (∀j,(T (scratch j)).length≤R) ∧
      (∀i,i≠180→i≠181→i≠182→(i.val < 264 ∨ 281 ≤ i.val)→T i=A i) := by
  have first:=clear_fields_run R A hwidth hzero h180 h181 h182
  obtain ⟨T,last,masters,f180,f181,f182,f276,f279,outside⟩:=metadata_run_full R u n w parent child
    (fieldsZero R A) (cleared_metadata_input R u n w parent child A hin) hn hsum hc hw hR hN
  have joined:=first.seq last
  have fuel : (6*R+8)+1+DeltaMetadata.budget u n w parent child=6*R+9+DeltaMetadata.budget u n w parent child := by omega
  rw [fuel] at joined
  refine ⟨T,joined,f180,f181,f182,f276,f279,?_,?_⟩
  · apply private_fit last _ hbudget
    intro j
    have hj : ∃k : Fin 25,metadataSlots k=scratch j ∧ k≠11 ∧ k≠12 ∧ k≠21 ∧ 5≤k.val := by
      fin_cases j <;> first
        | exact ⟨5,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨6,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨7,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨8,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨9,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨10,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨13,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨14,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨15,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨16,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨17,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨18,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨19,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨20,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨22,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨23,rfl,by decide,by decide,by decide,by decide⟩
        | exact ⟨24,rfl,by decide,by decide,by decide,by decide⟩
    obtain ⟨k,hk,h11,h12,h21,h5⟩:=hj
    rw [←hk,cleared_metadata_input R u n w parent child A hin k]
    have k0:k≠0 := by intro he;subst k;contradiction
    have k1:k≠1 := by intro he;subst k;contradiction
    have k2:k≠2 := by intro he;subst k;contradiction
    have k3:k≠3 := by intro he;subst k;contradiction
    have k4:k≠4 := by intro he;subst k;contradiction
    simp [DeltaScalarFields.input,k0,k1,k2,k3,k4]
  · intro i h180i h181i h182i hrange
    have cleared : fieldsZero R A i=A i := by
      simp only [fieldsZero,Function.update_of_ne h180i,Function.update_of_ne h181i,Function.update_of_ne h182i]
    by_cases selected : ∃j,metadataSlots j=i
    · obtain ⟨j,rfl⟩:=selected
      have hj : j.val<5 := by
        by_contra hh
        fin_cases j <;>simp [metadataSlots] at h180i h181i h182i hrange hh
      let k : Fin 5:=⟨j.val,hj⟩
      have he : k.castAdd 20=j := Fin.ext rfl
      rw [←he,masters,he,cleared]
    · exact (outside i (by simpa only [not_exists] using selected)).trans cleared

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
