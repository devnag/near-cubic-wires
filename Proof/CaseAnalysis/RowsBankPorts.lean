import Proof.CaseAnalysis.RowsBankClear
import Proof.CaseAnalysis.RowsPacketLoad

/-! The exact fixed packet port set is the whole native bank except its
growing output and the two shared erase resources. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankPorts
open LocalBitMultitape CloseoutRowsBankClear
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem work_complete (i : Fin 113) (h31 : i≠31) (h104 : i≠104) (h105 : i≠105) :
    ∃ j,work j=i := by
  have hn31 : i.val≠31 := fun h=>h31 (Fin.ext h)
  have hn104 : i.val≠104 := fun h=>h104 (Fin.ext h)
  have hn105 : i.val≠105 := fun h=>h105 (Fin.ext h)
  have hib := i.isLt
  by_cases h0 : i.val<31
  · let j : Fin 110:=⟨i.val,by omega⟩
    refine ⟨j,Fin.ext ?_⟩
    rw [work_val]
    simp [j,h0]
  · by_cases h1 : i.val<104
    · let j : Fin 110:=⟨i.val-1,by omega⟩
      refine ⟨j,Fin.ext ?_⟩
      rw [work_val]
      simp only [j]
      split_ifs <;> omega
    · let j : Fin 110:=⟨i.val-3,by omega⟩
      refine ⟨j,Fin.ext ?_⟩
      rw [work_val]
      simp only [j]
      split_ifs <;> omega

theorem erased_store (C : ℕ) (out : List Bool) (data : Fin 113→List Bool)
    (ho : data 31=out) (hs : ∀ i,data (slots i)=erased C i) : data=blank C out := by
  funext i
  by_cases h31 : i=31
  · subst i
    simpa only [blank,↓reduceIte] using ho
  by_cases h104 : i=104
  · subst i
    exact hs 110
  by_cases h105 : i=105
  · subst i
    exact hs 111
  obtain ⟨j,hj⟩ := work_complete i h31 h104 h105
  have he := hs ((j.castAdd 1).castAdd 1)
  rw [slots_work,hj] at he
  simpa only [erased,Fin.addCases_left,blank,h31,h104,h105,↓reduceIte] using he


theorem written_apply {t : ℕ} (fields : Fin t→List Bool) (C : ℕ)
    (js : List (Fin t)) (data : Fin t→List Bool) (i : Fin t) :
    CloseoutRowsPacketLoad.written fields C js data i=
      if i∈js then ZeroPadding.pad C (fields i) else data i := by
  induction js generalizing data with
  | nil => rfl
  | cons j js ih =>
    rw [CloseoutRowsPacketLoad.written,ih]
    by_cases hm : i∈js
    · simp [hm]
    · by_cases he : i=j
      · subst i
        simp [hm]
      · simp [hm,he]

end NearCubicWires.RepairOrdinary.CloseoutRowsBankPorts
