import Proof.Rows.RowReady

/-! The paid Header scratch eraser used at the end of completion. All 430
mutable Header ports are swept in parallel. The eight metadata inputs, raw
source and packet driver are excluded; so are every Frame and other work port.
The current heads, true cap driver and zero log are explicit input obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ45bee56da9f34d5a_HeaderErase
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJd4d1d9d7d1fa4313_Production PCJ45bee56da9f34d5a_RowState
open PCJ9eff70d512234a4c_Fixed
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

def retained (k : Fin 440) : Prop :=
  k.val=0 ∨ k.val=3 ∨ k.val=4 ∨ k.val=15 ∨ k.val=88 ∨ k.val=262 ∨
  k.val=277 ∨ k.val=278 ∨ k.val=282 ∨ k.val=283

def mutable (i : Fin 430) : Fin 440 :=
  ⟨if i.val<2 then i.val+1 else if i.val<12 then i.val+3
    else if i.val<84 then i.val+4 else if i.val<257 then i.val+5
    else if i.val<271 then i.val+6 else if i.val<274 then i.val+8
    else i.val+10,by split_ifs <;> omega⟩

theorem mutable_injective : Function.Injective mutable := by
  intro i j h
  have hv := congrArg Fin.val h
  change (if i.val<2 then i.val+1 else if i.val<12 then i.val+3
    else if i.val<84 then i.val+4 else if i.val<257 then i.val+5
    else if i.val<271 then i.val+6 else if i.val<274 then i.val+8
    else i.val+10) =
    (if j.val<2 then j.val+1 else if j.val<12 then j.val+3
    else if j.val<84 then j.val+4 else if j.val<257 then j.val+5
    else if j.val<271 then j.val+6 else if j.val<274 then j.val+8
    else j.val+10) at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem mutable_not_retained (i : Fin 430) : ¬retained (mutable i) := by
  intro h
  unfold retained mutable at h
  dsimp only at h
  split_ifs at h <;> rcases h with h|h|h|h|h|h|h|h|h|h <;> omega


theorem mutable_covers (k : Fin 440) (hk : ¬retained k) : ∃ i,mutable i=k := by
  unfold retained at hk
  have hbound := k.isLt
  by_cases h1 : k.val<3
  · refine ⟨⟨k.val-1,by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [mutable]
    split_ifs <;> omega
  by_cases h2 : k.val<15
  · refine ⟨⟨k.val-3,by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [mutable]
    split_ifs <;> omega
  by_cases h3 : k.val<88
  · refine ⟨⟨k.val-4,by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [mutable]
    split_ifs <;> omega
  by_cases h4 : k.val<262
  · refine ⟨⟨k.val-5,by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [mutable]
    split_ifs <;> omega
  by_cases h5 : k.val<277
  · refine ⟨⟨k.val-6,by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [mutable]
    split_ifs <;> omega
  by_cases h6 : k.val<282
  · refine ⟨⟨k.val-8,by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [mutable]
    split_ifs <;> omega
  · refine ⟨⟨k.val-10,by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [mutable]
    split_ifs <;> omega

variable (printer : WilliamsAlgorithm) (work : Nat) (drv lg : Fin (rowWork work))

def slots : Fin (430+1+1) → Fin (rowTapes printer work) :=
  Fin.addCases (m:=431) (n:=1)
    (Fin.addCases (m:=430) (n:=1)
      (fun i=>PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) (mutable i))
      (fun _ : Fin 1=>workSlot printer work drv))
    (fun _ : Fin 1=>workSlot printer work lg)

theorem slots_mutable (i : Fin 430) : slots printer work drv lg ((i.castAdd 1).castAdd 1) =
    PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) (mutable i) := by
  simp only [slots,Fin.addCases_left]

theorem slots_driver : slots printer work drv lg ((0 : Fin 1).natAdd 430 |>.castAdd 1) =
    workSlot printer work drv := by
  simp only [slots,Fin.addCases_left,Fin.addCases_right]

theorem slots_log : slots printer work drv lg ((0 : Fin 1).natAdd 431) =
    workSlot printer work lg := by
  simp only [slots,Fin.addCases_right]

theorem slots_val (i : Fin (430+1+1)) :
    (slots printer work drv lg i).val =
      if hi : i.val<430 then (mutable ⟨i.val,hi⟩).val
      else if i.val=430 then 440+(P1TopDownPaidPayload.tapes printer+2)+drv.val
      else 440+(P1TopDownPaidPayload.tapes printer+2)+lg.val := by
  refine Fin.addCases (m:=431) (n:=1) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=430) (n:=1) (fun i=>?_) (fun i=>?_) i
    · rw [slots_mutable,headerSlot_val]
      simp only [Fin.val_castAdd,dif_pos i.isLt]
    · have hz : i=0 := Subsingleton.elim i 0
      subst hz
      rw [slots_driver,workSlot_val]
      simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Nat.add_zero,
        dif_neg (Nat.lt_irrefl 430),if_true]
  · have hz : i=0 := Subsingleton.elim i 0
    subst hz
    rw [slots_log,workSlot_val]
    simp only [Fin.val_natAdd,Fin.val_zero,Nat.add_zero,dif_neg (by omega : ¬431<430),
      if_neg (by omega : (431:Nat)≠430)]

theorem slots_injective (hne : drv ≠ lg) : Function.Injective (slots printer work drv lg) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [slots_val,slots_val] at hv
  have hi := i.isLt
  have hj := j.isLt
  have hd : drv.val ≠ lg.val := fun he=>hne (Fin.ext he)
  apply Fin.ext
  unfold mutable at hv
  dsimp only at hv
  split_ifs at hv <;> omega

theorem slots_ne_retained (i : Fin (430+1+1)) (k : Fin 440) (hk : retained k) :
    slots printer work drv lg i ≠
      PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k := by
  intro he
  have hv := congrArg Fin.val he
  rw [slots_val,headerSlot_val] at hv
  have hi := i.isLt
  have hklt := k.isLt
  unfold retained at hk
  unfold mutable at hv
  dsimp only at hv
  split_ifs at hv <;> omega


def output (A : Fin (rowTapes printer work) → List Bool) (U : Nat) :=
  install (slots printer work drv lg) A (PCJ45bee56da9f34d5a_Plan.clearOutput 430 U (U+1))

theorem output_mutable (hne : drv ≠ lg)
    (A : Fin (rowTapes printer work) → List Bool) (U : Nat) (i : Fin 430) :
    output printer work drv lg A U
      (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) (mutable i)) =
      List.replicate U false := by
  rw [←slots_mutable printer work drv lg i,output,
    install_slot _ (slots_injective printer work drv lg hne)]
  simp only [PCJ45bee56da9f34d5a_Plan.clearOutput,PCJ45bee56da9f34d5a_Plan.clearInput,
    Fin.addCases_left]

theorem output_retained (A : Fin (rowTapes printer work) → List Bool) (U : Nat)
    (k : Fin 440) (hk : retained k) :
    output printer work drv lg A U
      (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k) =
      A (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k) :=
  install_other _ _ _ _ (fun i=>slots_ne_retained printer work drv lg i k hk)


variable {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g)

theorem commonHeader_mutable (i : Fin 430) :
    commonHeader a F g layout (mutable i)=[] := by
  classical
  unfold commonHeader CompactNativeInitialize.input
  by_cases h : ∃ j,CompactNativeInitialize.metadataSlots j=mutable i
  · obtain ⟨j,hj⟩ := h
    rw [←hj,install_slot _ CompactNativeInitialize.meta_injective]
    apply CompactMetadata.input_fresh
    by_contra hh
    have hj8 : j.val<8 := by omega
    let k : Fin 8 := ⟨j.val,hj8⟩
    have he : k.castAdd 154=j := Fin.ext rfl
    have hr : ∀ k : Fin 8,retained (CompactNativeInitialize.metadataSlots (k.castAdd 154)) := by
      intro k
      fin_cases k <;> simp [retained,CompactNativeInitialize.metadataSlots]
    apply mutable_not_retained i
    rw [←hj,←he]
    exact hr k
  · rw [install_other _ _ _ _ (by simpa only [not_exists] using h)]
    have h262 : mutable i ≠ 262 := by
      intro he
      apply mutable_not_retained i
      rw [he]
      simp [retained]
    have h277 : mutable i ≠ 277 := by
      intro he
      apply mutable_not_retained i
      rw [he]
      simp [retained]
    simp only [CompactNativeInitialize.base,if_neg h262,if_neg h277]
    split_ifs <;> rfl

theorem headerBank_mutable (reserve : Fin 440 → Nat) (j : Nat) (hn : F.rows ≠ [])
    (U : Nat) (hres : ∀ i,reserve (mutable i)=U) (i : Fin 430) :
    headerBank a F g layout reserve j (mutable i)=List.replicate U false := by
  rw [headerBank,if_neg hn,commonHeader_mutable,hres]
  simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]

/-- The eraser's exact whole Header output is the next padded Header bank;
only the ten retained words have to be transported from preceding stages. -/
theorem output_header (hne : drv ≠ lg)
    (A : Fin (rowTapes printer work) → List Bool) (U : Nat)
    (reserve : Fin 440 → Nat) (j : Nat) (hn : F.rows ≠ [])
    (hres : ∀ i,reserve (mutable i)=U)
    (hkeep : ∀ k,retained k → A (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k)=
      headerBank a F g layout reserve j k) (k : Fin 440) :
    output printer work drv lg A U
      (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k) =
      headerBank a F g layout reserve j k := by
  classical
  by_cases hk : retained k
  · rw [output_retained printer work drv lg A U k hk,hkeep k hk]
  · obtain ⟨i,rfl⟩ := mutable_covers k hk
    rw [output_mutable printer work drv lg hne,
      headerBank_mutable a F g layout reserve j hn U hres]


end
end PCJ45bee56da9f34d5a_HeaderErase
