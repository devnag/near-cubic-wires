import Proof.Rows.RowsRowLevelHeader

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsRowLevel
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

variable {q Lq : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q Lq)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g) (j : Fin F.rows.attach.length)

/-! ## 1. Row-level facts about the Header stage of row `j` -/

theorem rawBefore_succ :
    PCJ38fbfed565f64139_Family.rawBefore a F g j.val++
      (Packets.packets a F g (PCJ38fbfed565f64139_Family.rowAt F j).val).flatMap
        P1CompactNativeFamily.rawWord=
      PCJ38fbfed565f64139_Family.rawBefore a F g (j.val+1) := by
  have hj : j.val<F.rows.length := by simpa only [List.length_attach] using j.isLt
  have hr : (PCJ38fbfed565f64139_Family.rowAt F j).val=F.rows[j.val] := by
    simp only [PCJ38fbfed565f64139_Family.rowAt,List.getElem_attach]
  rw [hr]
  unfold PCJ38fbfed565f64139_Family.rawBefore
  rw [List.take_add_one,List.getElem?_eq_getElem hj,List.flatMap_append]
  simp only [Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

/-- The row's Header stage, as its accepted run states it. -/
abbrev hdrTapes := PCJcc051fd4c1bd4540_Header.finalTapes a F g layout
  (PCJ38fbfed565f64139_Family.rowAt F j).val [] (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
  (PCJ38fbfed565f64139_Family.rawAfter a F g j.val)
abbrev hdrHeads := PCJcc051fd4c1bd4540_Header.finalHeads a F g layout
  (PCJ38fbfed565f64139_Family.rowAt F j).val [] (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
  (PCJ38fbfed565f64139_Family.rawAfter a F g j.val)
abbrev hdrBudget := PCJcc051fd4c1bd4540_Header.budget a F g layout (PCJ38fbfed565f64139_Family.rowAt F j).val

/-- **Retained words** (C4's `hkeep`): each of the ten retained ports, padded at its reserve, is
already the next row's Header bank word. -/
theorem retained_word (reserve : Fin 440 → Nat) (k : Fin 440)
    (hk : PCJ45bee56da9f34d5a_HeaderErase.retained k) :
    ZeroPadding.pad (reserve k) (hdrTapes a F g layout j k)=
      PCJ45bee56da9f34d5a_RowState.headerBank a F g layout reserve (j.val+1) k := by
  rw [PCJ45bee56da9f34d5a_RowState.headerBank_successor,
    PCJ45bee56da9f34d5a_RowState.headerBank_at a F g layout reserve j]
  letI := Packets.radix a F g layout
  congr 1
  exact cold_retained_tapes (Packets.pool a F g) ((Packets.live F).card+1) layout.w
    (Packets.packets a F g (PCJ38fbfed565f64139_Family.rowAt F j).val) []
    (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
    (PCJ38fbfed565f64139_Family.rawAfter a F g j.val) k hk

/-- **Retained heads**: already the next row's ambient heads. -/
theorem retained_head (k : Fin 440) (hk : PCJ45bee56da9f34d5a_HeaderErase.retained k) :
    hdrHeads a F g layout j k=
      CompactColdFamily.ambientH [] (PCJ38fbfed565f64139_Family.rawBefore a F g (j.val+1)) k := by
  letI := Packets.radix a F g layout
  rw [←rawBefore_succ a F g j]
  exact cold_retained_heads (Packets.pool a F g) ((Packets.live F).card+1) layout.w
    (Packets.packets a F g (PCJ38fbfed565f64139_Family.rowAt F j).val) []
    (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
    (PCJ38fbfed565f64139_Family.rawAfter a F g j.val) k hk

/-- Every mutable Header port starts the Header stage empty with its head at `0`. -/
theorem mutable_ambient_head (pre : List Bool) (i : Fin 430) :
    CompactColdFamily.ambientH [] pre (PCJ45bee56da9f34d5a_HeaderErase.mutable i)=0 := by
  have hn := PCJ45bee56da9f34d5a_HeaderErase.mutable_not_retained i
  have h262 : PCJ45bee56da9f34d5a_HeaderErase.mutable i≠262 := by
    intro he
    rw [he] at hn
    exact hn (by unfold PCJ45bee56da9f34d5a_HeaderErase.retained; decide)
  have h277 : PCJ45bee56da9f34d5a_HeaderErase.mutable i≠277 := by
    intro he
    rw [he] at hn
    exact hn (by unfold PCJ45bee56da9f34d5a_HeaderErase.retained; decide)
  simp only [CompactColdFamily.ambientH,CompactNativeInitialize.heads,if_neg h262,if_neg h277]
  split_ifs <;> rfl

/-- The accepted Header run of row `j`. -/
theorem hdr_run (facts : ∀ r∈F.rows,Packets.PacketFacts a F g r) :
    Step PCJcc051fd4c1bd4540_Header.machine (hdrBudget a F g layout j)
      (CompactColdFamily.ambientH [] (PCJ38fbfed565f64139_Family.rawBefore a F g j.val))
      (PCJcc051fd4c1bd4540_Header.input a F g layout (PCJ38fbfed565f64139_Family.rowAt F j).val []
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val) (PCJ38fbfed565f64139_Family.rawAfter a F g j.val))
      (hdrHeads a F g layout j) (hdrTapes a F g layout j) :=
  (PCJcc051fd4c1bd4540_Header.run a F g layout (PCJ38fbfed565f64139_Family.rowAt F j).val
    (PCJ38fbfed565f64139_Family.rowAt F j).property
    (facts _ (PCJ38fbfed565f64139_Family.rowAt F j).property) []
    (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
    (PCJ38fbfed565f64139_Family.rawAfter a F g j.val)).1

/-- **Dirty head bound**: a mutable Header head moves at most `Header.budget` cells. -/
theorem mutable_head_le (facts : ∀ r∈F.rows,Packets.PacketFacts a F g r) (i : Fin 430) :
    hdrHeads a F g layout j (PCJ45bee56da9f34d5a_HeaderErase.mutable i) ≤ hdrBudget a F g layout j := by
  have h := step_head_le (hdr_run a F g layout j facts) (PCJ45bee56da9f34d5a_HeaderErase.mutable i)
  rw [mutable_ambient_head,Nat.zero_add] at h
  exact h

/-- **Dirty length bound**: a mutable Header tape grows to at most `Header.budget+1` cells. -/
theorem mutable_length_le (facts : ∀ r∈F.rows,Packets.PacketFacts a F g r) (i : Fin 430) :
    (hdrTapes a F g layout j (PCJ45bee56da9f34d5a_HeaderErase.mutable i)).length ≤
      hdrBudget a F g layout j+1 := by
  apply LocalSupport.step_fits (hdr_run a F g layout j facts) (PCJ45bee56da9f34d5a_HeaderErase.mutable i)
  · rw [←PCJ45bee56da9f34d5a_RowState.commonHeader_at a F g layout j,
      PCJ45bee56da9f34d5a_HeaderErase.commonHeader_mutable]
    simp
  · rw [mutable_ambient_head]
    omega

/-! ## 2. The C4 step -/

/-- Membership in the eraser's slot map: a mutable Header port, the driver or the log. -/
theorem eraser_slot_cases (printer : WilliamsAlgorithm) (work : Nat) (drvH lgH : Fin (rowWork work))
    (m : Fin (430+1+1)) :
    (∃ i,PCJ45bee56da9f34d5a_HeaderErase.slots printer work drvH lgH m=
        PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) (PCJ45bee56da9f34d5a_HeaderErase.mutable i) ∧
        m=(i.castAdd 1).castAdd 1) ∨
    (PCJ45bee56da9f34d5a_HeaderErase.slots printer work drvH lgH m=
        PCJ45bee56da9f34d5a_RowState.workSlot printer work drvH ∧ m=((0 : Fin 1).natAdd 430).castAdd 1) ∨
    (PCJ45bee56da9f34d5a_HeaderErase.slots printer work drvH lgH m=
        PCJ45bee56da9f34d5a_RowState.workSlot printer work lgH ∧ m=(0 : Fin 1).natAdd 431) := by
  refine Fin.addCases (m:=431) (n:=1) (fun m=>?_) (fun e=>?_) m
  · refine Fin.addCases (m:=430) (n:=1) (fun i=>?_) (fun e=>?_) m
    · exact Or.inl ⟨i,PCJ45bee56da9f34d5a_HeaderErase.slots_mutable printer work drvH lgH i,rfl⟩
    · obtain rfl : e=0 := Subsingleton.elim e 0
      exact Or.inr (Or.inl ⟨PCJ45bee56da9f34d5a_HeaderErase.slots_driver printer work drvH lgH,rfl⟩)
  · obtain rfl : e=0 := Subsingleton.elim e 0
    exact Or.inr (Or.inr ⟨PCJ45bee56da9f34d5a_HeaderErase.slots_log printer work drvH lgH,rfl⟩)

/-- **C4, the Header restore step.** From any row bank whose Header block holds the row's Header
stage output (padded at `reserve`, mutable reserve `U`), with every mutable Header head `≤ U`
and every retained head where the Header stage left it, and a resident `U` driver/log pair on
two work ports: the fixed `HeaderRewind.headerClear` machine ends with the Header block equal to
`headerBank (j+1)`, Header heads the next row's ambient heads, and every other port and head
unchanged. -/
theorem header_restore (printer : WilliamsAlgorithm) (work : Nat)
    (drvH lgH : Fin (rowWork work)) (hne : drvH≠lgH)
    (facts : ∀ r∈F.rows,Packets.PacketFacts a F g r)
    (reserve : Fin 440 → Nat) (U : Nat)
    (hres : ∀ i,reserve (PCJ45bee56da9f34d5a_HeaderErase.mutable i)=U)
    (hU : hdrBudget a F g layout j+1 ≤ U)
    (H : Fin (rowTapes printer work) → Nat) (A : Fin (rowTapes printer work) → List Bool)
    (hA : ∀ k,A (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k)=
      ZeroPadding.pad (reserve k) (hdrTapes a F g layout j k))
    (hmut : ∀ i,H (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work)
      (PCJ45bee56da9f34d5a_HeaderErase.mutable i)) ≤ U)
    (hret : ∀ k,PCJ45bee56da9f34d5a_HeaderErase.retained k →
      H (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k)=hdrHeads a F g layout j k)
    (hd : H (PCJ45bee56da9f34d5a_RowState.workSlot printer work drvH)=0)
    (hl : H (PCJ45bee56da9f34d5a_RowState.workSlot printer work lgH)=0)
    (hdriver : A (PCJ45bee56da9f34d5a_RowState.workSlot printer work drvH)=List.replicate U true)
    (hlog : A (PCJ45bee56da9f34d5a_RowState.workSlot printer work lgH)=List.replicate (U+1) false) :
    Step (PCJ45bee56da9f34d5a_HeaderRewind.headerClear printer work drvH lgH) (4*U+9) H A
      (dockH (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work)) H
        (CompactColdFamily.ambientH [] (PCJ38fbfed565f64139_Family.rawBefore a F g (j.val+1))))
      (install (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work)) A
        (PCJ45bee56da9f34d5a_RowState.headerBank a F g layout reserve (j.val+1))) := by
  classical
  have hlen : ∀ i,(A (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work)
      (PCJ45bee56da9f34d5a_HeaderErase.mutable i))).length ≤ U := by
    intro i
    rw [hA,hres]
    have hb := mutable_length_le a F g layout j facts i
    simp only [ZeroPadding.pad,List.length_append,List.length_replicate]
    omega
  have hinjH := PCJ38fbfed565f64139_Ready.header_injective printer (rowWork work)
  have hinjE := PCJ45bee56da9f34d5a_HeaderErase.slots_injective printer work drvH lgH hne
  have hn : F.rows≠[] := by
    intro he
    have hj : j.val<F.rows.length := by simpa only [List.length_attach] using j.isLt
    have h0 : F.rows.length=0 := congrArg List.length he
    omega
  have run := PCJ45bee56da9f34d5a_HeaderRewind.header_run printer work drvH lgH hne U H A hmut hlen
    hd hl hdriver hlog
  refine run.congr ?_ ?_
  · funext x
    by_cases hx : ∃ k,PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k=x
    · obtain ⟨k,rfl⟩ := hx
      rw [dockH_slot _ hinjH]
      by_cases hk : PCJ45bee56da9f34d5a_HeaderErase.retained k
      · rw [dockH_other _ _ _ _ (fun m=>PCJ45bee56da9f34d5a_HeaderErase.slots_ne_retained printer work
          drvH lgH m k hk),hret k hk,retained_head a F g layout j k hk]
      · obtain ⟨i,rfl⟩ := PCJ45bee56da9f34d5a_HeaderErase.mutable_covers k hk
        rw [←PCJ45bee56da9f34d5a_HeaderErase.slots_mutable printer work drvH lgH i,dockH_slot _ hinjE,
          mutable_ambient_head]
    · rw [dockH_other _ _ _ _ (fun k he=>hx ⟨k,he⟩)]
      by_cases hs : ∃ m,PCJ45bee56da9f34d5a_HeaderErase.slots printer work drvH lgH m=x
      · obtain ⟨m,rfl⟩ := hs
        rw [dockH_slot _ hinjE]
        rcases eraser_slot_cases printer work drvH lgH m with ⟨i,he,_⟩|⟨he,_⟩|⟨he,_⟩
        · exact absurd ⟨_,he.symm⟩ hx
        · rw [he,hd]
        · rw [he,hl]
      · rw [dockH_other _ _ _ _ (fun m he=>hs ⟨m,he⟩)]
  · funext x
    by_cases hx : ∃ k,PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k=x
    · obtain ⟨k,rfl⟩ := hx
      rw [install_slot _ hinjH]
      exact PCJ45bee56da9f34d5a_HeaderErase.output_header printer work drvH lgH a F g layout hne A U reserve
        (j.val+1) hn hres (fun k hk=>(hA k).trans (retained_word a F g layout j reserve k hk)) k
    · rw [install_other _ _ _ _ (fun k he=>hx ⟨k,he⟩)]
      unfold PCJ45bee56da9f34d5a_HeaderErase.output
      by_cases hs : ∃ m,PCJ45bee56da9f34d5a_HeaderErase.slots printer work drvH lgH m=x
      · obtain ⟨m,rfl⟩ := hs
        rw [install_slot _ hinjE]
        rcases eraser_slot_cases printer work drvH lgH m with ⟨i,he,_⟩|⟨he,hm⟩|⟨he,hm⟩
        · exact absurd ⟨_,he.symm⟩ hx
        · rw [he,hdriver,hm]
          simp only [PCJ45bee56da9f34d5a_Plan.clearOutput,PCJ45bee56da9f34d5a_Plan.clearInput,
            Fin.addCases_left,Fin.addCases_right]
        · rw [he,hlog,hm]
          simp only [PCJ45bee56da9f34d5a_Plan.clearOutput,PCJ45bee56da9f34d5a_Plan.clearInput,
            Fin.addCases_right]
      · rw [install_other _ _ _ _ (fun m he=>hs ⟨m,he⟩)]


end
end RowsRowLevel
