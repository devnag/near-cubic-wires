import Proof.Packets.PacketsMetaContract
import Proof.SourceAssembly.SourceCyclePad
import Proof.SourceAssembly.SourcePrologue
import Proof.SourceAssembly.SourceRequestResidentProducer

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-- **`Resident` is carried by any bank that agrees on every tape it reads.** -/
def resident_transport {U : Nat} {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    {packet : PacketWriter selector a} {rows : RowProducer selector a printer}
    {maskSlots : Fin (5 + mask.work) → Fin U}
    {pslots : Fin packet.ordinary.program.tapeCount → Fin U}
    {slot : Fin 13 → Fin U} {ret : Fin 4 → Fin U} {retDrv log : Fin U}
    {familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U}
    {poolSlots : Fin 373 → Fin U} {rewindSlots : Fin 3 → Fin U}
    {s1 d1 l1 s2 d2 l2 lenTape : Fin U}
    {r : Request} {layout : Packets.Layout a (r.family a) (geometryOf selector a r)} {caps : RowCaps}
    {H : Fin U → Nat} {A : Fin U → List Bool}
    (res : SourceRequest.Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
      rewindSlots s1 d1 l1 s2 d2 l2 lenTape r layout caps H A)
    (H' : Fin U → Nat) (A' : Fin U → List Bool)
    (hS : ∀ j, A' (slot j) = A (slot j)) (hM : ∀ i, A' (maskSlots i) = A (maskSlots i))
    (hP : ∀ j, A' (pslots j) = A (pslots j)) (hPo : ∀ i, A' (poolSlots i) = A (poolSlots i))
    (hF : ∀ i, A' (familySlots i) = A (familySlots i)) (hRw : ∀ i, A' (rewindSlots i) = A (rewindSlots i))
    (hRt : ∀ i, A' (ret i) = A (ret i)) (hRD : A' retDrv = A retDrv) (hLg : A' log = A log)
    (h1 : A' s1 = A s1) (h2 : A' d1 = A d1) (h3 : A' l1 = A l1) (h4 : A' s2 = A s2) (h5 : A' d2 = A d2)
    (h6 : A' l2 = A l2) (h7 : A' lenTape = A lenTape)
    (gS : ∀ j, H' (slot j) = H (slot j)) (gM : ∀ i, H' (maskSlots i) = H (maskSlots i))
    (gP : ∀ j, H' (pslots j) = H (pslots j)) (gPo : ∀ i, H' (poolSlots i) = H (poolSlots i))
    (gF : ∀ i, H' (familySlots i) = H (familySlots i)) (gRw : ∀ i, H' (rewindSlots i) = H (rewindSlots i))
    (gRt : ∀ i, H' (ret i) = H (ret i)) (gRD : H' retDrv = H retDrv) (gLg : H' log = H log)
    (g1 : H' s1 = H s1) (g2 : H' d1 = H d1) (g3 : H' l1 = H l1) (g4 : H' s2 = H s2) (g5 : H' d2 = H d2)
    (g6 : H' l2 = H l2) (g7 : H' lenTape = H lenTape) :
    SourceRequest.Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
      rewindSlots s1 d1 l1 s2 d2 l2 lenTape r layout caps H' A' :=
  { cap := res.cap,
    uK := res.uK,
    um := res.um,
    blank := res.blank,
    blankP := res.blankP,
    poolReserve := res.poolReserve,
    familyReserve := res.familyReserve,
    capS1 := res.capS1,
    capD1 := res.capD1,
    capL1 := res.capL1,
    capS2 := res.capS2,
    capD2 := res.capD2,
    capL2 := res.capL2,
    capLen := res.capLen,
    w_retDrv := hRD.trans res.w_retDrv,
    w_ret0 := (hRt 0).trans res.w_ret0,
    w_ret1 := (hRt 1).trans res.w_ret1,
    w_ret2 := (hRt 2).trans res.w_ret2,
    len_uK := res.len_uK,
    w_ret3 := (hRt 3).trans res.w_ret3,
    len_um := res.len_um,
    w_native := (hS 3).trans res.w_native,
    w_support := (hS 4).trans res.w_support,
    w_index := (hS 5).trans res.w_index,
    w_top := (hS 6).trans res.w_top,
    w_pool := fun i => (hPo i).trans (res.w_pool i),
    w_input := h1.trans res.w_input,
    w_inputLen := h2.trans res.w_inputLen,
    w_meta := h4.trans res.w_meta,
    w_metaLen := h5.trans res.w_metaLen,
    w_len := h7.trans res.w_len,
    b_log := hLg.trans res.b_log,
    b_maskLive := fun j hj => (hM j).trans (res.b_maskLive j hj),
    b_maskPriv := fun j hj => (hM j).trans (res.b_maskPriv j hj),
    b_slot1 := (hS 1).trans res.b_slot1,
    b_slot2 := (hS 2).trans res.b_slot2,
    b_slot7 := (hS 7).trans res.b_slot7,
    b_slot8 := (hS 8).trans res.b_slot8,
    b_slotTail := fun j hj => (hS j).trans (res.b_slotTail j hj),
    b_packet := fun j hj => (hP j).trans (res.b_packet j hj),
    b_l1 := h3.trans res.b_l1,
    b_l2 := h6.trans res.b_l2,
    b_family := fun i h0 h262 => (hF i).trans (res.b_family i h0 h262),
    s_rewind1 := (hRw 1).trans res.s_rewind1,
    s_rewind2 := (hRw 2).trans res.s_rewind2,
    hH_ret := fun i => (gRt i).trans (res.hH_ret i),
    hH_mask := fun j => (gM j).trans (res.hH_mask j),
    hH_log := gLg.trans res.hH_log,
    hH_retDrv := gRD.trans res.hH_retDrv,
    hH_slot := fun j => (gS j).trans (res.hH_slot j),
    hH_packet := fun j => (gP j).trans (res.hH_packet j),
    hH_pool := fun i => (gPo i).trans (res.hH_pool i),
    hH_family := fun i => (gF i).trans (res.hH_family i),
    hH_s1 := g1.trans res.hH_s1,
    hH_d1 := g2.trans res.hH_d1,
    hH_l1 := g3.trans res.hH_l1,
    hH_s2 := g4.trans res.hH_s2,
    hH_d2 := g5.trans res.hH_d2,
    hH_l2 := g6.trans res.hH_l2,
    hH_len := g7.trans res.hH_len,
    hH_rewind1 := (gRw 1).trans res.hH_rewind1,
    hH_rewind2 := (gRw 2).trans res.hH_rewind2,
    cs := res.cs,
    cq := res.cq,
    ck := res.ck,
    cm := res.cm,
    cq2 := res.cq2,
    cn := res.cn,
    cs2 := res.cs2,
    ci := res.ci,
    ct := res.ct,
    cl1 := res.cl1,
    cl2 := res.cl2 }

/-! ## 2. The monomial cursor -/

/-- The in-place increment, padded. -/
theorem incr_step (c R : Nat) :
    Step MatrixBucketDimensions.Increment.machine (2*c+5) (fun _ => 0)
      (fun _ => ZeroPadding.pad R (UnaryTemplate.tape c)) (fun _ => 0)
      (fun _ => ZeroPadding.pad R (UnaryTemplate.tape (c+1))) :=
  (Step.of_ready (MatrixBucketDimensions.Increment.increment_run c)).pad (fun _ => R)

/-- The cursor machine on its three local tapes `[curT, cur, scratch]`: increment the template, then read it out. -/
def cursorMachine :=
  Composition.machine (RecoveryFocus.machine (fun _ : Fin 1 => (0 : Fin 3)) MatrixBucketDimensions.Increment.machine)
    (UWalkUnary.machine false false)

def cursorCost (m : Nat) : Nat := (2*m+5) + 1 + (2*(m+1)+6)

theorem cursor_local (m R : Nat) (hR : m + 3 ≤ R) :
    Step cursorMachine (cursorCost m) (fun _ => 0)
      ![ZeroPadding.pad R (UnaryTemplate.tape m), List.replicate R false, List.replicate R false]
      (fun _ => 0)
      ![ZeroPadding.pad R (UnaryTemplate.tape (m+1)), ZeroPadding.pad R (List.replicate (m+1) true),
        List.replicate R false] := by
  have s1 := Prologue.dockKeep (incr_step m R) (fun _ : Fin 1 => (0 : Fin 3))
    (fun a b _ => Subsingleton.elim a b) (fun _ => 0)
    ![ZeroPadding.pad R (UnaryTemplate.tape m), List.replicate R false, List.replicate R false]
    (fun _ => rfl) (fun _ => rfl)
  have s2 := RowConst.stepUW false false (m+1) R R R
  have e1 : install (fun _ : Fin 1 => (0 : Fin 3))
      ![ZeroPadding.pad R (UnaryTemplate.tape m), List.replicate R false, List.replicate R false]
      (fun _ => ZeroPadding.pad R (UnaryTemplate.tape (m+1))) =
      ![ZeroPadding.pad R (UnaryTemplate.tape (m+1)), ZeroPadding.pad R [], ZeroPadding.pad R []] := by
    funext i
    fin_cases i
    · exact install_slot _ (fun a b _ => Subsingleton.elim a b) _ _ 0
    · rw [install_other _ _ _ _ (by intro j; exact Fin.ne_of_val_ne (by simp))]
      exact (Finish.blank_is_padded R).symm
    · rw [install_other _ _ _ _ (by intro j; exact Fin.ne_of_val_ne (by simp))]
      exact (Finish.blank_is_padded R).symm
  rw [e1] at s1
  have e2 : ZeroPadding.pad R (List.replicate (m + 1 + 2) false) = List.replicate R false := by
    simp only [ZeroPadding.pad, List.length_replicate, List.replicate_append_replicate]
    congr 1
    omega
  have hs := s1.seq s2
  rw [RowConst.out_ff, e2] at hs
  exact hs

/-- **The cursor on the layout**, docked on `[curT, cur, scr]`: every other tape and every head is kept. -/
theorem cursor_run {U : Nat} (sl : Fin 3 → Fin U) (hsl : Function.Injective sl) (m R : Nat) (hR : m + 3 ≤ R)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad R (UnaryTemplate.tape m))
    (h1 : A (sl 1) = List.replicate R false) (h2 : A (sl 2) = List.replicate R false) :
    Step (RecoveryFocus.machine sl cursorMachine) (cursorCost m) H A H
      (install sl A ![ZeroPadding.pad R (UnaryTemplate.tape (m+1)), ZeroPadding.pad R (List.replicate (m+1) true),
        List.replicate R false]) :=
  Prologue.dockKeep (cursor_local m R hR) sl hsl H A hH (by
    intro j; fin_cases j
    · exact h0
    · exact h1
    · exact h2)

/-! ## 3. One metadata stage, docked and padded -/

theorem stage_run {a : DecompositionAlgorithm} {v : Request → Nat}
    (st : PacketsGlue.RequestMeta.UnaryStage a v) (r : Request)
    {U : Nat} (sl : Fin (2 + st.extra) → Fin U) (hsl : Function.Injective sl) (c0 R : Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl ⟨0, by omega⟩) = ZeroPadding.pad c0 (RepairOrdinary.frame (Request.input a r)))
    (hb : ∀ j : Fin (2 + st.extra), j.val ≠ 0 → A (sl j) = List.replicate R false) :
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step (RecoveryFocus.machine sl st.machine) (st.cost r) H A H' A' ∧
      A' (sl ⟨0, by omega⟩) = A (sl ⟨0, by omega⟩) ∧ H' (sl ⟨0, by omega⟩) = 0 ∧
      A' (sl ⟨1, by omega⟩) = ZeroPadding.pad R (List.replicate (v r) true) ∧ H' (sl ⟨1, by omega⟩) = 0 ∧
      (∀ x, (∀ j, sl j ≠ x) → A' x = A x ∧ H' x = H x) := by
  obtain ⟨Hs, As, hst, a0, h0', a1, h1'⟩ := st.run r
  let cap : Fin (2 + st.extra) → Nat := fun j => if j.val = 0 then c0 else R
  have hp := hst.pad cap
  have hin : (fun j => ZeroPadding.pad (cap j)
      (PacketFamilyParent.inBank (2 + st.extra) (Request.input a r) j)) = fun j => A (sl j) := by
    funext j
    by_cases hj : j.val = 0
    · have e : j = ⟨0, by omega⟩ := Fin.ext hj
      rw [e]
      simp [cap, PacketFamilyParent.inBank]
      exact h0.symm
    · have hj' : j ≠ 0 := fun h => hj (by rw [h]; rfl)
      simp [cap, PacketFamilyParent.inBank, hj', hb j hj, Finish.blank_is_padded]
  rw [hin] at hp
  have hd := hp.dock sl hsl H A (fun j => (hH j)) (fun _ => rfl)
  refine ⟨_, _, hd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [install_slot sl hsl, a0]
    simp [cap]
    exact h0.symm
  · rw [dockH_slot sl hsl]; exact h0'
  · rw [install_slot sl hsl, a1]
    simp [cap]
  · rw [dockH_slot sl hsl]; exact h1'
  · intro x hx
    exact ⟨install_other sl _ _ x hx, dockH_other sl _ _ x hx⟩

end
end NearCubicWires.SourceConstruction.Rest
end
