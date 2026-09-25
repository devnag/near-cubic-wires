import Proof.SourceAssembly.SourceFactorSelWordsHostLay
import Proof.SourceAssembly.SourceRequestConsumer

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
open NearCubicWires.SourceFactorSel.Words
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

section res
variable {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
  {packet : PacketWriter selector a} {rows : RowProducer selector a printer} {V : Nat}

/-- **What the words stage's exit gives on the loader layout** (on the unpadded view `Av`). -/
structure Ctx (L : HostLay mask packet rows V) (gw : Nat) (r : Request) (MB : List Bool) (Rc dR : Nat)
    (H1 : Fin V → Nat) (Av : Fin V → List Bool) : Prop where
  tg : ∀ (x : Fin V) (p : Nat), 6 ≤ p → p < 29 → hostV L.P0 mask.work L.tc L.B L.Pc L.wB p = x.val →
    Av x = ZeroPadding.pad Rc (wd a r MB p) ∧ H1 x = 0
  ub : ∀ x : Fin V, x.val < L.gB ∧ ¬ L.IsTgt x.val ∧ L.Blank gw x.val ∧ ¬ L.NSv x.val →
    Av x = List.replicate Rc false ∧ H1 x = 0
  un : ∀ x : Fin V, L.NSv x.val → Av x = [] ∧ H1 x = 0
  rw1 : Av (L.rewindSlots 1) = List.replicate dR true ∧ H1 (L.rewindSlots 1) = 0
  rw2 : Av (L.rewindSlots 2) = List.replicate dR false ∧ H1 (L.rewindSlots 2) = 0

/-- Unfold the layout predicates and close a linear goal. -/
macro "lz" : tactic => `(tactic| (simp only [HostLay.IsTgt, HostLay.Blank, HostLay.NSv, HostLay.P0, HostLay.B, HostLay.tc] at *; omega))

section facts
variable {L : HostLay mask packet rows V} {gw : Nat} {r : Request} {MB : List Bool} {Rc dR : Nat}
  {H1 : Fin V → Nat} {Av : Fin V → List Bool} (c : Ctx L gw r MB Rc dR H1 Av)
include c

theorem Ctx.ret (i : Fin 4) : Av (L.ret i) = ZeroPadding.pad Rc (wd a r MB (15 + i.val)) ∧ H1 (L.ret i) = 0 :=
  c.tg (L.ret i) (15 + i.val) (by omega) (by omega) (by
    have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB (15 + i.val) (by omega)
    have := L.hret i; have := i.isLt; lz)

theorem Ctx.slotT (j : Fin 13) (h3 : 3 ≤ j.val) (h6 : j.val ≤ 6) :
    Av (L.slot j) = ZeroPadding.pad Rc (wd a r MB (8 + j.val)) ∧ H1 (L.slot j) = 0 :=
  c.tg (L.slot j) (8 + j.val) (by omega) (by omega) (by
    have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB (8 + j.val) (by omega)
    have := L.hslot j; lz)

theorem Ctx.poolT (i : Fin 373) (p : Nat) (h : (i.val = 98 ∧ p = 25) ∨ (224 ≤ i.val ∧ i.val < 227 ∧ p = i.val - 198)) :
    Av (L.poolSlots i) = ZeroPadding.pad Rc (wd a r MB p) ∧ H1 (L.poolSlots i) = 0 :=
  c.tg (L.poolSlots i) p (by omega) (by omega) (by
    have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB p (by omega)
    have hv := L.hpool i
    rw [if_neg (by omega)] at hv
    lz)

theorem Ctx.one (x : Fin V) (p : Nat) (h6 : 6 ≤ p) (h29 : p < 29)
    (hx : hostV L.P0 mask.work L.tc L.B L.Pc L.wB p = x.val) :
    Av x = ZeroPadding.pad Rc (wd a r MB p) ∧ H1 x = 0 := c.tg x p h6 h29 hx

theorem Ctx.maskF (j : Fin (5 + mask.work)) :
    (j.val < 4 → Av (L.maskSlots j) = []) ∧ (4 ≤ j.val → Av (L.maskSlots j) = List.replicate Rc false) ∧
      H1 (L.maskSlots j) = 0 := by
  have hv := L.hmask j
  have hgB := L.hgB
  by_cases h4 : j.val < 4
  · have e := c.un (L.maskSlots j) (by rw [if_neg (by omega)] at hv; lz)
    exact ⟨fun _ => e.1, fun h => absurd h (by omega), e.2⟩
  · have e := c.ub (L.maskSlots j) (by
      have := j.isLt
      have hG := L.hG
      by_cases h44 : j.val = 4
      · rw [if_pos h44] at hv
        lz
      · rw [if_neg h44] at hv
        lz)
    exact ⟨fun h => absurd h h4, fun _ => e.1, e.2⟩

theorem Ctx.slotN (j : Fin 13) (hn : j.val = 1 ∨ j.val = 7 ∨ 9 ≤ j.val) : Av (L.slot j) = [] ∧ H1 (L.slot j) = 0 :=
  c.un (L.slot j) (by have := L.hslot j; have := j.isLt; lz)

theorem Ctx.slotB (j : Fin 13) (hb : j.val = 0 ∨ j.val = 2 ∨ j.val = 8) :
    Av (L.slot j) = List.replicate Rc false ∧ H1 (L.slot j) = 0 :=
  c.ub (L.slot j) (by have := L.hslot j; have := L.hgB; have := L.hG; lz)

theorem Ctx.slotH (j : Fin 13) : H1 (L.slot j) = 0 := by
  by_cases h1 : j.val = 1 ∨ j.val = 7 ∨ 9 ≤ j.val
  · exact (c.slotN j h1).2
  by_cases h2 : j.val = 0 ∨ j.val = 2 ∨ j.val = 8
  · exact (c.slotB j h2).2
  · exact (c.slotT j (by omega) (by omega)).2

theorem Ctx.pkt (j : Fin packet.ordinary.program.tapeCount) :
    (j.val ≠ 0 → Av (L.pslots j) = List.replicate Rc false) ∧ H1 (L.pslots j) = 0 := by
  have hv := L.hpsl j
  have hgB := L.hgB
  have hG := L.hG
  have hd := L.hdesc
  have hd4 := L.hdesc440
  have hj := j.isLt
  by_cases h0 : j.val = 0
  · have hne : j.val ≠ L.outV := fun e => L.hout0 (e ▸ h0)
    rw [if_neg hne, if_pos h0] at hv
    exact ⟨fun h => absurd h0 h, (c.un (L.pslots j) (by lz)).2⟩
  · have e := c.ub (L.pslots j) (by
      by_cases ho : j.val = L.outV
      · rw [if_pos ho] at hv
        lz
      · rw [if_neg ho, if_neg h0] at hv
        lz)
    exact ⟨fun _ => e.1, e.2⟩

theorem Ctx.family (j : Fin (rowTapes printer rows.privateWork + 1)) (hR : j.val < L.R1) :
    Av (L.familySlots j) = List.replicate Rc false ∧ H1 (L.familySlots j) = 0 :=
  c.ub (L.familySlots j) (by
    have hv := L.hfam j
    have := L.hgB; have := L.hG; have := L.hsp; have := L.hdesc
    by_cases hd : j.val = L.descV
    · rw [if_pos hd] at hv
      lz
    · rw [if_neg hd] at hv
      lz)

theorem Ctx.poolB (i : Fin 373) (h98 : i.val ≠ 98) (h224 : i.val ≠ 224) (h225 : i.val ≠ 225) (h226 : i.val ≠ 226) :
    Av (L.poolSlots i) = List.replicate Rc false ∧ H1 (L.poolSlots i) = 0 :=
  c.ub (L.poolSlots i) (by
    have hv := L.hpool i
    have := L.hgB; have := L.hG; have := i.isLt; have := L.hdesc; have := L.hdesc440
    by_cases h34 : i.val = 34
    · rw [if_pos h34] at hv
      lz
    · rw [if_neg h34] at hv
      lz)

theorem Ctx.scrB (x : Fin V) (m : Nat) (hm : m = 398 ∨ m = 404 ∨ m = 407)
    (hx : x.val = L.G + L.R1 + m + mask.work + packet.ordinary.program.tapeCount) :
    Av x = List.replicate Rc false ∧ H1 x = 0 :=
  c.ub x (by have := L.hgB; lz)

end facts

/-- **The `Resident` of `r`, from the exit facts.** -/
theorem resident_of_ctx (L : HostLay mask packet rows V) (gw : Nat) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) (MB : List Bool) (Rc dR : Nat)
    (H1 : Fin V → Nat) (Av : Fin V → List Bool) (c : Ctx L gw r MB Rc dR H1 Av)
    (hMB : SLoad.Setup.metaBits layout.w layout.degree layout.C caps = MB) (hdR : caps.descriptorReserve = dR)
    (hR1 : L.R1 = rowTapes printer rows.privateWork + 1)
    (cs : (r.supportWord a).length ≤ Rc) (cq : 4 * r.q + 3 ≤ Rc)
    (ck : 4 * normalizedLiveCount r.q r.liveScale + 3 ≤ Rc) (cm : 4 * (r.family a).occurrences.length + 3 ≤ Rc)
    (cn : 2 * r.nativeWord.length + 1 ≤ Rc) (cs2 : 2 * (r.supportWord a).length + 1 ≤ Rc)
    (ci : 2 * (r.indexWord a).length + 1 ≤ Rc) (ct : 2 * (r.topWord a).length + 1 ≤ Rc)
    (cl1 : 2 * (r.input a).length + 1 ≤ Rc) (cl2 : 2 * MB.length + 1 ≤ Rc) :
    Nonempty (SourceRequest.Resident mask packet rows L.maskSlots L.pslots L.slot L.ret L.retDrv L.log L.familySlots L.poolSlots
      L.rewindSlots L.s1 L.d1 L.l1 L.s2 L.d2 L.l2 L.lenTape r layout caps H1 Av) := by
  have hq : ∀ (x : Fin V) (p : Nat), 6 ≤ p → p < 29 → hostV L.P0 mask.work L.tc L.B L.Pc L.wB p = x.val →
      Av x = ZeroPadding.pad Rc (wd a r MB p) ∧ H1 x = 0 := c.tg
  have eDrv := c.one L.retDrv 19 (by omega) (by omega) (by
    have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB 19 (by omega); have := L.hretDrv; lz)
  have eS1 := c.one L.s1 20 (by omega) (by omega) (by
    have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB 20 (by omega); have := L.hs1; lz)
  have eD1 := c.one L.d1 21 (by omega) (by omega) (by
    have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB 21 (by omega); have := L.hd1; lz)
  have eS2 := c.one L.s2 22 (by omega) (by omega) (by
    have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB 22 (by omega); have := L.hs2; lz)
  have eD2 := c.one L.d2 23 (by omega) (by omega) (by
    have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB 23 (by omega); have := L.hd2; lz)
  have eLen := c.one L.lenTape 24 (by omega) (by omega) (by
    have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB 24 (by omega); have := L.hlen; lz)
  have eLog := c.scrB L.log 398 (by omega) L.hlog
  have eL1 := c.scrB L.l1 404 (by omega) L.hl1
  have eL2 := c.scrB L.l2 407 (by omega) L.hl2
  have hfamR : ∀ j : Fin (rowTapes printer rows.privateWork + 1), j.val < L.R1 := fun j => by rw [hR1]; exact j.isLt
  refine ⟨{
    cap := Rc
    uK := List.replicate (normalizedLiveCount r.q r.liveScale) true
    um := List.replicate (r.family a).occurrences.length true
    blank := fun _ => Rc
    blankP := fun _ => Rc
    poolReserve := fun _ => Rc
    familyReserve := fun _ => Rc
    capS1 := Rc
    capD1 := Rc
    capL1 := Rc
    capS2 := Rc
    capD2 := Rc
    capL2 := Rc
    capLen := Rc
    w_retDrv := eDrv.1
    w_ret0 := (c.ret 0).1
    w_ret1 := (c.ret 1).1
    w_ret2 := (c.ret 2).1
    len_uK := List.length_replicate ..
    w_ret3 := (c.ret 3).1
    len_um := List.length_replicate ..
    w_native := (c.slotT 3 (by decide) (by decide)).1
    w_support := (c.slotT 4 (by decide) (by decide)).1
    w_index := (c.slotT 5 (by decide) (by decide)).1
    w_top := (c.slotT 6 (by decide) (by decide)).1
    w_pool := ?_
    w_input := eS1.1
    w_inputLen := eD1.1
    w_meta := ?_
    w_metaLen := ?_
    w_len := eLen.1
    b_log := eLog.1
    b_maskLive := fun j h => (c.maskF j).1 h
    b_maskPriv := fun j h => (c.maskF j).2.1 h
    b_slot1 := (c.slotN 1 (by decide)).1
    b_slot2 := (c.slotB 2 (by decide)).1
    b_slot7 := (c.slotN 7 (by decide)).1
    b_slot8 := (c.slotB 8 (by decide)).1
    b_slotTail := fun j h => (c.slotN j (Or.inr (Or.inr h))).1
    b_packet := fun j h => (c.pkt j).1 h
    b_l1 := eL1.1
    b_l2 := eL2.1
    b_family := fun j _ _ => (c.family j (hfamR j)).1
    s_rewind1 := (by rw [hdR]; exact c.rw1.1)
    s_rewind2 := (by rw [hdR]; exact c.rw2.1)
    hH_ret := fun i => (c.ret i).2
    hH_mask := fun j => (c.maskF j).2.2
    hH_log := eLog.2
    hH_retDrv := eDrv.2
    hH_slot := fun j => c.slotH j
    hH_packet := fun j => (c.pkt j).2
    hH_pool := ?_
    hH_family := fun j => (c.family j (hfamR j)).2
    hH_s1 := eS1.2
    hH_d1 := eD1.2
    hH_l1 := eL1.2
    hH_s2 := eS2.2
    hH_d2 := eD2.2
    hH_l2 := eL2.2
    hH_len := eLen.2
    hH_rewind1 := c.rw1.2
    hH_rewind2 := c.rw2.2
    cs := cs
    cq := cq
    ck := (by rw [List.length_replicate]; exact ck)
    cm := (by rw [List.length_replicate]; exact cm)
    cq2 := (by omega)
    cn := cn
    cs2 := cs2
    ci := ci
    ct := ct
    cl1 := cl1
    cl2 := (by rw [hMB]; exact cl2)
  }⟩
  · intro i
    by_cases h98 : i.val = 98
    · rw [(c.poolT i 25 (Or.inl ⟨h98, rfl⟩)).1]
      have e : i = 98 := Fin.ext h98
      rw [e]; rfl
    by_cases h224 : i.val = 224
    · rw [(c.poolT i 26 (Or.inr ⟨by omega, by omega, by omega⟩)).1]
      have e : i = 224 := Fin.ext h224
      rw [e]; rfl
    by_cases h225 : i.val = 225
    · rw [(c.poolT i 27 (Or.inr ⟨by omega, by omega, by omega⟩)).1]
      have e : i = 225 := Fin.ext h225
      rw [e, cold_input_225 selector a r]
      rfl
    by_cases h226 : i.val = 226
    · rw [(c.poolT i 28 (Or.inr ⟨by omega, by omega, by omega⟩)).1]
      have e : i = 226 := Fin.ext h226
      rw [e, cold_input_226 a r]
      rfl
    · rw [(c.poolB i h98 h224 h225 h226).1, Item4.cold_input_nil _ i h98 h224 h225 h226]
      exact (Item4.pad_nil_blank Rc).symm
  · rw [eS2.1, ← hMB]; rfl
  · rw [eD2.1, ← hMB]; rfl
  · intro i
    by_cases h98 : i.val = 98
    · exact (c.poolT i 25 (Or.inl ⟨h98, rfl⟩)).2
    by_cases h224 : 224 ≤ i.val ∧ i.val < 227
    · exact (c.poolT i (i.val - 198) (Or.inr ⟨h224.1, h224.2, rfl⟩)).2
    · exact (c.poolB i h98 (by omega) (by omega) (by omega)).2

end res

end
end NearCubicWires.SourceFactorSel.WordsHost

