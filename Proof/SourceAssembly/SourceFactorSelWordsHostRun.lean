import Proof.SourceAssembly.SourceFactorSelWordsHostRes

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

theorem pad_long (c : Nat) (l : List Bool) (h : c ≤ l.length) : ZeroPadding.pad c l = l := by
  simp [ZeroPadding.pad, Nat.sub_eq_zero_of_le h]

theorem prod_low (p : Nat) (hp : p ≤ 10) : prod p = 0 := by
  interval_cases p <;> rfl

theorem prod_pos (p : Nat) (h1 : 11 ≤ p) (h2 : p < 30) : 1 ≤ prod p := by
  interval_cases p <;> decide

section host
variable {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
  {packet : PacketWriter selector a} {rows : RowProducer selector a printer} {V : Nat}

/-- Every shared host value stays below the high residents' end. -/
theorem HostLay.hostV_lt (L : HostLay mask packet rows V) (N : Nat) (hN : L.wB + (N - 29) ≤ L.B + 43 + L.Pc)
    (hVB : L.B + 48 + L.Pc ≤ V) : ∀ p, 6 ≤ p → p < N → hostV L.P0 mask.work L.tc L.B L.Pc L.wB p < V := by
  intro p h6 hp
  have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB p h6
  have := L.hgB; have := L.hwB
  simp only [HostLay.B, HostLay.P0, HostLay.tc] at *
  omega

/-- **The words stage on the host.** -/
def wordsHostM (L : HostLay mask packet rows V) {k : Nat} (SB : Item4.StartBank a k) (src : Fin 6 → Fin V)
    (hV : ∀ p, 6 ≤ p → p < nW mask.work (Cold.tapes a) k → hostV L.P0 mask.work L.tc L.B L.Pc L.wB p < V) :=
  RecoveryFocus.machine (L.dock src (nW mask.work (Cold.tapes a) k) hV) (Words.wordsLoc mask SB)

/-- **The words stage's host run** at one request. -/
theorem words_host_req (L : HostLay mask packet rows V) {k : Nat} (SB : Item4.StartBank a k)
    (hIn : ∀ j, (SB.inPort j).val = j.val) (src : Fin 6 → Fin V) (hsrc : Function.Injective src)
    (hsr : ∀ i, L.gB ≤ (src i).val ∧ (src i).val < L.wB)
    (hN : L.wB + (nW mask.work (Cold.tapes a) k - 29) ≤ L.B + 43 + L.Pc) (hVB : L.B + 48 + L.Pc ≤ V)
    (hR1 : L.R1 = rowTapes printer rows.privateWork + 1)
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) (MB : List Bool)
    (Rc dR : Nat) (hMB : SLoad.Setup.metaBits layout.w layout.degree layout.C caps = MB)
    (hdR : caps.descriptorReserve = dR)
    (Rpad : Fin V → Nat) (hRpad : ∀ x : Fin V, L.G ≤ x.val → x.val < L.P0 + 408 + mask.work + L.tc → Rpad x = Rc)
    (H : Fin V → Nat) (A : Fin V → List Bool)
    (hA_src : ∀ i : Fin 6, A (src i) = ZeroPadding.pad Rc (wd a r MB i.val) ∧ H (src i) = 0)
    (hA_res : ∀ x : Fin V, L.B + 43 + L.Pc ≤ x.val → x.val < L.B + 48 + L.Pc →
      A x = ZeroPadding.pad Rc (wd a r MB (x.val - (L.B + 43 + L.Pc) + 6)) ∧ H x = 0)
    (hA_bl : ∀ x : Fin V, L.Blank (gwW mask.work (Cold.tapes a) k) x.val → A x = List.replicate Rc false ∧ H x = 0)
    (hA_rw : A (L.rewindSlots 1) = List.replicate dR true ∧ H (L.rewindSlots 1) = 0 ∧
      A (L.rewindSlots 2) = List.replicate dR false ∧ H (L.rewindSlots 2) = 0)
    (hlenfl : ∀ x, Rpad x ≤ (A x).length)
    (hNw : 2 * r.nativeWord.length + 1 ≤ Rc) (hS : 2 * (r.supportWord a).length + 1 ≤ Rc)
    (hT : 2 * (r.topWord a).length + 1 ≤ Rc) (cq : 4 * r.q + 3 ≤ Rc)
    (ck : 4 * normalizedLiveCount r.q r.liveScale + 3 ≤ Rc) (cm : 4 * (r.family a).occurrences.length + 3 ≤ Rc)
    (ci : 2 * (r.indexWord a).length + 1 ≤ Rc) (hneed : SB.need r ≤ Rc)
    (cl1 : 2 * (r.input a).length + 1 ≤ Rc) (cl2 : 2 * MB.length + 1 ≤ Rc) :
    ∃ (H1 : Fin V → Nat) (A1 : Fin V → List Bool) (Av : Fin V → List Bool),
      Step (wordsHostM L SB src (L.hostV_lt _ hN hVB)) (Words.wordsCost mask SB r MB) H A H1 A1 ∧
      (∀ x, A1 x = ZeroPadding.pad (Rpad x) (Av x)) ∧
      Nonempty (SourceRequest.Resident mask packet rows L.maskSlots L.pslots L.slot L.ret L.retDrv L.log L.familySlots
        L.poolSlots L.rewindSlots L.s1 L.d1 L.l1 L.s2 L.d2 L.l2 L.lenTape r layout caps H1 Av) ∧
      (∀ x, (∀ p : Fin (nW mask.work (Cold.tapes a) k), 11 ≤ p.val →
        L.dock src (nW mask.work (Cold.tapes a) k) (L.hostV_lt _ hN hVB) p ≠ x) → A1 x = A x ∧ H1 x = H x) := by
  classical
  have hV := L.hostV_lt _ hN hVB
  set N := nW mask.work (Cold.tapes a) k with hNdef
  set D := L.dock src N hV with hD
  have hgB := L.hgB
  have hwB := L.hwB
  have hgw : N - 29 = gwW mask.work (Cold.tapes a) k := by rw [hNdef, nW_eq]; omega
  have hN29 : 29 ≤ N := by rw [hNdef]; unfold nW; omega
  have hinj : Function.Injective D :=
    wsl_inj src _ _ _ _ _ _ hV rfl (by simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega) hN hsrc L.gB
      (by simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega) hsr
  -- the dock's entry bank
  have hent : ∀ p : Fin N, A (D p) = Gn a r MB Rc 0 p.val ∧ H (D p) = 0 := by
    intro p
    by_cases h6 : p.val < 6
    · have e : D p = src ⟨p.val, h6⟩ := wsl_src src _ _ _ _ _ _ hV p h6
      rw [e, Gn_old a r MB Rc 0 p.val (by rw [prod_low p.val (by omega)])]
      exact hA_src ⟨p.val, h6⟩
    have hvD : (D p).val = hostV L.P0 mask.work L.tc L.B L.Pc L.wB p.val := wsl_val src _ _ _ _ _ _ hV p h6
    have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB p.val (by omega)
    by_cases h11 : p.val < 11
    · have e := hA_res (D p) (by rw [hvD]; omega) (by rw [hvD]; omega)
      rw [show (D p).val - (L.B + 43 + L.Pc) + 6 = p.val by rw [hvD]; omega] at e
      rw [Gn_old a r MB Rc 0 p.val (by rw [prod_low p.val (by omega)])]
      exact e
    · have hb : L.Blank (gwW mask.work (Cold.tapes a) k) (D p).val := by
        rw [hvD]
        have := p.isLt
        simp only [HostLay.Blank, HostLay.B, HostLay.P0, HostLay.tc] at *
        omega
      obtain ⟨e1, e2⟩ := hA_bl (D p) hb
      refine ⟨?_, e2⟩
      rw [e1]
      by_cases h30 : p.val < 30
      · exact (Gn_new a r MB Rc 0 p.val (prod_pos p.val (by omega) h30)).symm
      · exact (Gn_high a r MB Rc 0 p.val (by omega)).symm
  obtain ⟨Hf, Ef, st, fin⟩ := Words.words_run selector mask SB hIn r MB Rc (fun p => A (D p)) (fun p => (hent p).1)
    hNw hS hT cq ck cm ci hneed (by omega)
  have d := st.dock D hinj H A (fun p => (hent p).2) (fun _ => rfl)
  -- the exit and its view
  set A1 := install D A Ef with hA1
  set H1 := dockH D H Hf with hH1
  let Av : Fin V → List Bool := fun x => if L.NSv x.val then [] else A1 x
  have off : ∀ x, (∀ p, D p ≠ x) → A1 x = A x ∧ H1 x = H x :=
    fun x hx => ⟨install_other D A Ef x hx, dockH_other D H Hf x hx⟩
  have hit : ∀ p : Fin N, p.val < 29 → A1 (D p) = ZeroPadding.pad Rc (wd a r MB p.val) ∧ H1 (D p) = 0 := by
    intro p hp
    rw [hA1, hH1, install_slot D hinj, dockH_slot D hinj]
    exact fin p (by omega)
  have nh : ∀ x : Fin V, x.val < L.gB → ¬ L.IsTgt x.val → ∀ p, D p ≠ x :=
    fun x h1 h2 => L.nohit src N hV (fun i => (hsr i).1) hN x h1 h2
  have ctx : Ctx L (gwW mask.work (Cold.tapes a) k) r MB Rc dR H1 Av := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x p h6 h29 hv
      have ex : D ⟨p, by omega⟩ = x := L.dock_at src N hV ⟨p, by omega⟩ x h6 hv
      have hns : ¬ L.NSv x.val := by
        rw [← hv]
        have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB p h6
        simp only [HostLay.NSv, HostLay.B, HostLay.P0, HostLay.tc] at *
        omega
      have e := hit ⟨p, by omega⟩ h29
      rw [ex] at e
      exact ⟨by simp only [Av]; rw [if_neg hns]; exact e.1, e.2⟩
    · intro x ⟨h1, h2, h3, h4⟩
      obtain ⟨e1, e2⟩ := off x (nh x h1 h2)
      obtain ⟨b1, b2⟩ := hA_bl x h3
      exact ⟨by simp only [Av]; rw [if_neg h4, e1, b1], by rw [e2, b2]⟩
    · intro x hx
      have hc : x.val < L.gB ∧ ¬ L.IsTgt x.val ∧ L.Blank (gwW mask.work (Cold.tapes a) k) x.val := by
        simp only [HostLay.NSv, HostLay.IsTgt, HostLay.Blank, HostLay.B, HostLay.P0, HostLay.tc] at *
        omega
      obtain ⟨e1, e2⟩ := off x (nh x hc.1 hc.2.1)
      obtain ⟨b1, b2⟩ := hA_bl x hc.2.2
      exact ⟨by simp only [Av]; rw [if_pos hx], by rw [e2, b2]⟩
    · have v1 := L.hrw1
      have hG := L.hG
      have hF := L.hF
      have hns : ¬ L.NSv (L.rewindSlots 1).val := by
        simp only [HostLay.NSv, HostLay.P0] at *; omega
      have ht : ¬ L.IsTgt (L.rewindSlots 1).val := by
        simp only [HostLay.IsTgt, HostLay.B, HostLay.P0, HostLay.tc] at *; omega
      obtain ⟨e1, e2⟩ := off _ (nh _ (by simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega) ht)
      exact ⟨by simp only [Av]; rw [if_neg hns, e1, hA_rw.1], by rw [e2, hA_rw.2.1]⟩
    · have v2 := L.hrw2
      have hG := L.hG
      have hF := L.hF
      have hns : ¬ L.NSv (L.rewindSlots 2).val := by
        simp only [HostLay.NSv, HostLay.P0] at *; omega
      have ht : ¬ L.IsTgt (L.rewindSlots 2).val := by
        simp only [HostLay.IsTgt, HostLay.B, HostLay.P0, HostLay.tc] at *; omega
      obtain ⟨e1, e2⟩ := off _ (nh _ (by simp only [HostLay.B, HostLay.P0, HostLay.tc] at *; omega) ht)
      exact ⟨by simp only [Av]; rw [if_neg hns, e1, hA_rw.2.2.1], by rw [e2, hA_rw.2.2.2]⟩
  refine ⟨H1, A1, Av, d, ?_, resident_of_ctx L _ r layout caps MB Rc dR H1 Av ctx hMB hdR hR1 (by omega) cq ck cm hNw hS ci hT
    cl1 cl2, ?_⟩
  · intro x
    by_cases hx : L.NSv x.val
    · have hc : x.val < L.gB ∧ ¬ L.IsTgt x.val ∧ L.Blank (gwW mask.work (Cold.tapes a) k) x.val ∧
          L.G ≤ x.val ∧ x.val < L.P0 + 408 + mask.work + L.tc := by
        simp only [HostLay.NSv, HostLay.IsTgt, HostLay.Blank, HostLay.B, HostLay.P0, HostLay.tc] at *
        omega
      obtain ⟨e1, _⟩ := off x (nh x hc.1 hc.2.1)
      rw [e1, (hA_bl x hc.2.2.1).1, hRpad x hc.2.2.2.1 hc.2.2.2.2]
      simp only [Av]
      rw [if_pos hx]
      exact (Item4.pad_nil_blank Rc).symm
    · simp only [Av]
      rw [if_neg hx]
      exact (pad_long _ _ ((hlenfl x).trans (RunBound.step_len_ge d x))).symm
  · intro x hx
    by_cases hr : ∃ p, D p = x
    · obtain ⟨p, rfl⟩ := hr
      have h11 : p.val < 11 := by
        by_contra hc
        exact hx p (by omega) rfl
      obtain ⟨e1, e2⟩ := hit p (by omega)
      obtain ⟨g1, g2⟩ := hent p
      refine ⟨?_, by rw [e2, g2]⟩
      rw [e1, g1, Gn_old a r MB Rc 0 p.val (by rw [prod_low p.val (by omega)])]
    · simp only [not_exists] at hr
      exact off x hr

end host

end
end NearCubicWires.SourceFactorSel.WordsHost

