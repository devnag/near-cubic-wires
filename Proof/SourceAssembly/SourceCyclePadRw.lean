import Proof.SourceAssembly.SourceCyclePad

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ1fef9807c6954e94_Native PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open SupplierEstimator SupplierPipeline NearCubicWires.P1Closure
namespace NearCubicWires.SourceConstruction.Cycle
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- **`cycle_prepared_pad` with the rewind tapes at the exit** (see the module header). -/
theorem cycle_prepared_pad_rw {U s : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective pslots)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U)
    (retDrv log rawDrv rawDst rawLog : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (hfinj : Function.Injective familySlots)
    (poolSlots : Fin 373 → Fin U) (hpinj : Function.Injective poolSlots)
    (rewindSlots : Fin 3 → Fin U) (hrinj : Function.Injective rewindSlots)
    (hraw : pslots packet.ordinary.program.outputTape = familySlots
      ((PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork rows.privateWork) 262).castAdd 1))
    (hpool : poolSlots 34 = familySlots
      ((PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork rows.privateWork) 0).castAdd 1))
    (hsrc : rewindSlots 0 = familySlots
      ((PCJ38fbfed565f64139_Ready.descriptor printer (rowWork rows.privateWork)).castAdd 1))
    (s1 d1 l1 s2 d2 l2 lenTape : Fin U) (pre : Machine U s)
    (cs : Fin 16 → Fin U) (fam : Fin (r_tapes printer) → Fin U) (drv : Fin 7 → Fin U)
    (w : Wiring mask packet rows maskSlots pslots slot ret retDrv log familySlots poolSlots
      rewindSlots s1 d1 l1 s2 d2 l2 lenTape cs fam drv)
    (H1 : Fin U → Nat) (A1 : Fin U → List Bool) (Av : Fin U → List Bool) (R : Fin U → Nat)
    (hM : ∀ x, A1 x = ZeroPadding.pad (R x) (Av x))
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) (good : RowCaps.Good selector a printer r layout facts caps)
    (res : SourceRequest.Resident mask packet rows maskSlots pslots slot ret retDrv log familySlots
      poolSlots rewindSlots s1 d1 l1 s2 d2 l2 lenTape r layout caps H1 Av)
    (hR1 : R (rewindSlots 1) = 0) (hR2 : R (rewindSlots 2) = 0)
    (M2 U0 Rc S Rw B v : Nat)
    (hM2 : A1 (cs 1) = ZeroPadding.pad Rc (List.replicate M2 true))
    (hU0 : A1 (cs 2) = ZeroPadding.pad Rc (List.replicate U0 true))
    (hwork : ∀ k : Fin 16, 4 ≤ k.val → A1 (cs k) = ZeroPadding.pad Rc [])
    (hcsH : ∀ k : Fin 16, k.val ≠ 0 → k.val ≠ 3 → H1 (cs k) = 0)
    (hS : A1 (drv 0) = ZeroPadding.pad Rc (UnaryTemplate.tape S))
    (hR : A1 (drv 1) = ZeroPadding.pad Rc (UnaryTemplate.tape Rw))
    (hB : A1 (drv 2) = ZeroPadding.pad Rc (UnaryTemplate.tape B))
    (hv : A1 (drv 4) = ZeroPadding.pad Rc (UnaryTemplate.tape v))
    (hdH : ∀ k : Fin 7, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4) → H1 (drv k) = 1)
    (hfamA : ∀ i, i ≠ PCJ515eaa990d75455b_FamilyInit.sourcePort printer →
      A1 (fam i) = List.replicate Rc false)
    (hfamH : ∀ i, i ≠ PCJ515eaa990d75455b_FamilyInit.sourcePort printer → H1 (fam i) = 0)
    (hcnt : SourceRequest.famReserve res R (Fin.last _) = Rc)
    (hdesc : max (SourceRequest.famReserve res R (SLoad.Final.port printer rows)) caps.descriptorReserve = Rc)
    (hL : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length + 3 ≤ Rc) :
    ∃ H' A', (∀ (n : Nat) (H0 : Fin U → Nat) (A0 : Fin U → List Bool), Step pre n H0 A0 H1 A1 →
      (cycleCode mask packet rows maskSlots hminj pslots hsinj slot ret retDrv log rawDrv
        rawDst rawLog familySlots hfinj poolSlots hpinj rewindSlots hrinj hraw hpool hsrc
        s1 d1 l1 s2 d2 l2 pre cs fam drv).Prepared
        (dataList a (r.family a) (geometryOf selector a r) layout facts)
        ((n + 1 + SourceRequest.seedFuel mask packet r) + 1 +
          (BinaryCacheColdRun.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) + 1 +
            (SLoad.Setup.cost (r.input a).length
                (SLoad.Setup.metaBits layout.w layout.degree layout.C caps).length + 1 +
              rowInitBudget a rows.coefficient rows.degree r layout.w layout.degree layout.C caps)) + 1 +
          (PCJ38fbfed565f64139_Family.budget printer (r.family a) (rows.state r layout facts caps) +
            1 + (2 * caps.descriptorReserve + 2 + 1 +
              (RowWidth.cost (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length
                  M2 U0 (dataList a (r.family a) (geometryOf selector a r) layout facts).length + 1 +
                initFuel printer ⟨S, Rw, B,
                  RowWidth.rw M2 U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length,
                  v, (dataList a (r.family a) (geometryOf selector a r) layout facts).length⟩))))
        H0 H' A0 A') ∧
      (cycleCode mask packet rows maskSlots hminj pslots hsinj slot ret retDrv log rawDrv
        rawDst rawLog familySlots hfinj poolSlots hpinj rewindSlots hrinj hraw hpool hsrc
        s1 d1 l1 s2 d2 l2 (PCJ6e421fabe2aa4155_SourceReuse.haltMachine U) cs fam drv).Prepared
        (dataList a (r.family a) (geometryOf selector a r) layout facts)
        ((0 + 1 + SourceRequest.seedFuel mask packet r) + 1 +
          (BinaryCacheColdRun.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) + 1 +
            (SLoad.Setup.cost (r.input a).length
                (SLoad.Setup.metaBits layout.w layout.degree layout.C caps).length + 1 +
              rowInitBudget a rows.coefficient rows.degree r layout.w layout.degree layout.C caps)) + 1 +
          (PCJ38fbfed565f64139_Family.budget printer (r.family a) (rows.state r layout facts caps) +
            1 + (2 * caps.descriptorReserve + 2 + 1 +
              (RowWidth.cost (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length
                  M2 U0 (dataList a (r.family a) (geometryOf selector a r) layout facts).length + 1 +
                initFuel printer ⟨S, Rw, B,
                  RowWidth.rw M2 U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length,
                  v, (dataList a (r.family a) (geometryOf selector a r) layout facts).length⟩))))
        H1 H' A1 A' ∧
      (∀ i, H' (fam i) = r_inputH printer (dataList a (r.family a) (geometryOf selector a r) layout facts)
        S Rw B (dataList a (r.family a) (geometryOf selector a r) layout facts).length i) ∧
      (∀ i, A' (fam i) = ZeroPadding.pad Rc
        (r_inputT printer (dataList a (r.family a) (geometryOf selector a r) layout facts) S Rw B
          (RowWidth.rw M2 U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length)
          v (dataList a (r.family a) (geometryOf selector a r) layout facts).length i)) ∧
      (∀ x, Free slot maskSlots pslots poolSlots familySlots rewindSlots x → (∀ k, cs k ≠ x) →
        (∀ i, fam i ≠ x) → (∀ k, drv k ≠ x) → H' x = H1 x ∧ A' x = A1 x) ∧
      H' (rewindSlots 1) = 0 ∧ A' (rewindSlots 1) = List.replicate caps.descriptorReserve true ∧
      H' (rewindSlots 2) = 0 ∧ A' (rewindSlots 2) = List.replicate caps.descriptorReserve false := by
  classical
  
  obtain ⟨poolA, hready, hraw', hframe⟩ := SourceRequest.seed_ready mask packet rows maskSlots hminj
    pslots hsinj slot w.hinj ret retDrv log rawDrv rawDst rawLog familySlots poolSlots rewindSlots
    s1 d1 l1 s2 d2 l2 lenTape w.hmsk w.hoffm w.hslot0 w.hoffp w.hmp w.hrm w.hrl w.hlm w.hdr w.hdl
    w.hDd w.hDl w.hpS w.hpM w.hpP r layout caps H1 Av res R
  have hz : (fun x => ZeroPadding.pad (R x) (Av x)) = A1 := funext fun x => (hM x).symm
  rw [hz] at hready
  
  have hsetup := SourceRequest.setup_ready mask packet rows maskSlots pslots slot ret retDrv log
    familySlots hfinj poolSlots hpinj rewindSlots s1 d1 l1 s2 d2 l2 lenTape w.hpP w.hpool0 w.hraw262
    w.hfamOut w.os1 w.od1 w.ol1 w.os2 w.od2 w.ol2 w.e1 w.e2 w.e3 w.e4 w.e5 w.e6 w.k1 w.k2 w.k3 w.k4
    w.k5 w.k6 w.m1 w.m2 w.m4 r layout caps H1 Av res R poolA hraw' hframe
  -- the setup exit's ambient bank, off the family bank, is the prologue's
  obtain ⟨amb, hamb⟩ : ∃ amb : Fin U → List Bool, amb =
      SLoad.Prepared.setupExit selector a printer rows.privateWork r layout caps familySlots
        (SourceRequest.famReserve res R)
        (install poolSlots poolA (fun i => ZeroPadding.pad (max (R (poolSlots i))
          (res.poolReserve i))
          (BinaryCacheColdRun.output (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) i))) :=
    ⟨_, rfl⟩
  have ambFree : ∀ x, SourceRequest.Outside slot maskSlots pslots poolSlots x →
      (∀ i, familySlots i ≠ x) → amb x = A1 x := by
    intro x hx hf
    have h := SourceRequest.setup_frame (selector := selector) (a := a) (printer := printer)
      rows.privateWork r layout caps slot maskSlots pslots familySlots poolSlots
      (SourceRequest.famReserve res R) (fun i => max (R (poolSlots i))
        (res.poolReserve i)) poolA Av R hframe x hx hf
    rw [install_other familySlots _ _ x hf] at h
    rw [hamb]
    exact h.trans (hM x).symm
  rw [← hamb] at hsetup
  
  obtain ⟨Hf, hHf⟩ : ∃ Hf : Fin U → Nat, Hf =
      dockH rewindSlots
        (dockH familySlots H1 (SLoad.Final.exitCfg printer rows layout facts caps).heads)
        (CompetitorRecordRewind.cfg 2
          (SLoad.Prepared.srcWord printer rows layout facts caps
            (SourceRequest.famReserve res R)) 0
          caps.descriptorReserve 0 0 (List.replicate caps.descriptorReserve false)).heads :=
    ⟨_, rfl⟩
  obtain ⟨Af, hAf⟩ : ∃ Af : Fin U → List Bool, Af =
      install rewindSlots
        (install familySlots amb (fun i => ZeroPadding.pad (SourceRequest.famReserve res R i)
          ((SLoad.Final.exitCfg printer rows layout facts caps).tapes i)))
        (fun i => ZeroPadding.pad ((![0, 0, caps.descriptorReserve] : Fin 3 → Nat) i)
          ((CompetitorRecordRewind.cfg 2
            (SLoad.Prepared.srcWord printer rows layout facts caps
              (SourceRequest.famReserve res R)) 0
            caps.descriptorReserve 0 0 (List.replicate caps.descriptorReserve false)).tapes i)) :=
    ⟨_, rfl⟩
  have fH : ∀ x, Free slot maskSlots pslots poolSlots familySlots rewindSlots x → Hf x = H1 x := by
    intro x ⟨_, hf, hr⟩
    rw [hHf, dockH_other rewindSlots _ _ x hr, dockH_other familySlots _ _ x hf]
  have fA : ∀ x, Free slot maskSlots pslots poolSlots familySlots rewindSlots x → Af x = A1 x := by
    intro x ⟨ho, hf, hr⟩
    rw [hAf, install_other rewindSlots _ _ x hr, install_other familySlots _ _ x hf]
    exact ambFree x ho hf
  
  have eA0 : Af (cs 0) = ZeroPadding.pad (max (R lenTape) res.capLen)
      (List.replicate (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length true) := by
    rw [fA _ (w.fcs 0 (by decide)), w.hlen, hM, res.w_len, Uniform.pad_pad]
  have eA1 : Af (cs 1) = ZeroPadding.pad Rc (List.replicate M2 true) := by
    rw [fA _ (w.fcs 1 (by decide))]; exact hM2
  have eA2 : Af (cs 2) = ZeroPadding.pad Rc (List.replicate U0 true) := by
    rw [fA _ (w.fcs 2 (by decide))]; exact hU0
  have eA3 : Af (cs 3) = ZeroPadding.pad Rc
      (CompareMachine.word (dataList a (r.family a) (geometryOf selector a r) layout facts).length) := by
    rw [w.hcnt, hAf, install_other rewindSlots _ _ _ w.hcntRew, install_slot familySlots hfinj,
      (exit_counter rows layout facts caps).1]
    rw [hcnt]
  have eAk : ∀ k : Fin 16, 4 ≤ k.val → Af (cs k) = ZeroPadding.pad Rc [] := by
    intro k hk
    rw [fA _ (w.fcs k (by omega))]; exact hwork k hk
  have eHc : ∀ k, Hf (cs k) = RowWidth.inH k := by
    intro k
    by_cases h3 : k.val = 3
    · have e : k = 3 := Fin.ext h3
      subst e
      rw [w.hcnt, hHf, dockH_other rewindSlots _ _ _ w.hcntRew, dockH_slot familySlots hfinj,
        (exit_counter rows layout facts caps).2]
      rfl
    · rw [fH _ (w.fcs k h3)]
      by_cases h0 : k.val = 0
      · have e : k = 0 := Fin.ext h0
        subst e
        rw [w.hlen, res.hH_len]; rfl
      · rw [hcsH k h0 h3]
        simp [RowWidth.inH, h3]
  have eU0 : Af (drv 0) = ZeroPadding.pad Rc (UnaryTemplate.tape S) := by
    rw [fA _ (w.fdrv 0 (Or.inl rfl))]; exact hS
  have eU1 : Af (drv 1) = ZeroPadding.pad Rc (UnaryTemplate.tape Rw) := by
    rw [fA _ (w.fdrv 1 (Or.inr (Or.inl rfl)))]; exact hR
  have eU2 : Af (drv 2) = ZeroPadding.pad Rc (UnaryTemplate.tape B) := by
    rw [fA _ (w.fdrv 2 (Or.inr (Or.inr (Or.inl rfl))))]; exact hB
  have eU4 : Af (drv 4) = ZeroPadding.pad Rc (UnaryTemplate.tape v) := by
    rw [fA _ (w.fdrv 4 (Or.inr (Or.inr (Or.inr rfl))))]; exact hv
  have eUH : ∀ k : Fin 7, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4) → Hf (drv k) = 1 := by
    intro k hk
    rw [fH _ (w.fdrv k hk)]; exact hdH k hk
  have eHf : ∀ i, Hf (fam i) = 0 := by
    intro i
    by_cases hi : i = PCJ515eaa990d75455b_FamilyInit.sourcePort printer
    · rw [hi, w.hsrcp, hHf, dockH_slot rewindSlots hrinj]
      rfl
    · rw [fH _ (w.ffam i hi)]; exact hfamH i hi
  have eSrc : Af (fam (PCJ515eaa990d75455b_FamilyInit.sourcePort printer)) =
      ZeroPadding.pad Rc ((dataList a (r.family a) (geometryOf selector a r) layout facts).flatMap
        (P1TopDownPaidReusable.Datum.word printer)) := by
    rw [w.hsrcp, hAf, install_slot rewindSlots hrinj]
    have hw : max (SourceRequest.famReserve res R (SLoad.Final.port printer rows))
        caps.descriptorReserve = Rc := hdesc
    show ZeroPadding.pad 0 (ZeroPadding.pad (max (SourceRequest.famReserve res R
        (SLoad.Final.port printer rows)) caps.descriptorReserve)
        (PCJ38fbfed565f64139_Cached.descriptorWord printer
          (dataList a (r.family a) (geometryOf selector a r) layout facts))) = _
    rw [hw, pad_zero]
    rfl
  have eBlank : ∀ i, i ≠ PCJ515eaa990d75455b_FamilyInit.sourcePort printer →
      Af (fam i) = List.replicate Rc false := by
    intro i hi
    rw [fA _ (w.ffam i hi)]; exact hfamA i hi
  obtain ⟨H', A', hstep, hfH, hfA, hfr⟩ := FinishCycle.finish_cycle printer
    (dataList a (r.family a) (geometryOf selector a r) layout facts)
    (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length
    M2 U0 Rc (max (R lenTape) res.capLen) S Rw B v cs w.hcs fam drv w.hjoin w.hd3 w.hd5 w.hd6 w.hfam_cs w.hdu_cs
    Hf Af eA0 eA1 eA2 eA3 eAk eHc hL eU0 eU1 eU2 eU4 eUH eHf eSrc eBlank
  rw [hHf, hAf] at hstep
  -- the rewind bank
  have hA1r : amb (rewindSlots 1) = List.replicate caps.descriptorReserve true :=
    (ambFree _ w.or1 w.h1).trans (by rw [hM, hR1, pad_zero]; exact res.s_rewind1)
  have hA2r : amb (rewindSlots 2) = List.replicate caps.descriptorReserve false :=
    (ambFree _ w.or2 w.h2).trans (by rw [hM, hR2, pad_zero]; exact res.s_rewind2)
  
  have csOff : ∀ i : Fin 3, (∀ j, familySlots j ≠ rewindSlots i) → ∀ k, cs k ≠ rewindSlots i := by
    intro i hfi k
    by_cases h3 : k.val = 3
    · have e : k = 3 := Fin.ext h3
      rw [e, w.hcnt]; exact hfi _
    · exact fun h => (w.fcs k h3).2.2 i h.symm
  have famOff : ∀ i : Fin 3, rewindSlots 0 ≠ rewindSlots i → ∀ i', fam i' ≠ rewindSlots i := by
    intro i h0 i'
    by_cases hs : i' = PCJ515eaa990d75455b_FamilyInit.sourcePort printer
    · rw [hs, w.hsrcp]; exact h0
    · exact fun h => (w.ffam i' hs).2.2 i h.symm
  have drvOff : ∀ i : Fin 3, (∀ j, familySlots j ≠ rewindSlots i) → ∀ k, drv k ≠ rewindSlots i := by
    intro i hfi k
    by_cases hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4
    · exact fun h => (w.fdrv k hk).2.2 i h.symm
    · have h356 : k = 3 ∨ k = 5 ∨ k = 6 := by
        revert hk; fin_cases k <;> decide
      rcases h356 with h | h | h <;> rw [h]
      · rw [w.hd3]; exact csOff i hfi 4
      · rw [w.hd5]; exact csOff i hfi 3
      · rw [w.hd6]; exact csOff i hfi 5
  have r1 := hfr (rewindSlots 1) (csOff 1 w.h1) (famOff 1 (fun h => absurd (hrinj h) (by decide))) (drvOff 1 w.h1)
  have r2 := hfr (rewindSlots 2) (csOff 2 w.h2) (famOff 2 (fun h => absurd (hrinj h) (by decide))) (drvOff 2 w.h2)
  have hr1H : Hf (rewindSlots 1) = 0 := by rw [hHf, dockH_slot rewindSlots hrinj]; rfl
  have hr2H : Hf (rewindSlots 2) = 0 := by rw [hHf, dockH_slot rewindSlots hrinj]; rfl
  have hr1A : Af (rewindSlots 1) = List.replicate caps.descriptorReserve true := by
    rw [hAf, install_slot rewindSlots hrinj]
    show ZeroPadding.pad 0 (List.replicate caps.descriptorReserve true) = _
    exact ZeroPadding.pad_zero _
  have hr2A : Af (rewindSlots 2) = List.replicate caps.descriptorReserve false := by
    rw [hAf, install_slot rewindSlots hrinj]
    show ZeroPadding.pad caps.descriptorReserve (List.replicate caps.descriptorReserve false) = _
    simp [ZeroPadding.pad]
  refine ⟨H', A', fun n H0 A0 hpre => SLoad.Prepared.prepared (cycleCode mask packet rows maskSlots hminj
      pslots hsinj slot ret retDrv log rawDrv rawDst rawLog familySlots hfinj poolSlots hpinj rewindSlots
      hrinj hraw hpool hsrc s1 d1 l1 s2 d2 l2 pre cs fam drv) layout facts caps good
    (fun i => max (R (poolSlots i)) (res.poolReserve i))
    (SourceRequest.famReserve res R) H1 H1 H0 H' poolA amb A0 A'
    (n + 1 + SourceRequest.seedFuel mask packet r) _ _ w.h1 w.h2 res.hH_rewind1 res.hH_rewind2
    hA1r hA2r (PCJ6e421fabe2aa4155_SourceRefill.prepend_ready _ pre r n _ H0 H1 _ A0 A1 _ hpre hready)
    hsetup hstep,
    SLoad.Prepared.prepared (cycleCode mask packet rows maskSlots hminj
      pslots hsinj slot ret retDrv log rawDrv rawDst rawLog familySlots hfinj poolSlots hpinj rewindSlots
      hrinj hraw hpool hsrc s1 d1 l1 s2 d2 l2 (PCJ6e421fabe2aa4155_SourceReuse.haltMachine U) cs fam drv)
      layout facts caps good
    (fun i => max (R (poolSlots i)) (res.poolReserve i))
    (SourceRequest.famReserve res R) H1 H1 H1 H' poolA amb A1 A'
    (0 + 1 + SourceRequest.seedFuel mask packet r) _ _ w.h1 w.h2 res.hH_rewind1 res.hH_rewind2
    hA1r hA2r (PCJ6e421fabe2aa4155_SourceRefill.prepend_ready _ _ r 0 _ H1 H1 _ A1 A1 _
      (PCJ6e421fabe2aa4155_SourceReuse.halt_step H1 A1) hready)
    hsetup hstep, hfH, hfA, ?_, r1.1.trans hr1H, r1.2.trans hr1A, r2.1.trans hr2H, r2.2.trans hr2A⟩
  intro x hx hcx hfx hdx
  obtain ⟨e1, e2⟩ := hfr x hcx hfx hdx
  exact ⟨e1.trans (fH x hx), e2.trans (fA x hx)⟩

end
end NearCubicWires.SourceConstruction.Cycle
end
