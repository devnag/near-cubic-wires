import Proof.SourceAssembly.SourceRefillSeam

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-- **The refill prologue**: the clear on `clr2`, then `rest`, then the driver refresh. ONE fixed machine. -/
def refillPro {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt2 se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) :=
  Composition.machine
    (RecoveryFocus.machine (Dims.clr2 e.ext1 hV) (PCJ6e421fabe2aa4155_SourceClear.machine (d.tcl2 se.extra sp.extra gW)))
    (Composition.machine (restMachine se sp e.ext1 hV g7M) (refreshMachine e hV))

section layout
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- Every tape of `InClear` is a stage tape of `clr2`. -/
theorem clr2_cover (x : Fin V) (hx : d.InClear eX pX gW x.val) :
    ∃ kk : Fin (d.tcl2 eX pX gW), Dims.clr2 e hV (Fin.castAdd 1 (Fin.castAdd 1 kk)) = x := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  have ht : d.tcl = d.rt + d.pscr := rfl
  have ht2 : d.tcl2 eX pX gW = d.tcl + 14 + restPc eX pX gW := rfl
  unfold SourceConstruction.Dims.InClear at hx
  rcases hx with h | h | h | h
  · refine ⟨⟨x.val - d.F, by omega⟩, Fin.ext ?_⟩
    simp only [Dims.clr2, Dims.clr2V, SourceConstruction.Dims.clearV, Fin.val_castAdd]
    split_ifs <;> omega
  · refine ⟨⟨d.rt + (x.val - d.G), by omega⟩, Fin.ext ?_⟩
    simp only [Dims.clr2, Dims.clr2V, SourceConstruction.Dims.clearV, Fin.val_castAdd]
    split_ifs <;> omega
  · refine ⟨⟨d.tcl + (x.val - d.B), by omega⟩, Fin.ext ?_⟩
    simp only [Dims.clr2, Dims.clr2V, SourceConstruction.Dims.clearV, Fin.val_castAdd]
    split_ifs <;> omega
  · refine ⟨⟨d.tcl + 14 + (x.val - d.B - 19), by omega⟩, Fin.ext ?_⟩
    simp only [Dims.clr2, Dims.clr2V, SourceConstruction.Dims.clearV, Fin.val_castAdd]
    split_ifs <;> omega

/-- Off `InClear` and off the driver/log, a tape is not in `clr2`. -/
theorem clr2_off (x : Fin V) (h1 : ¬ d.InClear eX pX gW x.val) (h2 : x ≠ d.scr hV 11) (h3 : x ≠ d.scr hV 12) :
    ∀ kk, Dims.clr2 e hV kk ≠ x := by
  intro kk hk
  have hkv := kk.isLt
  by_cases hs : kk.val < d.tcl2 eX pX gW
  · have e1 : kk = Fin.castAdd 1 (Fin.castAdd 1 ⟨kk.val, hs⟩) := Fin.ext rfl
    rw [e1] at hk
    exact h1 (hk ▸ Dims.clr2_in e hV _)
  by_cases hd : kk.val = d.tcl2 eX pX gW
  · have e1 : kk = Fin.castAdd 1 ((0 : Fin 1).natAdd (d.tcl2 eX pX gW)) := Fin.ext (by simp [hd])
    rw [e1, Dims.clr2_driver] at hk
    exact h2 hk.symm
  · have e1 : kk = (0 : Fin 1).natAdd (d.tcl2 eX pX gW + 1) := Fin.ext (by simp; omega)
    rw [e1, Dims.clr2_log] at hk
    exact h3 hk.symm

theorem out_in {v : Nat} (h : OutV d eX pX gW v) : d.InClear eX pX gW v := by
  unfold OutV at h; unfold SourceConstruction.Dims.InClear restPc at *; omega

/-- The per-call block is inside the clear set. -/
theorem pcT_in (i : Fin (restPc eX pX gW)) : d.InClear eX pX gW (Dims.pcT e hV i).val := by
  have := i.isLt
  unfold SourceConstruction.Dims.InClear; simp only [Dims.pcT]; omega

/-- A tape below the per-call block is off the cursor's dock. -/
theorem curSlots_ne_below (x : Fin V) (hx : x.val < d.B + 19) (i : Fin 3) : curSlots e hV i ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  fin_cases i <;> simp [curSlots, SourceConstruction.Dims.pcT, SourceConstruction.Dims.rsT] at hv <;> omega

/-- **The clear's exit**, tape by tape. -/
theorem clear_facts (Rc : Nat) (Hout : Fin V → Nat) (amb : Fin V → List Bool) :
    (∀ x : Fin V, d.InClear eX pX gW x.val → install (Dims.clr2 e hV) amb
      (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false) (List.replicate Rc true)
        (List.replicate (Rc+2) false)) x = List.replicate Rc false) ∧
    (∀ x : Fin V, d.InClear eX pX gW x.val → dockH (Dims.clr2 e hV) Hout (fun _ => 0) x = 0) ∧
    install (Dims.clr2 e hV) amb (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false)
      (List.replicate Rc true) (List.replicate (Rc+2) false)) (d.scr hV 11) = List.replicate Rc true ∧
    dockH (Dims.clr2 e hV) Hout (fun _ => 0) (d.scr hV 11) = 0 ∧
    install (Dims.clr2 e hV) amb (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false)
      (List.replicate Rc true) (List.replicate (Rc+2) false)) (d.scr hV 12) = List.replicate (Rc+2) false ∧
    dockH (Dims.clr2 e hV) Hout (fun _ => 0) (d.scr hV 12) = 0 ∧
    (∀ x : Fin V, ¬ d.InClear eX pX gW x.val → x ≠ d.scr hV 11 → x ≠ d.scr hV 12 →
      install (Dims.clr2 e hV) amb (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false)
        (List.replicate Rc true) (List.replicate (Rc+2) false)) x = amb x) ∧
    (∀ x : Fin V, ¬ d.InClear eX pX gW x.val → x ≠ d.scr hV 11 → x ≠ d.scr hV 12 →
      dockH (Dims.clr2 e hV) Hout (fun _ => 0) x = Hout x) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, fun x h1 h2 h3 => ?_⟩
  · obtain ⟨kk, hk⟩ := clr2_cover e hV x hx
    rw [← hk, install_slot _ (Dims.clr2_injective e hV)]
    simp [PCJ6e421fabe2aa4155_SourceClear.join]
  · obtain ⟨kk, hk⟩ := clr2_cover e hV x hx
    rw [← hk, dockH_slot _ (Dims.clr2_injective e hV)]
  · rw [← Dims.clr2_driver e hV, install_slot _ (Dims.clr2_injective e hV), PCJ6e421fabe2aa4155_SourceClear.join,
      Fin.addCases_left, Fin.addCases_right]
  · rw [← Dims.clr2_driver e hV, dockH_slot _ (Dims.clr2_injective e hV)]
  · rw [← Dims.clr2_log e hV, install_slot _ (Dims.clr2_injective e hV), PCJ6e421fabe2aa4155_SourceClear.join,
      Fin.addCases_right]
  · rw [← Dims.clr2_log e hV, dockH_slot _ (Dims.clr2_injective e hV)]
  · exact install_other _ amb _ x (clr2_off e hV x h1 h2 h3)
  · exact dockH_other _ Hout _ x (clr2_off e hV x h1 h2 h3)

end layout

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

/-- **`Resident` survives** any change off the tapes it reads (`LowT`: below the family bank's end, the loader
scratch, `lenTape`). -/
theorem resident_keep_low (e : (𝔇).Ext) {V : Nat} (hV : (𝔇).U ≤ V) {r' : Request}
    {layout : Packets.Layout (decompositionOf sources) (r'.family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) r')} {caps : RowCaps}
    {H H' : Fin V → Nat} {A A' : Fin V → List Bool}
    (res0 : Resident mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
        ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
        ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e hV)
        ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
        (Dims.lenTape e hV) r' layout caps H A)
    (avT : ∀ x : Fin V, LowT (𝔇) x.val → A' x = A x) (hT : ∀ x : Fin V, LowT (𝔇) x.val → H' x = H x) :
    Nonempty (Resident mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
        ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
        ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e hV)
        ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
        (Dims.lenTape e hV) r' layout caps H' A') :=
  ⟨resident_transport res0 H' A'
    (fun jj => avT _ (low_slot hV jj)) (fun ii => avT _ (low_mask hV ii)) (fun jj => avT _ (low_pslots hV jj))
    (fun ii => avT _ (low_pool hV ii)) (fun ii => avT _ (low_family hV ii))
    (fun ii => avT _ (low_rewind e hV ii))
    (fun ii => avT _ (low_ret hV ii)) (avT _ (low_scr hV 0 (by decide))) (avT _ (low_scr hV 1 (by decide)))
    (avT _ (low_scr hV 5 (by decide))) (avT _ (low_scr hV 6 (by decide))) (avT _ (low_scr hV 7 (by decide)))
    (avT _ (low_scr hV 8 (by decide))) (avT _ (low_scr hV 9 (by decide))) (avT _ (low_scr hV 10 (by decide)))
    (avT _ (low_len e hV))
    (fun jj => hT _ (low_slot hV jj)) (fun ii => hT _ (low_mask hV ii))
    (fun jj => hT _ (low_pslots hV jj)) (fun ii => hT _ (low_pool hV ii))
    (fun ii => hT _ (low_family hV ii)) (fun ii => hT _ (low_rewind e hV ii))
    (fun ii => hT _ (low_ret hV ii)) (hT _ (low_scr hV 0 (by decide)))
    (hT _ (low_scr hV 1 (by decide))) (hT _ (low_scr hV 5 (by decide)))
    (hT _ (low_scr hV 6 (by decide))) (hT _ (low_scr hV 7 (by decide)))
    (hT _ (low_scr hV 8 (by decide))) (hT _ (low_scr hV 9 (by decide)))
    (hT _ (low_scr hV 10 (by decide))) (hT _ (low_len e hV))⟩

end concrete

end
end NearCubicWires.SourceConstruction.Rest
end
