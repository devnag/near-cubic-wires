import Proof.Rows.RowsInitGlobal
import Proof.Rows.RowsFinalNE

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace RowsInit.FrameEntry
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.P1Closure
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open RowsConstruction RowsConstruction.BaseLayout RowsConstruction.PartsStep RowsConstruction.PartsFill
open RowsInit.Global (wS hS fS cS hFin)
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (NI : ℕ)
  (pubOf : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin 2 → List Bool)
  (initOf : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin NI → List Bool)
  (rcpOf : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin 64 → List Bool)
  (Rp : Request → ℕ) (c : PCJ38fbfed565f64139_Row.Code printer (rowTapes printer (rowsWork NI)))
  (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
  (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps)

/-- `InitHole'.initial`'s entry configuration, the completion code `c` generalized. -/
abbrev E := PCJ38fbfed565f64139_Family.entry printer c (r.family a)
  (RowsConstruction.stateOf selector a printer (rowsWork NI) (rowpPort NI 0) (rowpPort NI 1) (reserveFn selector a)
    (baseFn selector a NI pubOf initOf rcpOf) (fuelOf a Rp) (rowFuelOf printer a Rp) r layout facts caps)

theorem E_heads : (E selector a printer NI pubOf initOf rcpOf Rp c r layout facts caps).heads =
    Fin.addCases (PCJ45bee56da9f34d5a_RowState.headBank printer (rowsWork NI) a (r.family a) (geometryOf selector a r) 0 [])
      (fun _ : Fin 1 => 1) := rfl

theorem E_tapes : (E selector a printer NI pubOf initOf rcpOf Rp c r layout facts caps).tapes =
    Fin.addCases (PCJ45bee56da9f34d5a_RowState.bank printer (rowsWork NI) a (r.family a) (geometryOf selector a r) layout caps
      (reserveOf caps) (baseFn selector a NI pubOf initOf rcpOf r layout caps) (rowpPort NI 0) (rowpPort NI 1) 0 [])
      (fun _ : Fin 1 => CompareMachine.word (r.family a).rows.attach.length) := rfl

omit pubOf initOf rcpOf Rp c layout facts caps in
theorem rawBefore_zero : PCJ38fbfed565f64139_Family.rawBefore a (r.family a) (geometryOf selector a r) 0 = [] := by
  simp [PCJ38fbfed565f64139_Family.rawBefore]

omit pubOf initOf rcpOf Rp c layout facts caps in
theorem cS_ne_castSucc (y : Fin (rowTapes printer (rowsWork NI))) : Fin.castSucc y ≠ cS printer NI := by
  intro h
  have h1 := congrArg Fin.val h
  rw [RowsInit.Global.cS_val, Fin.val_castSucc] at h1
  have h2 := y.isLt
  have h3 := RowsInit.Global.T_eq printer NI
  have h4 : rowsWork NI = NI + 610 := rfl
  omega

/-- **The entry heads ARE RX's `hFin`** (`1` on the counter tape and on Header 277, `0` elsewhere). -/
theorem entry_heads : (E selector a printer NI pubOf initOf rcpOf Rp c r layout facts caps).heads = hFin printer NI := by
  rw [E_heads]
  funext x
  refine Fin.lastCases ?_ (fun y => ?_) x
  · have e : Fin.last (rowTapes printer (rowsWork NI)) = Fin.natAdd (rowTapes printer (rowsWork NI)) (0 : Fin 1) := rfl
    conv_lhs => rw [e, Fin.addCases_right]
    simp [hFin, RowsInit.Global.cS]
  · have e : Fin.castSucc y = Fin.castAdd 1 y := rfl
    conv_lhs => rw [e, Fin.addCases_left]
    have hc := cS_ne_castSucc printer NI y
    rcases PCJ45bee56da9f34d5a_RowState.port_classify printer (rowsWork NI) y with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [PCJ45bee56da9f34d5a_RowState.headBank, PCJ45bee56da9f34d5a_RowState.portCases_header,
        rawBefore_zero selector a r]
      unfold hFin
      have e : Fin.castSucc (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork (rowsWork NI)) k) = hS printer NI k := rfl
      rw [e]
      by_cases hk : k = 277
      · subst hk
        simp [CompactColdFamily.ambientH, CompactNativeInitialize.heads]
      · have hne : hS printer NI k ≠ hS printer NI 277 := fun h => hk (RowsInit.Global.hS_inj printer NI h)
        have hcs : hS printer NI k ≠ cS printer NI := hc
        have hn : ¬ (hS printer NI k = cS printer NI ∨ hS printer NI k = hS printer NI 277) := by
          rintro (h | h)
          · exact hcs h
          · exact hne h
        rw [if_neg hn]
        simp only [CompactColdFamily.ambientH, CompactNativeInitialize.heads, List.length_nil]
        split_ifs <;> rfl
    · rw [PCJ45bee56da9f34d5a_RowState.headBank, PCJ45bee56da9f34d5a_RowState.portCases_frame]
      unfold hFin
      have e : Fin.castSucc (PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork (rowsWork NI)) k) = fS printer NI k := rfl
      rw [e]
      have h277 : fS printer NI k ≠ hS printer NI 277 := by
        intro h
        have := congrArg Fin.val h
        rw [RowsInit.Global.fS_val, RowsInit.Global.hS_val] at this
        simp at this
        omega
      have hn : ¬ (fS printer NI k = cS printer NI ∨ fS printer NI k = hS printer NI 277) := by
        rintro (h | h)
        · exact hc h
        · exact h277 h
      rw [if_neg hn]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simp [PCJ38fbfed565f64139_Row.Frame.heads, PCJeb9c0f0306e9481c_FramingSpec.heads]
      · simp only [PCJ38fbfed565f64139_Row.Frame.heads, PCJeb9c0f0306e9481c_FramingSpec.heads, Fin.addCases_right]
        fin_cases i <;> rfl
    · rw [PCJ45bee56da9f34d5a_RowState.headBank, PCJ45bee56da9f34d5a_RowState.portCases_work]
      unfold hFin
      have e : Fin.castSucc (PCJ45bee56da9f34d5a_RowState.workSlot printer (rowsWork NI) k) = wS printer NI k := rfl
      rw [e]
      have h277 : wS printer NI k ≠ hS printer NI 277 := by
        intro h
        have := congrArg Fin.val h
        rw [RowsInit.Global.wS_val, RowsInit.Global.hS_val] at this
        simp at this
        omega
      have hn : ¬ (wS printer NI k = cS printer NI ∨ wS printer NI k = hS printer NI 277) := by
        rintro (h | h)
        · exact hc h
        · exact h277 h
      rw [if_neg hn]

/-- **Any bank with the entry's four blocks IS `entry.tapes`** (the Frame block in `TailOut.frm`'s form, the counter in `TailOut.ctr`'s). -/
theorem entry_tapes (B : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool)
    (hh : ∀ k, B (hS printer NI k) = PCJ45bee56da9f34d5a_RowState.headerBank a (r.family a) (geometryOf selector a r) layout
      (reserveOf caps) 0 k)
    (hf : ∀ k, B (fS printer NI k) = if k.val = P1TopDownPaidPayload.tapes printer then
      List.replicate caps.descriptorReserve false else List.replicate caps.copyCap false)
    (hw : ∀ x, B (wS printer NI x) = PCJ45bee56da9f34d5a_RowState.workBank (rowsWork NI) caps
      (baseFn selector a NI pubOf initOf rcpOf r layout caps) (rowpPort NI 0) (rowpPort NI 1) 0 x)
    (hc : B (cS printer NI) = CompareMachine.word (r.family a).rows.length) :
    (E selector a printer NI pubOf initOf rcpOf Rp c r layout facts caps).tapes = B := by
  rw [E_tapes]
  funext x
  refine Fin.lastCases ?_ (fun y => ?_) x
  · have e : Fin.last (rowTapes printer (rowsWork NI)) = Fin.natAdd (rowTapes printer (rowsWork NI)) (0 : Fin 1) := rfl
    conv_lhs => rw [e, Fin.addCases_right]
    rw [List.length_attach]
    exact hc.symm
  · have e : Fin.castSucc y = Fin.castAdd 1 y := rfl
    conv_lhs => rw [e, Fin.addCases_left]
    rcases PCJ45bee56da9f34d5a_RowState.port_classify printer (rowsWork NI) y with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [PCJ45bee56da9f34d5a_RowState.bank, PCJ45bee56da9f34d5a_RowState.portCases_header]
      exact (hh k).symm
    · rw [PCJ45bee56da9f34d5a_RowState.bank, PCJ45bee56da9f34d5a_RowState.portCases_frame]
      refine Eq.trans ?_ (hf k).symm
      unfold PCJ45bee56da9f34d5a_RowState.frameBank
      split_ifs
      · exact RowsInit.ThrInitRun.pad_nil _
      · rfl
    · rw [PCJ45bee56da9f34d5a_RowState.bank, PCJ45bee56da9f34d5a_RowState.portCases_work]
      exact (hw k).symm

end
end RowsInit.FrameEntry
