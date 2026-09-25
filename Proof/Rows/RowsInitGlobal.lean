import Proof.Rows.RowsInitWorkPhase
import Proof.Rows.RowsInitHdrSpec
import Proof.Rows.RowsInitFamilyWord

/-! # Rows initializer: the global stages on the whole row bank (work phase docked, Frame writer, counter, Header / bump)

**Consumer.** `FinalNE.InitHole'.initial` (`rows-construction-20260923/RowsFinalNE.lean`): ONE machine on
`Fin (rowTapes printer (rowsWork NI) + 1)` from `rowPublicInput` (all heads `0`) to `Family.entry`'s heads and tapes: Header block
(nonempty family: `pad (reserveOf caps k) (commonHeader k)`; empty family: the public pool word only), Header 277's head `1`,
the Frame block `RowState.frameBank caps []`, the work block `workBank … (baseOf … r) … 0`, and the family counter
`CompareMachine.word |rows|` with head `1`.

**Machine** (`initM`): the work phase `WorkPhase.workM` docked on the work slots ; the verified Frame writer
`RowsInit.frame_backing` (drivers: `rowp 0/1`, `rcp 40`; log: an `init` scratch port) ; the verified counter
`FamilyWord.word_run` docked (word on the extra tape, head `1`) ; `CloseoutRowsOriginalSwitch` on the nonempty flag (work port 150):
the Header writer `HdrSpec` (typed, RH) docked, else a one-step head bump on Header 277.

**Paper.** `paper.tex:1190-1212`. **Budget.** Work phase + `2cC+4+1+(2dR+4)` (linear) + the counter (SMALL) + Header (`HdrSpec.cost_le`)
or `1`, + `1` per composition, `2` per switch.
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.Global
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.PacketFamilyParent
open RowsInit.ThrLoop (wp wp_val rw_eq)
open RowsInit.ThrWork (port_cases stop_run cell0_rep)
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. The global ports -/

section Ports
variable (printer : WilliamsAlgorithm) (NI : ℕ)

def wS (k : Fin (2 + rowsWork NI)) : Fin (rowTapes printer (rowsWork NI) + 1) :=
  (PCJ45bee56da9f34d5a_RowState.workSlot printer (rowsWork NI) k).castSucc
def hS (k : Fin 440) : Fin (rowTapes printer (rowsWork NI) + 1) :=
  (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork (rowsWork NI)) k).castSucc
def fS (k : Fin (P1TopDownPaidPayload.tapes printer + 2)) : Fin (rowTapes printer (rowsWork NI) + 1) :=
  (PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork (rowsWork NI)) k).castSucc
def cS : Fin (rowTapes printer (rowsWork NI) + 1) := Fin.last _

theorem wS_val (k : Fin (2 + rowsWork NI)) :
    (wS printer NI k).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + k.val := rfl
theorem hS_val (k : Fin 440) : (hS printer NI k).val = k.val := rfl
theorem fS_val (k : Fin (P1TopDownPaidPayload.tapes printer + 2)) : (fS printer NI k).val = 440 + k.val := rfl
theorem cS_val : (cS printer NI).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + rowsWork NI) := rfl

theorem wS_inj : Function.Injective (wS printer NI) := fun x y h => Fin.ext (by
  have := congrArg Fin.val h; rw [wS_val, wS_val] at this; omega)
theorem hS_inj : Function.Injective (hS printer NI) := fun x y h => Fin.ext (by
  have := congrArg Fin.val h; rw [hS_val, hS_val] at this; omega)
theorem fS_inj : Function.Injective (fS printer NI) := fun x y h => Fin.ext (by
  have := congrArg Fin.val h; rw [fS_val, fS_val] at this; omega)

end Ports

/-! ## 2. `baseOf` off its `init` block, per block -/

section BaseOf
variable (a : DecompositionAlgorithm) (NI : ℕ) (pub pub' : Fin 2 → List Bool) (init init' : Fin NI → List Bool)
  (rcp rcp' : Fin 64 → List Bool) (C cC hF : ℕ)

theorem baseOf_pub (r : Request) (j : ℕ) (i : Fin 2) : baseOf a NI pub init rcp C cC hF r j (pubPort NI i) = pub i := by
  cases r with
  | terminal => simp [baseOf]
  | thr r four L target => exact (thr_base_rc a r four L target NI pub init rcp C cC hF j).1 i
  | sym r four L target => exact (sym_base_rc a r four L target NI pub init rcp C cC hF j).1 i

theorem baseOf_init (r : Request) (j : ℕ) (i : Fin NI) : baseOf a NI pub init rcp C cC hF r j (initPort NI i) = init i := by
  cases r with
  | terminal => simp [baseOf]
  | thr r four L target => exact (thr_base_rc a r four L target NI pub init rcp C cC hF j).2.1 i
  | sym r four L target => exact (sym_base_rc a r four L target NI pub init rcp C cC hF j).2.1 i

theorem baseOf_rcp (r : Request) (j : ℕ) (i : Fin 64) : baseOf a NI pub init rcp C cC hF r j (rcpPort NI i) = rcp i := by
  cases r with
  | terminal => simp [baseOf]
  | thr r four L target => exact (thr_base_rc a r four L target NI pub init rcp C cC hF j).2.2.2 i
  | sym r four L target => exact (sym_base_rc a r four L target NI pub init rcp C cC hF j).2.2.2 i

/-- Off the `pub`, `init`, `rcp` blocks, `baseOf` does not depend on them. -/
theorem baseOf_indep (r : Request) (j : ℕ) (p : Fin (2 + rowsWork NI))
    (hp1 : ∀ i, p ≠ pubPort NI i) (hp2 : ∀ i, p ≠ initPort NI i) (hp3 : ∀ i, p ≠ rcpPort NI i) :
    baseOf a NI pub init rcp C cC hF r j p = baseOf a NI pub' init' rcp' C cC hF r j p := by
  rcases port_cases NI p with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact absurd rfl (hp1 i)
  · exact absurd rfl (hp2 i)
  · cases r with
    | terminal => simp [baseOf]
    | thr r four L target =>
      exact ((thr_base_rc a r four L target NI pub init rcp C cC hF j).2.2.1 i).trans
        ((thr_base_rc a r four L target NI pub' init' rcp' C cC hF j).2.2.1 i).symm
    | sym r four L target =>
      exact ((sym_base_rc a r four L target NI pub init rcp C cC hF j).2.2.1 i).trans
        ((sym_base_rc a r four L target NI pub' init' rcp' C cC hF j).2.2.1 i).symm
  · exact absurd rfl (hp3 i)
  · cases r with
    | terminal => simp [baseOf]
    | thr r four L target => cases h : thrKeyAt a r L target j <;> simp [baseOf, thrBase, h]
    | sym r four L target => cases h : symKeyAt r L target j <;> simp [baseOf, symBase, h]
  · cases r with
    | terminal => simp [baseOf]
    | thr r four L target => cases h : thrKeyAt a r L target j <;> simp [baseOf, thrBase, h]
    | sym r four L target => cases h : symKeyAt r L target j <;> simp [baseOf, symBase, h]
  · cases r with
    | terminal => simp [baseOf]
    | thr r four L target => cases h : thrKeyAt a r L target j <;> simp [baseOf, thrBase, h]
    | sym r four L target => cases h : symKeyAt r L target j <;> simp [baseOf, symBase, h]

end BaseOf

/-! ## 3. Global value maps -/

section Maps
variable (printer : WilliamsAlgorithm) (NI : ℕ)

/-- The global port of value `v` (clamped; every use has `v` in range). -/
def gp (v : ℕ) : Fin (rowTapes printer (rowsWork NI) + 1) := ⟨v % (rowTapes printer (rowsWork NI) + 1), Nat.mod_lt _ (by omega)⟩

theorem gp_val {v : ℕ} (h : v < rowTapes printer (rowsWork NI) + 1) : (gp printer NI v).val = v := Nat.mod_eq_of_lt h

theorem T_eq : rowTapes printer (rowsWork NI) = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + (NI + 610)) := rfl

/-- The work port of work value `k` as a global value. -/
abbrev wv (k : ℕ) : ℕ := 440 + (P1TopDownPaidPayload.tapes printer + 2) + k

/-- The named work ports' global values. -/
theorem wvals :
    (wS printer NI (pubPort NI 0)).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) ∧
    (wS printer NI (pubPort NI 1)).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + 1 ∧
    (wS printer NI (rowpPort NI 6)).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + NI + 6) ∧
    (wS printer NI (rowpPort NI 7)).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + NI + 7) ∧
    (wS printer NI (wp NI 150)).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + 150 ∧
    (cS printer NI).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + (NI + 610)) := by
  have hW := rw_eq NI
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [wS_val, rowpPort_val]; rfl
  · rw [wS_val, rowpPort_val]; rfl
  · rw [wS_val, wp_val (by rw [hW]; omega)]
  · rw [cS_val, hW]

/-- A work port outside `[2, 2 + NI)` is not an `init` port. -/
theorem not_init (x : Fin (2 + rowsWork NI)) (h : ¬ (2 ≤ x.val ∧ x.val < 2 + NI)) : ∀ i, x ≠ initPort NI i :=
  fun i e => h (by
    have h1 := congrArg Fin.val e
    rw [RowsInit.ThrLoop.init_val] at h1
    have h2 := i.isLt
    exact ⟨by omega, by omega⟩)

/-- A non-`init` work port lies outside `[2, 2 + NI)`. -/
theorem init_not (x : Fin (2 + rowsWork NI)) (hx : ∀ i, x ≠ initPort NI i) : ¬ (2 ≤ x.val ∧ x.val < 2 + NI) :=
  fun ⟨h1, h2⟩ => hx ⟨x.val - 2, by omega⟩ (Fin.ext (by rw [RowsInit.ThrLoop.init_val]; simp only; omega))

theorem pub0_ni : ∀ i, pubPort NI 0 ≠ initPort NI i := not_init NI _ (by rw [RowsInit.ThrLoop.pub_val]; simp)
theorem pub1_ni : ∀ i, pubPort NI 1 ≠ initPort NI i := not_init NI _ (by rw [RowsInit.ThrLoop.pub_val]; simp)
theorem rowp_ni (j : Fin 8) : ∀ i, rowpPort NI j ≠ initPort NI i := not_init NI _ (by rw [rowpPort_val]; omega)

end Maps

/-! ## 4. The work phase, docked -/

theorem meta_eq (w deg C : ℕ) (caps : RowCaps) :
    rowMetadataWord w deg C caps =
      frame (RowsInit.metaWord w deg C caps.headerFuel caps.copyCap caps.descriptorReserve caps.rawReserve) := rfl

section Work
variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (NI : ℕ)

theorem work_in (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (k : Fin (2 + rowsWork NI)) :
    rowPublicInput selector a printer (rowsWork NI) r layout caps (wS printer NI k) =
      WorkPhase.workIn NI (frame (r.input a)) (rowMetadataWord layout.w layout.degree layout.C caps) k := by
  have hv := wS_val printer NI k
  unfold rowPublicInput WorkPhase.workIn
  rw [if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega)]
  have rq : (rowRequestPort printer (rowsWork NI)).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) := rfl
  have rc : (rowCapsPort printer (rowsWork NI)).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + 1 := rfl
  by_cases k0 : k.val = 0
  · rw [if_pos (Fin.ext (by rw [hv, rq, k0]; rfl)), if_pos k0]
  · have n0 : wS printer NI k ≠ rowRequestPort printer (rowsWork NI) := fun h => k0 (by
      have := congrArg Fin.val h; rw [hv, rq] at this; omega)
    rw [if_neg n0, if_neg k0]
    by_cases k1 : k.val = 1
    · rw [if_pos (Fin.ext (by rw [hv, rc, k1])), if_pos k1]
    · have n1 : wS printer NI k ≠ rowCapsPort printer (rowsWork NI) := fun h => k1 (by
        have := congrArg Fin.val h; rw [hv, rc] at this; omega)
      rw [if_neg n1, if_neg k1]

theorem work_dock (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    {s : ℕ} {M : Machine (2 + rowsWork NI) s} {c : ℕ} {B : Fin (2 + rowsWork NI) → List Bool}
    (hs : Step M c (fun _ => 0) (WorkPhase.workIn NI (frame (r.input a))
      (rowMetadataWord layout.w layout.degree layout.C caps)) (fun _ => 0) B) :
    Step (RecoveryFocus.machine (wS printer NI) M) c (fun _ => 0) (rowPublicInput selector a printer (rowsWork NI) r layout caps)
      (fun _ => 0) (install (wS printer NI) (rowPublicInput selector a printer (rowsWork NI) r layout caps) B) :=
  RowsInit.VecDock.run_dock hs (wS printer NI) (wS_inj printer NI) (fun _ => 0) _ (fun _ => rfl)
    (fun k => work_in selector a printer NI r layout caps k)

end Work

/-! ## 5. The Frame writer (verified `RowsInit.frame_backing`) -/

section Frame
variable (printer : WilliamsAlgorithm) (NI iDL : ℕ) (hI : iDL < NI)

def drvG : Fin (rowTapes printer (rowsWork NI) + 1) := wS printer NI (rowpPort NI 0)
def lgG : Fin (rowTapes printer (rowsWork NI) + 1) := wS printer NI (rowpPort NI 1)
def dRG : Fin (rowTapes printer (rowsWork NI) + 1) := wS printer NI (rcpPort NI 40)
def dlogG : Fin (rowTapes printer (rowsWork NI) + 1) := wS printer NI (initPort NI ⟨iDL, hI⟩)

/-- The Frame writer's machine (exactly `frame_backing`'s). -/
def frameM := Composition.machine
  (RecoveryFocus.machine (RowsInit.eraseAll (fS printer NI ∘ RowsInit.pcPorts (P1TopDownPaidPayload.tapes printer))
    (drvG printer NI) (lgG printer NI)) (RecoveryScratchErase.resetMachine (P1TopDownPaidPayload.tapes printer + 1)))
  (RecoveryFocus.machine (RowsInit.eraseAll (fun _ : Fin 1 => fS printer NI ((0 : Fin 2).natAdd
    (P1TopDownPaidPayload.tapes printer))) (dRG printer NI) (dlogG printer NI iDL hI)) (RecoveryScratchErase.resetMachine 1))

theorem vals :
    (drvG printer NI).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + NI) ∧
    (lgG printer NI).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + NI + 1) ∧
    (dRG printer NI).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + NI + 8 + 40) ∧
    (dlogG printer NI iDL hI).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + iDL) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [drvG, wS_val, rowpPort_val]; rfl
  · rw [lgG, wS_val, rowpPort_val]; rfl
  · rw [dRG, wS_val, RowsInit.Prefix.rcp_val]; rfl
  · rw [dlogG, wS_val, RowsInit.ThrLoop.init_val]

/-- **The Frame block of row 0.** -/
theorem frame_stage (cC dR : ℕ) (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool)
    (hA : ∀ k, A (fS printer NI k) = []) (hd : A (drvG printer NI) = List.replicate cC true)
    (hl : A (lgG printer NI) = List.replicate (cC + 1) false) (hr : A (dRG printer NI) = List.replicate dR true)
    (hlog : A (dlogG printer NI iDL hI) = []) :
    ∃ A', Step (frameM printer NI iDL hI) (2 * cC + 4 + 1 + (2 * dR + 4)) (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ k, A' (fS printer NI k) = if k.val = P1TopDownPaidPayload.tapes printer then List.replicate dR false
        else List.replicate cC false) ∧
      A' (dlogG printer NI iDL hI) = List.replicate (dR + 1) false ∧
      (∀ x, (∀ k, fS printer NI k ≠ x) → x ≠ dlogG printer NI iDL hI → A' x = A x) := by
  obtain ⟨v1, v2, v3, v4⟩ := vals printer NI iDL hI
  have hf : ∀ k, (fS printer NI k).val < 440 + (P1TopDownPaidPayload.tapes printer + 2) := fun k => by
    rw [fS_val]; have := k.isLt; omega
  have ne : ∀ (x : Fin (rowTapes printer (rowsWork NI) + 1)) (k : Fin (P1TopDownPaidPayload.tapes printer + 2)),
      440 + (P1TopDownPaidPayload.tapes printer + 2) ≤ x.val → fS printer NI k ≠ x := fun x k hx h => by
    have := hf k; rw [h] at this; omega
  have i1 := RowsInit.eraseAll_injective (fS printer NI ∘ RowsInit.pcPorts (P1TopDownPaidPayload.tapes printer))
    (drvG printer NI) (lgG printer NI) ((fS_inj printer NI).comp (RowsInit.pcPorts_injective _))
    (fun i => ne _ _ (by rw [v1]; omega)) (fun i => ne _ _ (by rw [v2]; omega))
    (fun h => by have := congrArg Fin.val h; rw [v1, v2] at this; omega)
  have i2 := RowsInit.eraseAll_injective (fun _ : Fin 1 => fS printer NI ((0 : Fin 2).natAdd
    (P1TopDownPaidPayload.tapes printer))) (dRG printer NI) (dlogG printer NI iDL hI)
    (fun x y _ => Subsingleton.elim x y) (fun i => ne _ _ (by rw [v3]; omega)) (fun i => ne _ _ (by rw [v4]; omega))
    (fun h => by have := congrArg Fin.val h; rw [v3, v4] at this; omega)
  exact RowsInit.frame_backing (fS printer NI) (drvG printer NI) (lgG printer NI) (dRG printer NI)
    (dlogG printer NI iDL hI) i1 i2 (fS_inj printer NI) (fun k => ne _ _ (by rw [v4]; omega))
    (fun k => ne _ _ (by rw [v2]; omega)) (fun k => ne _ _ (by rw [v3]; omega))
    (fun h => by have := congrArg Fin.val h; rw [v4, v2] at this; omega)
    (fun h => by have := congrArg Fin.val h; rw [v3, v2] at this; omega)
    cC dR (fun _ => 0) A (fun _ => rfl) (fun _ => rfl) hA hd hl hr hlog

end Frame

/-! ## 6. The family counter (verified `FamilyWord.word_run`), docked -/

section Counter
variable (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (NI oCt : ℕ)

abbrev ctrS := RowsInit.Prefix.rowsS a
abbrev eC := (ctrS a).extra

/-- The counter's local port `j` as a global value: request (0), the word tape (`cS`), else `init (oCt + j)`. -/
def scv (j : ℕ) : ℕ :=
  if j = 0 then wv printer 0 else if j = 2 + eC a + 2 then 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + (NI + 610))
  else wv printer (2 + oCt + j)

def sc (j : Fin (2 + eC a + 1 + 3)) : Fin (rowTapes printer (rowsWork NI) + 1) := gp printer NI (scv a printer NI oCt j.val)

variable (hC : oCt + eC a + 6 ≤ NI)
include hC

theorem scv_lt (j : ℕ) (hj : j < 2 + eC a + 1 + 3) : scv a printer NI oCt j < rowTapes printer (rowsWork NI) + 1 := by
  rw [T_eq]; unfold scv wv; split_ifs <;> omega

theorem sc_val (j : Fin (2 + eC a + 1 + 3)) : (sc a printer NI oCt j).val = scv a printer NI oCt j.val :=
  gp_val printer NI (scv_lt a printer NI oCt hC j.val j.isLt)

theorem sc_inj : Function.Injective (sc a printer NI oCt) := fun x y h => Fin.ext (by
  have hv := congrArg Fin.val h
  rw [sc_val a printer NI oCt hC, sc_val a printer NI oCt hC] at hv
  have hx := x.isLt
  have hy := y.isLt
  simp only [scv, wv] at hv
  split_ifs at hv <;> omega)

theorem sc_word : sc a printer NI oCt (FamilyWord.wordPort (ctrS a)) = cS printer NI :=
  Fin.ext (by rw [sc_val a printer NI oCt hC, cS_val]; simp [scv, FamilyWord.wordPort, rw_eq])

theorem sc_zero : sc a printer NI oCt ⟨0, by omega⟩ = wS printer NI (pubPort NI 0) :=
  Fin.ext (by rw [sc_val a printer NI oCt hC, wS_val]; simp [scv, wv, RowsInit.ThrLoop.pub_val])

/-- The counter's exit heads, globally: `1` on `cS`, `0` elsewhere. -/
theorem ctr_heads (x : Fin (rowTapes printer (rowsWork NI) + 1)) :
    dockH (sc a printer NI oCt) (fun _ => 0) (FamilyWord.wordH (ctrS a)) x = if x = cS printer NI then 1 else 0 := by
  classical
  by_cases hx : ∃ j, sc a printer NI oCt j = x
  · obtain ⟨j, rfl⟩ := hx
    rw [dockH_slot _ (sc_inj a printer NI oCt hC)]
    unfold FamilyWord.wordH
    by_cases hj : j = FamilyWord.wordPort (ctrS a)
    · subst hj; rw [if_pos rfl, sc_word a printer NI oCt hC, if_pos rfl]
    · rw [if_neg hj, if_neg (fun h => hj ((sc_inj a printer NI oCt hC) (h.trans (sc_word a printer NI oCt hC).symm)))]
  · simp only [not_exists] at hx
    rw [dockH_other _ _ _ _ hx, if_neg (fun h => hx _ ((sc_word a printer NI oCt hC).trans h.symm))]

/-- **The family counter** on the global bank (the request on `pub 0`, the word tape and the scratch blank; heads `0`). -/
theorem ctr_stage (r : Request) (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool)
    (h0 : A (wS printer NI (pubPort NI 0)) = frame (r.input a)) (hc : A (cS printer NI) = [])
    (hs : ∀ x : Fin (rowTapes printer (rowsWork NI) + 1), wv printer (2 + oCt) ≤ x.val →
      x.val < wv printer (2 + oCt + eC a + 6) → A x = []) :
    ∃ Aout : Fin (2 + eC a + 1 + 3) → List Bool,
      Step (RecoveryFocus.machine (sc a printer NI oCt) (FamilyWord.wordMachine (ctrS a)))
        (FamilyWord.wordCost (ctrS a) r) (fun _ => 0) A (fun x => if x = cS printer NI then 1 else 0)
        (install (sc a printer NI oCt) A Aout) ∧
      Aout ⟨0, by omega⟩ = frame (r.input a) ∧
      Aout (FamilyWord.wordPort (ctrS a)) = RepairSource.VerifierDecoding.CompareMachine.word (r.family a).rows.length := by
  obtain ⟨Aout, hs', a0, aw⟩ := FamilyWord.word_run (ctrS a) r
  refine ⟨Aout, ?_, a0, aw⟩
  have d := hs'.dock (sc a printer NI oCt) (sc_inj a printer NI oCt hC) (fun _ => 0) A (fun _ => rfl) (by
    intro j
    by_cases j0 : j.val = 0
    · rw [show j = ⟨0, by omega⟩ from Fin.ext j0, sc_zero a printer NI oCt hC, h0,
        show (⟨0, by omega⟩ : Fin (2 + eC a + 1 + 3)) = FamilyWord.sA (ctrS a) ⟨0, by omega⟩ from Fin.ext rfl,
        FamilyWord.wordIn_sA,
        show (⟨0, by omega⟩ : Fin (2 + eC a + 1)) = Fin.castAdd 1 (⟨0, by omega⟩ : Fin (2 + eC a)) from Fin.ext rfl,
        Fin.addCases_left]
      rfl
    by_cases jw : j = FamilyWord.wordPort (ctrS a)
    · rw [jw, sc_word a printer NI oCt hC, hc, FamilyWord.wordIn_hi _ _ _ (by simp [FamilyWord.wordPort])]
    · have hv := sc_val a printer NI oCt hC j
      have hjw : j.val ≠ 2 + eC a + 2 := fun h => jw (Fin.ext h)
      unfold scv at hv
      rw [if_neg j0, if_neg hjw] at hv
      have hl := j.isLt
      have hE : eC a = (ctrS a).extra := rfl
      have hw := FamilyWord.wordPort (ctrS a)
      rw [hs _ (by rw [hv]; simp only [wv]; omega) (by rw [hv]; simp only [wv]; omega)]
      by_cases hhi : 2 + eC a + 1 ≤ j.val
      · rw [FamilyWord.wordIn_hi _ _ _ hhi]
      · have hj' : j.val < 2 + eC a + 1 := by omega
        rw [show j = FamilyWord.sA (ctrS a) ⟨j.val, hj'⟩ from Fin.ext rfl, FamilyWord.wordIn_sA]
        by_cases hj2 : j.val < 2 + eC a
        · rw [show (⟨j.val, hj'⟩ : Fin (2 + eC a + 1)) = Fin.castAdd 1 (⟨j.val, hj2⟩ : Fin (2 + eC a)) from Fin.ext rfl,
            Fin.addCases_left]
          simp [inBank, j0]
        · rw [show (⟨j.val, hj'⟩ : Fin (2 + eC a + 1)) = Fin.natAdd (2 + eC a) (0 : Fin 1) from
            Fin.ext (by simp only [Fin.val_natAdd, Fin.val_zero]; omega), Fin.addCases_right])
  exact d.congr (funext (ctr_heads a printer NI oCt hC)) rfl

/-- The counter's install moves nothing but `pub 0` (handed back), the word tape and its `init` scratch. -/
theorem sc_other (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) (Aout : Fin (2 + eC a + 1 + 3) → List Bool)
    (x : Fin (rowTapes printer (rowsWork NI) + 1)) (h0 : x.val ≠ wv printer 0) (hc : x.val ≠ (cS printer NI).val)
    (hr : ¬ (wv printer (2 + oCt) ≤ x.val ∧ x.val < wv printer (2 + oCt + eC a + 6))) :
    install (sc a printer NI oCt) A Aout x = A x := by
  refine install_other _ _ _ _ (fun j hj => ?_)
  have hv := congrArg Fin.val hj
  rw [sc_val a printer NI oCt hC] at hv
  have hl := j.isLt
  rw [cS_val] at hc
  have hW := rw_eq NI
  simp only [scv, wv] at hv h0 hr
  split_ifs at hv <;> omega

/-- The counter's install leaves every non-`init` work port as it was. -/
theorem sc_work (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) (Aout : Fin (2 + eC a + 1 + 3) → List Bool)
    (ha : Aout ⟨0, by omega⟩ = A (wS printer NI (pubPort NI 0)))
    (x : Fin (2 + rowsWork NI)) (hx : ∀ i, x ≠ initPort NI i) :
    install (sc a printer NI oCt) A Aout (wS printer NI x) = A (wS printer NI x) := by
  have hv := wS_val printer NI x
  have hni := init_not NI x hx
  have hxl : x.val < 2 + (NI + 610) := rw_eq NI ▸ x.isLt
  by_cases e0 : x.val = 0
  · have ex : wS printer NI x = sc a printer NI oCt ⟨0, by omega⟩ := by
      rw [sc_zero a printer NI oCt hC]; exact congrArg _ (Fin.ext e0)
    rw [ex, install_slot _ (sc_inj a printer NI oCt hC), ha, sc_zero a printer NI oCt hC]
  · have hc : (wS printer NI x).val ≠ (cS printer NI).val := by rw [hv, cS_val]; have := rw_eq NI; omega
    have hr : ¬ (wv printer (2 + oCt) ≤ (wS printer NI x).val ∧
        (wS printer NI x).val < wv printer (2 + oCt + eC a + 6)) := by
      rw [hv]; simp only [wv]; omega
    exact sc_other a printer NI oCt hC A Aout _ (by rw [hv]; simp only [wv]; omega) hc hr

end Counter

/-! ## 7. The Header writer (typed `HdrSpec`) and the empty-family bump, docked -/

section Hdr
variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (NI oH : ℕ)
  (H : RowsInit.Hdr.HdrSpec selector a printer)

/-- The Header writer's local port `i` as a global value. -/
def shv (i : ℕ) : ℕ :=
  if i < 440 then i else if i = 440 then wv printer 0 else if i = 441 then wv printer 1
  else if i = 442 then wv printer (2 + NI + 6) else if i = 443 then wv printer (2 + NI + 7)
  else wv printer (2 + oH + (i - 444))

def sh (i : Fin (440 + 4 + H.needH)) : Fin (rowTapes printer (rowsWork NI) + 1) := gp printer NI (shv printer NI oH i.val)

/-- The global head vector after the counter: `1` on the word tape. -/
def hC1 (x : Fin (rowTapes printer (rowsWork NI) + 1)) : ℕ := if x = cS printer NI then 1 else 0
/-- The final global head vector: `1` on the word tape and on Header 277. -/
def hFin (x : Fin (rowTapes printer (rowsWork NI) + 1)) : ℕ :=
  if x = cS printer NI ∨ x = hS printer NI 277 then 1 else 0

variable (hH : oH + H.needH ≤ NI)
include hH

theorem shv_lt (i : ℕ) (hi : i < 440 + 4 + H.needH) : shv printer NI oH i < rowTapes printer (rowsWork NI) + 1 := by
  rw [T_eq]; unfold shv wv; split_ifs <;> omega

theorem sh_val (i : Fin (440 + 4 + H.needH)) : (sh selector a printer NI oH H i).val = shv printer NI oH i.val :=
  gp_val printer NI (shv_lt selector a printer NI oH H hH i.val i.isLt)

theorem sh_inj : Function.Injective (sh selector a printer NI oH H) := fun x y h => Fin.ext (by
  have hv := congrArg Fin.val h
  rw [sh_val selector a printer NI oH H hH, sh_val selector a printer NI oH H hH] at hv
  have hx := x.isLt
  have hy := y.isLt
  simp only [shv, wv] at hv
  split_ifs at hv <;> omega)

theorem sh_ne_c (i : Fin (440 + 4 + H.needH)) : sh selector a printer NI oH H i ≠ cS printer NI := fun h => by
  have hv := congrArg Fin.val h
  rw [sh_val selector a printer NI oH H hH] at hv
  have h2 := hv.trans (cS_val printer NI)
  have hi := i.isLt
  have hW := rw_eq NI
  simp only [shv, wv] at h2
  split_ifs at h2 <;> omega

theorem sh_hdr (k : Fin 440) : sh selector a printer NI oH H ⟨k.val, by omega⟩ = hS printer NI k :=
  Fin.ext (by rw [sh_val selector a printer NI oH H hH, hS_val]; simp [shv])

theorem hdr_heads (x : Fin (rowTapes printer (rowsWork NI) + 1)) :
    dockH (sh selector a printer NI oH H) (hC1 printer NI) (RowsInit.Hdr.hdrOutH H.needH) x = hFin printer NI x := by
  classical
  unfold hFin
  by_cases hx : ∃ j, sh selector a printer NI oH H j = x
  · obtain ⟨j, rfl⟩ := hx
    rw [dockH_slot _ (sh_inj selector a printer NI oH H hH)]
    unfold RowsInit.Hdr.hdrOutH
    have hj := j.isLt
    have hv := sh_val selector a printer NI oH H hH j
    have hne := sh_ne_c selector a printer NI oH H hH j
    by_cases h277 : j.val = 277
    · rw [if_pos h277, if_pos (Or.inr (by rw [← sh_hdr selector a printer NI oH H hH 277]; exact congrArg _ (Fin.ext h277)))]
    · rw [if_neg h277, if_neg (fun h => by
        rcases h with h | h
        · exact hne h
        · have := congrArg Fin.val h
          rw [hv, hS_val] at this
          simp only [shv, wv] at this
          split_ifs at this <;> omega)]
  · simp only [not_exists] at hx
    rw [dockH_other _ _ _ _ hx]
    unfold hC1
    by_cases hc : x = cS printer NI
    · rw [if_pos hc, if_pos (Or.inl hc)]
    · rw [if_neg hc, if_neg (fun h => by
        rcases h with h | h
        · exact hc h
        · exact hx ⟨277, by omega⟩ ((sh_hdr selector a printer NI oH H hH 277).trans h.symm))]

/-- **The Header writer, docked** (nonempty family, `Good` caps). -/
theorem hdr_stage (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps)
    (good : RowCaps.Good selector a printer r layout facts caps) (hne : (r.family a).rows ≠ [])
    (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool)
    (hh : ∀ k : Fin 440, A (hS printer NI k) = if k.val = 0 then exactListWord (Packets.pool a (r.family a)
      (geometryOf selector a r)) else if k.val = 262 then r.raw selector a else [])
    (h0 : A (wS printer NI (pubPort NI 0)) = frame (r.input a))
    (h1 : A (wS printer NI (pubPort NI 1)) = rowMetadataWord layout.w layout.degree layout.C caps)
    (h6 : A (wS printer NI (rowpPort NI 6)) = List.replicate (2 * caps.headerFuel) true)
    (h7 : A (wS printer NI (rowpPort NI 7)) = List.replicate (2 * caps.headerFuel + 1) false)
    (hs : ∀ x : Fin (rowTapes printer (rowsWork NI) + 1), wv printer (2 + oH) ≤ x.val →
      x.val < wv printer (2 + oH + H.needH) → A x = []) :
    ∃ A' : Fin (440 + 4 + H.needH) → List Bool,
      Step (RecoveryFocus.machine (sh selector a printer NI oH H) H.machine) (H.cost r layout caps) (hC1 printer NI) A
        (hFin printer NI) (install (sh selector a printer NI oH H) A A') ∧
      (∀ k : Fin 440, A' ⟨k.val, by omega⟩ = ZeroPadding.pad (RowsConstruction.PartsStep.reserveOf caps k)
        (PCJ45bee56da9f34d5a_RowState.commonHeader a (r.family a) (geometryOf selector a r) layout k)) ∧
      A' ⟨440, by omega⟩ = frame (r.input a) ∧
      A' ⟨441, by omega⟩ = rowMetadataWord layout.w layout.degree layout.C caps ∧
      A' ⟨442, by omega⟩ = List.replicate (2 * caps.headerFuel) true ∧
      A' ⟨443, by omega⟩ = List.replicate (2 * caps.headerFuel + 1) false := by
  obtain ⟨A', hs', hk, a0, a1, a2, a3⟩ := H.run r layout facts caps good hne
  refine ⟨A', ?_, hk, a0, a1, a2, a3⟩
  have d := hs'.dock (sh selector a printer NI oH H) (sh_inj selector a printer NI oH H hH) (hC1 printer NI) A
    (fun j => by unfold hC1; rw [if_neg (sh_ne_c selector a printer NI oH H hH j)]) (by
      intro j
      have hj := j.isLt
      have hv := sh_val selector a printer NI oH H hH j
      unfold RowsInit.Hdr.hdrIn
      by_cases h440 : j.val < 440
      · rw [show j = ⟨(⟨j.val, h440⟩ : Fin 440).val, by omega⟩ from Fin.ext rfl, sh_hdr selector a printer NI oH H hH, hh]
        simp only
        by_cases e0 : j.val = 0
        · rw [if_pos e0, if_pos e0]
        · rw [if_neg e0, if_neg e0]
          by_cases e2 : j.val = 262
          · rw [if_pos e2, if_pos e2]
          · rw [if_neg e2, if_neg e2, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg (by omega), if_neg (by omega)]
        simp only [shv, if_neg h440] at hv
        by_cases e440 : j.val = 440
        · rw [if_pos e440, show sh selector a printer NI oH H j = wS printer NI (pubPort NI 0) from
            Fin.ext (by rw [hv, if_pos e440, wS_val]; rfl), h0]
        rw [if_neg e440] at hv ⊢
        by_cases e441 : j.val = 441
        · rw [if_pos e441, show sh selector a printer NI oH H j = wS printer NI (pubPort NI 1) from
            Fin.ext (by rw [hv, if_pos e441, wS_val]; rfl), h1]
        rw [if_neg e441] at hv ⊢
        by_cases e442 : j.val = 442
        · rw [if_pos e442, show sh selector a printer NI oH H j = wS printer NI (rowpPort NI 6) from
            Fin.ext (by rw [hv, if_pos e442, wS_val, rowpPort_val]; rfl), h6]
        rw [if_neg e442] at hv ⊢
        by_cases e443 : j.val = 443
        · rw [if_pos e443, show sh selector a printer NI oH H j = wS printer NI (rowpPort NI 7) from
            Fin.ext (by rw [hv, if_pos e443, wS_val, rowpPort_val]; rfl), h7]
        rw [if_neg e443] at hv ⊢
        exact hs _ (by rw [hv]; simp only [wv]; omega) (by rw [hv]; simp only [wv]; omega))
  exact d.congr (funext (hdr_heads selector a printer NI oH H hH)) rfl

/-- The Header writer's install moves nothing but the Header block, its four read-back ports and its scratch. -/
theorem sh_other (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) (A' : Fin (440 + 4 + H.needH) → List Bool)
    (x : Fin (rowTapes printer (rowsWork NI) + 1)) (hx : 440 ≤ x.val) (h0 : x.val ≠ wv printer 0)
    (h1 : x.val ≠ wv printer 1) (h6 : x.val ≠ wv printer (2 + NI + 6)) (h7 : x.val ≠ wv printer (2 + NI + 7))
    (hr : ¬ (wv printer (2 + oH) ≤ x.val ∧ x.val < wv printer (2 + oH + H.needH))) :
    install (sh selector a printer NI oH H) A A' x = A x := by
  refine install_other _ _ _ _ (fun j hj => ?_)
  have hv := congrArg Fin.val hj
  rw [sh_val selector a printer NI oH H hH] at hv
  have hl := j.isLt
  simp only [shv, wv] at hv h0 h1 h6 h7 hr
  split_ifs at hv <;> omega

/-- The Header writer's install leaves every non-`init` work port as it was (the four read-back words handed back). -/
theorem sh_work (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) (A' : Fin (440 + 4 + H.needH) → List Bool)
    (a0 : A' ⟨440, by omega⟩ = A (wS printer NI (pubPort NI 0)))
    (a1 : A' ⟨441, by omega⟩ = A (wS printer NI (pubPort NI 1)))
    (a6 : A' ⟨442, by omega⟩ = A (wS printer NI (rowpPort NI 6)))
    (a7 : A' ⟨443, by omega⟩ = A (wS printer NI (rowpPort NI 7)))
    (x : Fin (2 + rowsWork NI)) (hx : ∀ i, x ≠ initPort NI i) :
    install (sh selector a printer NI oH H) A A' (wS printer NI x) = A (wS printer NI x) := by
  obtain ⟨u0, u1, u6, u7, -, -⟩ := wvals printer NI
  have hv := wS_val printer NI x
  have hni := init_not NI x hx
  have hxl : x.val < 2 + (NI + 610) := rw_eq NI ▸ x.isLt
  by_cases e0 : x.val = 0
  · have ex : x = pubPort NI 0 := Fin.ext e0
    subst ex
    conv_lhs => rw [show wS printer NI (pubPort NI 0) = sh selector a printer NI oH H ⟨440, by omega⟩ from Fin.ext (by
      rw [u0, sh_val selector a printer NI oH H hH]; simp [shv, wv]), install_slot _ (sh_inj selector a printer NI oH H hH)]
    exact a0
  by_cases e1 : x.val = 1
  · have ex : x = pubPort NI 1 := Fin.ext e1
    subst ex
    conv_lhs => rw [show wS printer NI (pubPort NI 1) = sh selector a printer NI oH H ⟨441, by omega⟩ from Fin.ext (by
      rw [u1, sh_val selector a printer NI oH H hH]; simp [shv, wv]), install_slot _ (sh_inj selector a printer NI oH H hH)]
    exact a1
  by_cases e6 : x.val = 2 + NI + 6
  · have ex : x = rowpPort NI 6 := Fin.ext (by rw [rowpPort_val]; exact e6)
    subst ex
    conv_lhs => rw [show wS printer NI (rowpPort NI 6) = sh selector a printer NI oH H ⟨442, by omega⟩ from Fin.ext (by
      rw [u6, sh_val selector a printer NI oH H hH]; simp [shv, wv]), install_slot _ (sh_inj selector a printer NI oH H hH)]
    exact a6
  by_cases e7 : x.val = 2 + NI + 7
  · have ex : x = rowpPort NI 7 := Fin.ext (by rw [rowpPort_val]; exact e7)
    subst ex
    conv_lhs => rw [show wS printer NI (rowpPort NI 7) = sh selector a printer NI oH H ⟨443, by omega⟩ from Fin.ext (by
      rw [u7, sh_val selector a printer NI oH H hH]; simp [shv, wv]), install_slot _ (sh_inj selector a printer NI oH H hH)]
    exact a7
  have k0 : 440 ≤ (wS printer NI x).val := by rw [hv]; omega
  have k1 : (wS printer NI x).val ≠ wv printer 0 := by rw [hv]; simp only [wv]; omega
  have k2 : (wS printer NI x).val ≠ wv printer 1 := by rw [hv]; simp only [wv]; omega
  have k3 : (wS printer NI x).val ≠ wv printer (2 + NI + 6) := by rw [hv]; simp only [wv]; omega
  have k4 : (wS printer NI x).val ≠ wv printer (2 + NI + 7) := by rw [hv]; simp only [wv]; omega
  have k5 : ¬ (wv printer (2 + oH) ≤ (wS printer NI x).val ∧ (wS printer NI x).val < wv printer (2 + oH + H.needH)) := by
    rw [hv]; simp only [wv]; omega
  exact sh_other selector a printer NI oH H hH A A' _ k0 k1 k2 k3 k4 k5

/-- The Header writer's install leaves the Frame block alone. -/
theorem sh_frm (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) (A' : Fin (440 + 4 + H.needH) → List Bool)
    (k : Fin (P1TopDownPaidPayload.tapes printer + 2)) :
    install (sh selector a printer NI oH H) A A' (fS printer NI k) = A (fS printer NI k) := by
  have hk := k.isLt
  have hv := fS_val printer NI k
  exact sh_other selector a printer NI oH H hH A A' _ (by rw [hv]; omega) (by rw [hv]; simp only [wv]; omega)
    (by rw [hv]; simp only [wv]; omega) (by rw [hv]; simp only [wv]; omega) (by rw [hv]; simp only [wv]; omega)
    (by rw [hv]; simp only [wv]; omega)

/-- The Header writer's install leaves the counter's word tape alone. -/
theorem sh_ctr (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) (A' : Fin (440 + 4 + H.needH) → List Bool) :
    install (sh selector a printer NI oH H) A A' (cS printer NI) = A (cS printer NI) :=
  install_other _ _ _ _ (sh_ne_c selector a printer NI oH H hH)

omit hH in
/-- **The empty-family bump**: Header 277's head `0 → 1`, nothing written. -/
theorem bump_stage (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) :
    Step (RecoveryFocus.machine (fun _ : Fin 1 => hS printer NI 277) RowsInit.bump) 1 (hC1 printer NI) A
      (hFin printer NI) A := by
  have d := (RowsInit.bump_run 0 (A (hS printer NI 277))).dock (fun _ : Fin 1 => hS printer NI 277)
    (fun x y _ => Subsingleton.elim x y) (hC1 printer NI) A
    (fun _ => by unfold hC1; rw [if_neg (fun h => by have := congrArg Fin.val h; rw [hS_val, cS_val] at this; omega)])
    (fun _ => rfl)
  refine d.congr (funext fun x => ?_) (install_existing _ _ _ (fun _ => rfl))
  classical
  unfold hFin
  by_cases hx : x = hS printer NI 277
  · subst hx
    rw [dockH_slot (fun _ : Fin 1 => hS printer NI 277) (fun x y _ => Subsingleton.elim x y) _ _ 0, if_pos (Or.inr rfl)]
  · rw [dockH_other _ _ _ _ (fun _ h => hx h.symm)]
    unfold hC1
    by_cases hc : x = cS printer NI
    · rw [if_pos hc, if_pos (Or.inl hc)]
    · rw [if_neg hc, if_neg (fun h => h.elim hc hx)]

end Hdr

/-! ## 8. The global tail: Frame writer ; counter ; (Header writer | bump) -/

section Tail
variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
  (NI iDL : ℕ) (hI : iDL < NI) (H : RowsInit.Hdr.HdrSpec selector a printer)

def tailM := Composition.machine (Composition.machine (frameM printer NI iDL hI)
    (RecoveryFocus.machine (sc a printer NI (iDL + 1)) (FamilyWord.wordMachine (ctrS a))))
  (CloseoutRowsOriginalSwitch.machine (RecoveryFocus.machine (sh selector a printer NI (iDL + 1 + eC a + 6) H) H.machine)
    (RecoveryFocus.machine (fun _ : Fin 1 => hS printer NI 277) RowsInit.bump) (wS printer NI (wp NI 150)))

def headCost (r : Request) (caps : RowCaps) : ℕ :=
  (2 * caps.copyCap + 4 + 1 + (2 * caps.descriptorReserve + 4)) + 1 + FamilyWord.wordCost (ctrS a) r + 1

/-- The entry facts of the tail (all read from the bank after the work phase). -/
structure TailIn (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) : Prop where
  hdr : ∀ k : Fin 440, A (hS printer NI k) = if k.val = 0 then exactListWord (Packets.pool a (r.family a)
    (geometryOf selector a r)) else if k.val = 262 then r.raw selector a else []
  frm : ∀ k, A (fS printer NI k) = []
  ctr : A (cS printer NI) = []
  p0 : A (wS printer NI (pubPort NI 0)) = frame (r.input a)
  p1 : A (wS printer NI (pubPort NI 1)) = rowMetadataWord layout.w layout.degree layout.C caps
  r0 : A (wS printer NI (rowpPort NI 0)) = List.replicate caps.copyCap true
  r1 : A (wS printer NI (rowpPort NI 1)) = List.replicate (caps.copyCap + 1) false
  r6 : A (wS printer NI (rowpPort NI 6)) = List.replicate (2 * caps.headerFuel) true
  r7 : A (wS printer NI (rowpPort NI 7)) = List.replicate (2 * caps.headerFuel + 1) false
  dR : A (wS printer NI (rcpPort NI 40)) = List.replicate caps.descriptorReserve true
  flag : A (wS printer NI (wp NI 150)) = List.replicate (r.family a).rows.length true
  blank : ∀ x : Fin (rowTapes printer (rowsWork NI) + 1), wv printer (2 + iDL) ≤ x.val →
    x.val < wv printer (2 + (iDL + 1 + eC a + 6) + H.needH) → A x = []

structure TailOut (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (A B : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) : Prop where
  ctr : B (cS printer NI) = RepairSource.VerifierDecoding.CompareMachine.word (r.family a).rows.length
  frm : ∀ k, B (fS printer NI k) = if k.val = P1TopDownPaidPayload.tapes printer then
    List.replicate caps.descriptorReserve false else List.replicate caps.copyCap false
  work : ∀ x : Fin (2 + rowsWork NI), (∀ i, x ≠ initPort NI i) → B (wS printer NI x) = A (wS printer NI x)
  low : ∀ i : Fin NI, i.val < iDL → B (wS printer NI (initPort NI i)) = A (wS printer NI (initPort NI i))

end Tail

section TailRun
variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
  (NI iDL : ℕ) (hI : iDL < NI) (H : RowsInit.Hdr.HdrSpec selector a printer)
  (hR : iDL + 1 + eC a + 6 + H.needH ≤ NI) (hD : 150 ≤ iDL)
include hR hD

/-- **Frame writer ; family counter** on the tail's entry bank. -/
theorem tail_pre (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) (hA : TailIn selector a printer NI iDL H r layout caps A) :
    ∃ A2, Step (Composition.machine (frameM printer NI iDL hI)
        (RecoveryFocus.machine (sc a printer NI (iDL + 1)) (FamilyWord.wordMachine (ctrS a))))
        (2 * caps.copyCap + 4 + 1 + (2 * caps.descriptorReserve + 4) + 1 + FamilyWord.wordCost (ctrS a) r)
        (fun _ => 0) A (hC1 printer NI) A2 ∧
      (∀ k : Fin 440, A2 (hS printer NI k) = A (hS printer NI k)) ∧
      A2 (cS printer NI) = RepairSource.VerifierDecoding.CompareMachine.word (r.family a).rows.length ∧
      (∀ k, A2 (fS printer NI k) = if k.val = P1TopDownPaidPayload.tapes printer then
        List.replicate caps.descriptorReserve false else List.replicate caps.copyCap false) ∧
      (∀ x : Fin (2 + rowsWork NI), (∀ i, x ≠ initPort NI i) → A2 (wS printer NI x) = A (wS printer NI x)) ∧
      A2 (wS printer NI (wp NI 150)) = A (wS printer NI (wp NI 150)) ∧
      (∀ x : Fin (rowTapes printer (rowsWork NI) + 1), wv printer (2 + (iDL + 1 + eC a + 6)) ≤ x.val →
        x.val < wv printer (2 + NI) → A2 x = A x) ∧
      (∀ i : Fin NI, i.val < iDL → A2 (wS printer NI (initPort NI i)) = A (wS printer NI (initPort NI i))) := by
  obtain ⟨u0, -, -, -, u150, uc⟩ := wvals printer NI
  have hP2 : ∀ k : Fin (P1TopDownPaidPayload.tapes printer + 2),
      (fS printer NI k).val < 440 + (P1TopDownPaidPayload.tapes printer + 2) := fun k => by
    rw [fS_val]; have := k.isLt; omega
  obtain ⟨-, -, -, v4⟩ := vals printer NI iDL hI
  have hlog : A (dlogG printer NI iDL hI) = [] := hA.blank _ (by rw [v4]) (by rw [v4]; simp only [wv]; omega)
  obtain ⟨A1, s1, f1, -, fr1⟩ := frame_stage printer NI iDL hI caps.copyCap caps.descriptorReserve A hA.frm hA.r0 hA.r1
    hA.dR hlog
  have a1 : ∀ x : Fin (rowTapes printer (rowsWork NI) + 1), 440 + (P1TopDownPaidPayload.tapes printer + 2) ≤ x.val →
      x.val ≠ 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + iDL) → A1 x = A x := by
    intro x h1 h2
    refine fr1 x (fun k hk => ?_) (fun h => h2 (by rw [h, v4]))
    have := hP2 k; rw [hk] at this; omega
  have hCt : iDL + 1 + eC a + 6 ≤ NI := by omega
  have c0 : A1 (wS printer NI (pubPort NI 0)) = frame (r.input a) := by
    rw [a1 _ (by rw [u0]) (by rw [u0]; omega)]; exact hA.p0
  have cc : A1 (cS printer NI) = [] := by
    rw [a1 _ (by rw [uc]; omega) (by rw [uc]; omega)]; exact hA.ctr
  have cs : ∀ x : Fin (rowTapes printer (rowsWork NI) + 1), wv printer (2 + (iDL + 1)) ≤ x.val →
      x.val < wv printer (2 + (iDL + 1) + eC a + 6) → A1 x = [] := by
    intro x h1 h2
    simp only [wv] at h1 h2
    rw [a1 x (by omega) (by omega)]
    exact hA.blank x (by simp only [wv]; omega) (by simp only [wv]; omega)
  obtain ⟨Aout, s2, ao0, aow⟩ := ctr_stage a printer NI (iDL + 1) hCt r A1 c0 cc cs
  refine ⟨install (sc a printer NI (iDL + 1)) A1 Aout, s1.seq s2, fun k => ?_, ?_, fun k => ?_, fun x hx => ?_, ?_,
    fun x h1 h2 => ?_, fun i hi => ?_⟩
  · have hk := k.isLt
    have hv := hS_val printer NI k
    rw [sc_other a printer NI (iDL + 1) hCt A1 Aout _ (by rw [hv]; simp only [wv]; omega) (by rw [hv, uc]; omega)
      (by rw [hv]; simp only [wv]; omega)]
    exact fr1 _ (fun k' hk' => by have := congrArg Fin.val hk'; rw [fS_val, hv] at this; omega)
      (fun h => by have := congrArg Fin.val h; rw [hv, v4] at this; omega)
  · rw [← sc_word a printer NI (iDL + 1) hCt, install_slot _ (sc_inj a printer NI (iDL + 1) hCt), aow]
  · have hk := hP2 k
    rw [sc_other a printer NI (iDL + 1) hCt A1 Aout _ (by simp only [wv]; omega) (by rw [uc]; omega)
      (by simp only [wv]; omega)]
    exact f1 k
  · have hv := wS_val printer NI x
    have hni := init_not NI x hx
    rw [sc_work a printer NI (iDL + 1) hCt A1 Aout (ao0.trans c0.symm) x hx]
    exact a1 _ (by rw [hv]; omega) (by rw [hv]; omega)
  · rw [sc_other a printer NI (iDL + 1) hCt A1 Aout _ (by rw [u150]; simp only [wv]; omega) (by rw [u150, uc]; omega)
      (by rw [u150]; simp only [wv]; omega)]
    exact a1 _ (by rw [u150]; omega) (by rw [u150]; omega)
  · simp only [wv] at h1 h2
    rw [sc_other a printer NI (iDL + 1) hCt A1 Aout _ (by simp only [wv]; omega) (by rw [uc]; omega)
      (by simp only [wv]; omega)]
    exact a1 _ (by omega) (by omega)
  · have hv : (wS printer NI (initPort NI i)).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + i.val) := by
      rw [wS_val, RowsInit.ThrLoop.init_val]
    have hi' := i.isLt
    rw [sc_other a printer NI (iDL + 1) hCt A1 Aout _ (by rw [hv]; simp only [wv]; omega) (by rw [hv, uc]; omega)
      (by rw [hv]; simp only [wv]; omega)]
    exact a1 _ (by rw [hv]; omega) (by rw [hv]; omega)

/-- **The tail on a nonempty family** (the switch takes the Header writer). -/
theorem tail_ne (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps)
    (good : RowCaps.Good selector a printer r layout facts caps) (hne : (r.family a).rows ≠ [])
    (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) (hA : TailIn selector a printer NI iDL H r layout caps A) :
    ∃ B, Step (tailM selector a printer NI iDL hI H) (headCost a r caps + (H.cost r layout caps + 2)) (fun _ => 0) A
        (hFin printer NI) B ∧
      (∀ k : Fin 440, B (hS printer NI k) = ZeroPadding.pad (RowsConstruction.PartsStep.reserveOf caps k)
        (PCJ45bee56da9f34d5a_RowState.commonHeader a (r.family a) (geometryOf selector a r) layout k)) ∧
      TailOut selector a printer NI iDL r layout caps A B := by
  obtain ⟨-, -, -, -, u150, uc⟩ := wvals printer NI
  obtain ⟨A2, s12, p_h, p_c, p_f, p_w, p_fl, p_s, p_l⟩ := tail_pre selector a printer NI iDL hI H hR hD r layout caps A hA
  have hH' : iDL + 1 + eC a + 6 + H.needH ≤ NI := hR
  have d_hh : ∀ k : Fin 440, A2 (hS printer NI k) = if k.val = 0 then exactListWord (Packets.pool a (r.family a)
      (geometryOf selector a r)) else if k.val = 262 then r.raw selector a else [] := fun k => (p_h k).trans (hA.hdr k)
  have d_h0 := (p_w _ (pub0_ni NI)).trans hA.p0
  have d_h1 := (p_w _ (pub1_ni NI)).trans hA.p1
  have d_h6 := (p_w _ (rowp_ni NI 6)).trans hA.r6
  have d_h7 := (p_w _ (rowp_ni NI 7)).trans hA.r7
  have d_hs : ∀ x : Fin (rowTapes printer (rowsWork NI) + 1), wv printer (2 + (iDL + 1 + eC a + 6)) ≤ x.val →
      x.val < wv printer (2 + (iDL + 1 + eC a + 6) + H.needH) → A2 x = [] := by
    intro x h1 h2
    rw [p_s x h1 (by simp only [wv] at h2 ⊢; omega)]
    exact hA.blank x (by simp only [wv] at h1 ⊢; omega) h2
  obtain ⟨A', s3, hk, a440, a441, a442, a443⟩ := hdr_stage selector a printer NI (iDL + 1 + eC a + 6) H hH' r layout facts
    caps good hne A2 d_hh d_h0 d_h1 d_h6 d_h7 d_hs
  have hflag : readTapeBit (A2 (wS printer NI (wp NI 150))) (hC1 printer NI (wS printer NI (wp NI 150))) = true := by
    have hn : wS printer NI (wp NI 150) ≠ cS printer NI := fun h => by
      have := congrArg Fin.val h; rw [u150, uc] at this; omega
    rw [p_fl, hA.flag]
    unfold hC1
    rw [if_neg hn, cell0_rep]
    simp [List.length_pos_iff.mpr hne]
  have sw := CloseoutRowsOriginalSwitch.true_run (RecoveryFocus.machine (sh selector a printer NI (iDL + 1 + eC a + 6) H)
    H.machine) (RecoveryFocus.machine (fun _ : Fin 1 => hS printer NI 277) RowsInit.bump) (wS printer NI (wp NI 150)) s3
    hflag
  refine ⟨_, (s12.seq sw).enlarge (by unfold headCost; omega), fun k => ?_, ⟨?_, fun k => ?_, fun x hx => ?_, fun i hi => ?_⟩⟩
  · rw [← sh_hdr selector a printer NI _ H hH' k, install_slot _ (sh_inj selector a printer NI _ H hH')]
    exact hk k
  · rw [sh_ctr selector a printer NI _ H hH', p_c]
  · rw [sh_frm selector a printer NI _ H hH', p_f]
  · rw [sh_work selector a printer NI _ H hH' A2 A' (a440.trans d_h0.symm) (a441.trans d_h1.symm)
      (a442.trans d_h6.symm) (a443.trans d_h7.symm) x hx, p_w x hx]
  · have hv : (wS printer NI (initPort NI i)).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + (2 + i.val) := by
      rw [wS_val, RowsInit.ThrLoop.init_val]
    have hi' := i.isLt
    rw [sh_other selector a printer NI _ H hH' A2 A' _ (by rw [hv]; omega) (by rw [hv]; simp only [wv]; omega)
      (by rw [hv]; simp only [wv]; omega) (by rw [hv]; simp only [wv]; omega) (by rw [hv]; simp only [wv]; omega)
      (by rw [hv]; simp only [wv]; omega), p_l i hi]

/-- **The tail on an empty family** (the switch takes the Header-277 bump; the Header block stays the public one, which on an
empty family is `RowState.headerBank`'s empty branch: the pool word on Header 0, every other Header blank). -/
theorem tail_e (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (he : (r.family a).rows = [])
    (A : Fin (rowTapes printer (rowsWork NI) + 1) → List Bool) (hA : TailIn selector a printer NI iDL H r layout caps A) :
    ∃ B, Step (tailM selector a printer NI iDL hI H) (headCost a r caps + (1 + 2)) (fun _ => 0) A (hFin printer NI) B ∧
      (∀ k : Fin 440, B (hS printer NI k) = if k.val = 0 then exactListWord (Packets.pool a (r.family a)
        (geometryOf selector a r)) else []) ∧
      TailOut selector a printer NI iDL r layout caps A B := by
  obtain ⟨-, -, -, -, u150, uc⟩ := wvals printer NI
  obtain ⟨A2, s12, p_h, p_c, p_f, p_w, p_fl, -, p_l⟩ := tail_pre selector a printer NI iDL hI H hR hD r layout caps A hA
  have hflag : readTapeBit (A2 (wS printer NI (wp NI 150))) (hC1 printer NI (wS printer NI (wp NI 150))) = false := by
    have hn : wS printer NI (wp NI 150) ≠ cS printer NI := fun h => by
      have := congrArg Fin.val h; rw [u150, uc] at this; omega
    rw [p_fl, hA.flag, he]
    unfold hC1
    rw [if_neg hn, cell0_rep]
    simp
  have sw := CloseoutRowsOriginalSwitch.false_run (RecoveryFocus.machine (sh selector a printer NI (iDL + 1 + eC a + 6) H)
    H.machine) (RecoveryFocus.machine (fun _ : Fin 1 => hS printer NI 277) RowsInit.bump) (wS printer NI (wp NI 150))
    (bump_stage printer NI A2) hflag
  have hraw : r.raw selector a = [] := by simp [Request.raw, he]
  refine ⟨A2, (s12.seq sw).enlarge (by unfold headCost; omega), fun k => ?_, ⟨p_c, p_f, p_w, p_l⟩⟩
  rw [p_h k, hA.hdr k, hraw]
  by_cases h0 : k.val = 0 <;> simp [h0]

end TailRun

end
end RowsInit.Global
