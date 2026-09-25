import Proof.Rows.RowsKeyZeroThr

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.KeyZeroMode
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch
open RowsConstruction.BaseLayout RowsConstruction.KeyStep
open RowsConstruction.KeyZero (symK0 symK0Cost symBlank0 sym_key0_run)
open RowsConstruction.KeyZeroThr (thrK0 thrK0Cost thrBlank0 thrZInit thr_key0_run)
noncomputable section

section Ports
variable (NI : Nat)

/-- **The key-0 writer for both modes** (one fixed machine for fixed `NI` and `init` placements). -/
def k0 (iMode : Fin NI) (iz : Fin 9 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (iniS : Fin 9 → Fin NI) :=
  CloseoutRowsOriginalSwitch.machine (thrK0 NI iz ib iOne) (symK0 NI iniS) (initPort NI iMode)

theorem thrBlank0_init (B : Fin (2+rowsWork NI) → List Bool) (i : Fin NI) :
    thrBlank0 NI B (initPort NI i) = B (initPort NI i) := by
  unfold thrBlank0
  simp only [Function.update_of_ne (RowsConstruction.ThrKey.initPort_ne_master NI i _)]

theorem symBlank0_init (B : Fin (2+rowsWork NI) → List Bool) (i : Fin NI) :
    symBlank0 NI B (initPort NI i) = B (initPort NI i) := by
  unfold symBlank0
  simp only [Function.update_of_ne (RowsConstruction.ThrKey.initPort_ne_master NI i _)]

def keyBlank (K : Finset (Fin 254)) (B : Fin (2+rowsWork NI) → List Bool) : Fin (2+rowsWork NI) → List Bool :=
  fun p => if p ∈ K.image (masterPort NI) then [] else B p

/-- `thrBlank0` is RX's `blankKeys` at the THR key set. -/
theorem thrBlank0_eq (B : Fin (2+rowsWork NI) → List Bool) : thrBlank0 NI B = keyBlank NI thrKeySet B := by
  funext p
  unfold thrBlank0 keyBlank
  by_cases hp : p ∈ thrKeySet.image (masterPort NI)
  · rw [if_pos hp]
    simp only [Finset.mem_image, thrKeySet, Finset.mem_insert, Finset.mem_singleton] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ThrSelCasc.masterPort_inj]
  · rw [if_neg hp]
    have hne : ∀ k ∈ thrKeySet, p ≠ masterPort NI k := fun k hk e => hp (Finset.mem_image.mpr ⟨k, hk, e.symm⟩)
    simp only [thrKeySet, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at hne
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hne
    simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10]

/-- `symBlank0` is RX's `blankKeys` at the SYM key set. -/
theorem symBlank0_eq (B : Fin (2+rowsWork NI) → List Bool) : symBlank0 NI B = keyBlank NI symKeySet B := by
  funext p
  unfold symBlank0 keyBlank
  by_cases hp : p ∈ symKeySet.image (masterPort NI)
  · rw [if_pos hp]
    simp only [Finset.mem_image, symKeySet, Finset.mem_insert, Finset.mem_singleton] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rcases hk with rfl | rfl | rfl | rfl <;>
      simp [ThrSelCasc.masterPort_inj, SymC5.tgtP]
  · rw [if_neg hp]
    have hne : ∀ k ∈ symKeySet, p ≠ masterPort NI k := fun k hk e => hp (Finset.mem_image.mpr ⟨k, hk, e.symm⟩)
    simp only [symKeySet, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at hne
    obtain ⟨n1, n2, n3, n4⟩ := hne
    have e0 : SymC5.tgtP 0 = 140 := rfl
    have e1 : SymC5.tgtP 1 = 141 := rfl
    have e2 : SymC5.tgtP 2 = 142 := rfl
    have e3 : SymC5.tgtP 3 = 143 := rfl
    simp [e0, e1, e2, e3, n1, n2, n3, n4]

end Ports

/-! ## 1. Each mode -/

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

/-- **THR request**: the flag `[true]` selects the THR writer. -/
theorem thr_k0 (iMode : Fin NI) (hmode : init iMode = [true]) (iz : Fin 9 → Fin NI) (hiz : Function.Injective iz)
    (hz : ∀ m, init (iz m) = thrZInit (KeyTop.wT a r four L target) (ThrWidth.T a r four L target)
      (Ff r.q (ThrWidth.T a r four L target)) (Uf r.q (ThrWidth.T a r four L target)) m)
    (ib : Fin 82 → Fin NI) (iOne : Fin NI) (hib : Function.Injective ib) (hone : ib 9 ≠ iOne)
    (hinitB : ∀ k : Fin 82, ¬ (73 ≤ k.val ∧ k.val < 77) → init (ib k) = ThrSelBase.baseInit a r four L target k)
    (hinitO : init iOne = ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target))
      (fb (KeyTop.wT a r four L target) 1))
    (iniS : Fin 9 → Fin NI) (h0 : 0 < (RCFive.RowKeys.thrKeys a r L target).length) :
    Step (k0 NI iMode iz ib iOne iniS)
      (thrK0Cost (KeyTop.wT a r four L target) (ThrWidth.T a r four L target) (Ff r.q (ThrWidth.T a r four L target))
        (Uf r.q (ThrWidth.T a r four L target))
        (ThrSelBase.baseCost (ThrSelBase.bF (ThrWidth.T a r four L target)) (KeyTop.wT a r four L target)) + 2)
      (fun _ => 0) (thrBlank0 NI (thrBase a r four L target NI pub init rcp C cC hF 0))
      (fun _ => 0) (thrBase a r four L target NI pub init rcp C cC hF 0) :=
  CloseoutRowsOriginalSwitch.true_run _ _ _
    (thr_key0_run a r four L target NI pub init rcp C cC hF iz hiz hz ib iOne hib hone hinitB hinitO h0)
    (by rw [thrBlank0_init, (thr_base_rc a r four L target NI pub init rcp C cC hF 0).2.1, hmode]; rfl)

end Thr

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

/-- **SYM request**: the flag `[false]` selects the SYM writer. -/
theorem sym_k0 (iMode : Fin NI) (hmode : init iMode = [false]) (iz : Fin 9 → Fin NI) (ib : Fin 82 → Fin NI)
    (iOne : Fin NI) (iniS : Fin 9 → Fin NI)
    (hinitS : ∀ m, init (iniS m) = SymC5.symInit (SymC5.sw a r four L target) r.circuits.length (SymC5.sbnd r) m)
    (h0 : 0 < (RCFive.RowKeys.symKeys r L target).length) :
    Step (k0 NI iMode iz ib iOne iniS)
      (symK0Cost (SymC5.sw a r four L target) (symRes r.q (symT a r four L target)) + 2)
      (fun _ => 0) (symBlank0 NI (symBase a r four L target NI pub init rcp C cC hF 0))
      (fun _ => 0) (symBase a r four L target NI pub init rcp C cC hF 0) :=
  CloseoutRowsOriginalSwitch.false_run _ _ _
    (sym_key0_run a r four L target NI pub init rcp C cC hF iniS hinitS h0)
    (by rw [symBlank0_init, (sym_base_rc a r four L target NI pub init rcp C cC hF 0).2.1, hmode]; rfl)

end Sym

/-! ## 2. Every request at once (`baseOf`) -/

/-- The key-0 writer's cost per request. -/
def k0Cost (a : DecompositionAlgorithm) : PCJd4d1d9d7d1fa4313_Production.Request → Nat
  | .terminal => 0
  | .thr r four L target =>
      thrK0Cost (KeyTop.wT a r four L target) (ThrWidth.T a r four L target) (Ff r.q (ThrWidth.T a r four L target))
        (Uf r.q (ThrWidth.T a r four L target))
        (ThrSelBase.baseCost (ThrSelBase.bF (ThrWidth.T a r four L target)) (KeyTop.wT a r four L target)) + 2
  | .sym r four L target => symK0Cost (SymC5.sw a r four L target) (symRes r.q (symT a r four L target)) + 2

end
end RowsConstruction.KeyZeroMode
