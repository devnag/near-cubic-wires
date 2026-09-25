import Proof.Rows.RowsCompleteWork
import Proof.Rows.RowsSymC5

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CompleteRow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open RowsConstruction.BaseLayout RowsConstruction.ThrCell RowsConstruction.MaskStage RowsConstruction.CompleteWork
noncomputable section

/-- The SYM loop machine. -/
abbrev symLoop := CloseoutRowsDegreeLoop.machine (MaskGeneric.gouterBody SymVerdict.machine SymVerdict.heads0)

section Mach
variable (NI : Nat)

/-- **W1** (one fixed machine): the row's mask, THR or SYM by the resident flag. -/
def W1 (iMode : Fin NI) :=
  CloseoutRowsOriginalSwitch.machine (maskW NI thrLoop) (maskW NI symLoop) (initPort NI iMode)

/-- **W2** (one fixed machine): verdict erase, then C5 (THR or SYM by the resident flag). -/
def W2 (iMode : Fin NI) (ini : Fin 40 → Fin NI) (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI)
    (iniS : Fin 9 → Fin NI) :=
  Composition.machine (eraseW NI) (CloseoutRowsOriginalSwitch.machine (ThrC5.thrC5 NI ini ix ib iOne)
    (SymC5.symC5 NI iniS) (initPort NI iMode))

end Mach

/-! ## THR rows -/

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

theorem thr_keys_len : (KeySucc.keys a r L target).length =
    (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length := by
  rw [← RCFive.RowKeys.thr_rows_eq a r L target, List.length_map]

/-- The THR row's mask word. -/
abbrev thrW (j : Nat) (hj : j < (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length) :
    List Bool :=
  PCJ45bee56da9f34d5a_SelectionWord.gridWord (thrLive r L) (thrLive r L)ᶜ.card (half_sum _)
    (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows[j].select

theorem thr_w1 (j : Nat) (hj : j < (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length)
    (iMode : Fin NI) (hmode : init iMode = [true]) :
    Step (W1 NI iMode) (thrMaskCost a r four L target + 2) (fun _ => 0)
      (thrBase a r four L target NI pub init rcp C cC hF j) (fun _ => 0)
      (Function.update (thrBase a r four L target NI pub init rcp C cC hF j) (loopPort NI vL)
        (thrW a r L target j hj)) := by
  refine CloseoutRowsOriginalSwitch.true_run _ _ _
    (thr_mask_work a r four L target NI pub init rcp C cC hF j hj) ?_
  rw [(thr_base_rc a r four L target NI pub init rcp C cC hF j).2.1, hmode]
  rfl

theorem thr_blank (j : Nat) (hj : j < (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length) :
    thrBase a r four L target NI pub init rcp C cC hF j (loopPort NI vL) =
      List.replicate (2^(thrLive r L)ᶜ.card) false ∧
    thrBase a r four L target NI pub init rcp C cC hF j (c6Port NI 0) =
      List.replicate (2^(thrLive r L)ᶜ.card) true ∧
    thrBase a r four L target NI pub init rcp C cC hF j (c6Port NI 1) =
      List.replicate (2*2^(thrLive r L)ᶜ.card+1) false := by
  obtain ⟨k, _, hloop, hc6, _⟩ := thr_base_masters a r four L target NI pub init rcp C cC hF j hj
  exact ⟨by rw [hloop]; rfl, by rw [hc6]; rfl, by rw [hc6]; rfl⟩

/-- **THR W2**: from the row's bank with its mask on the verdict tape to row `j+1`'s bank. -/
theorem thr_w2 (j : Nat) (hj : j < (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length)
    (iMode : Fin NI) (hmode : init iMode = [true])
    (ini : Fin 40 → Fin NI) (hini : Function.Injective ini) (Rp Lp : Nat)
    (hinit : ∀ m, init (ini m) = ThrKey.psInit (KeyTop.wT a r four L target) Rp Lp m)
    (hRp : ∀ p, p ≤ KeySucc.cut a r target →
      RowsConstruction.ThrPrime.psCost (KeyTop.wT a r four L target) (KeySucc.cut a r target) p + 1 ≤ Rp)
    (hL : Rp + 1 ≤ Lp)
    (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (hib : Function.Injective ib) (hone : ib 9 ≠ iOne)
    (hinitD : ∀ c, init (ix c) = KeyStep.fb (ThrWidth.T a r four L target) (ThrSel.bnd a r c))
    (hinitB : ∀ k : Fin 82, ¬ (73 ≤ k.val ∧ k.val < 77) → init (ib k) = ThrSelBase.baseInit a r four L target k)
    (hinitO : init iOne = ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target))
      (KeyStep.fb (KeyTop.wT a r four L target) 1))
    (iniS : Fin 9 → Fin NI) :
    Step (W2 NI iMode ini ix ib iOne iniS)
      (2*2^(thrLive r L)ᶜ.card+4+1+(ThrC5.c5Cost (KeyTop.wT a r four L target) (KeyTop.RT a r four L target)
        (natBitLength (KeyTop.NS a r L target)) (seedScratch (KeyTop.NS a r L target)) Rp
        (ThrWidth.T a r four L target) (ThrSelBase.bF (ThrWidth.T a r four L target))+2))
      (fun _ => 0)
      (Function.update (thrBase a r four L target NI pub init rcp C cC hF j) (loopPort NI vL) (thrW a r L target j hj))
      (fun _ => 0) (thrBase a r four L target NI pub init rcp C cC hF (j+1)) := by
  obtain ⟨hv, hd, hg⟩ := thr_blank a r four L target NI pub init rcp C cC hF j hj
  have hne0 : c6Port NI 0 ≠ loopPort NI vL := by
    intro e; have := congrArg Fin.val e; rw [c6Port_val, loopPort_val] at this; simp [vL] at this
  have hne1 : c6Port NI 1 ≠ loopPort NI vL := by
    intro e; have := congrArg Fin.val e; rw [c6Port_val, loopPort_val] at this; simp [vL] at this
  have s1 := erase_work NI (thrLive r L)ᶜ.card (thrW a r L target j hj)
    (by rw [PCJ45bee56da9f34d5a_SelectionWord.gridWord_length])
    (Function.update (thrBase a r four L target NI pub init rcp C cC hF j) (loopPort NI vL) (thrW a r L target j hj))
    (Function.update_self _ _ _) (by rw [Function.update_of_ne hne0, hd]) (by rw [Function.update_of_ne hne1, hg])
  rw [Function.update_idem, ← hv, Function.update_eq_self] at s1
  have hk : j < (KeySucc.keys a r L target).length := by rw [thr_keys_len]; exact hj
  have s2 := CloseoutRowsOriginalSwitch.true_run (ThrC5.thrC5 NI ini ix ib iOne) (SymC5.symC5 NI iniS)
    (initPort NI iMode)
    (ThrC5.thr_c5 a r four L target NI pub init rcp C cC hF j hk ini hini Rp Lp hinit hRp hL ix ib iOne hib hone
      hinitD hinitB hinitO)
    (by rw [(thr_base_rc a r four L target NI pub init rcp C cC hF j).2.1, hmode]; rfl)
  exact s1.seq s2

end Thr

/-! ## SYM rows -/

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

theorem sym_keys_len : (RCFive.RowKeys.symKeys r L target).length =
    (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length := by
  rw [← RCFive.RowKeys.sym_rows_eq r L target, List.length_map]

/-- The SYM mask cost. -/
abbrev symMaskCost : Nat :=
  1+1+((2^(((symLive r L)ᶜ.card+1)/2)*(ThrMask.rowCost (symLive r L)ᶜ.card r.q
    (symRes r.q (symT a r four L target)) (SymVerdict.cost r L target (symT a r four L target)
      (symT a r four L target+3))+3)+3)+1+(1+1+(2*2^(symLive r L)ᶜ.card+2)))

/-- The SYM row's mask word. -/
abbrev symW (j : Nat) (hj : j < (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length) :
    List Bool :=
  PCJ45bee56da9f34d5a_SelectionWord.gridWord (symLive r L) (symLive r L)ᶜ.card (half_sum _)
    (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows[j].select

/-- **SYM C3 inside `complete`.** -/
theorem sym_mask_work (j : Nat)
    (hj : j < (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length) :
    Step (maskW NI symLoop) (symMaskCost a r four L target) (fun _ => 0)
      (symBase a r four L target NI pub init rcp C cC hF j) (fun _ => 0)
      (Function.update (symBase a r four L target NI pub init rcp C cC hF j) (loopPort NI vL)
        (symW r L target j hj)) := by
  obtain ⟨k, hk, hrow, hloop, hc6, _⟩ := sym_base_masters a r four L target NI pub init rcp C cC hF j hj
  have hM := sym_row_mask a r four L target (symRes r.q (symT a r four L target)) (symR_le_res _ _) k hk []
  simp only [List.nil_append] at hM
  unfold symW
  rw [← hrow]
  refine mask_work NI (symLive r L) (symLive r L)ᶜ.card (symRes r.q (symT a r four L target)) (loopCl r.q)
    (loopDl r.q) (symMasters a r four L target (symRes r.q (symT a r four L target)) k) _
    (PCJ45bee56da9f34d5a_SelectionWord.gridWord_length _ _ _ _) _ _ hM _ (fun i => ?_)
  unfold lslots localT
  rcases split2 i with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rw [Fin.addCases_left, Fin.addCases_left, hloop]; rfl
  · rw [Fin.addCases_right, Fin.addCases_right, hc6]

theorem sym_w1 (j : Nat) (hj : j < (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length)
    (iMode : Fin NI) (hmode : init iMode = [false]) :
    Step (W1 NI iMode) (symMaskCost a r four L target + 2) (fun _ => 0)
      (symBase a r four L target NI pub init rcp C cC hF j) (fun _ => 0)
      (Function.update (symBase a r four L target NI pub init rcp C cC hF j) (loopPort NI vL)
        (symW r L target j hj)) := by
  refine CloseoutRowsOriginalSwitch.false_run _ _ _
    (sym_mask_work a r four L target NI pub init rcp C cC hF j hj) ?_
  rw [(sym_base_rc a r four L target NI pub init rcp C cC hF j).2.1, hmode]
  rfl

theorem sym_blank (j : Nat) (hj : j < (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length) :
    symBase a r four L target NI pub init rcp C cC hF j (loopPort NI vL) =
      List.replicate (2^(symLive r L)ᶜ.card) false ∧
    symBase a r four L target NI pub init rcp C cC hF j (c6Port NI 0) =
      List.replicate (2^(symLive r L)ᶜ.card) true ∧
    symBase a r four L target NI pub init rcp C cC hF j (c6Port NI 1) =
      List.replicate (2*2^(symLive r L)ᶜ.card+1) false := by
  obtain ⟨k, _, _, hloop, hc6, _⟩ := sym_base_masters a r four L target NI pub init rcp C cC hF j hj
  exact ⟨by rw [hloop]; rfl, by rw [hc6]; rfl, by rw [hc6]; rfl⟩

/-- **SYM W2**. -/
theorem sym_w2 (j : Nat) (hj : j < (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length)
    (iMode : Fin NI) (hmode : init iMode = [false])
    (ini : Fin 40 → Fin NI) (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI)
    (iniS : Fin 9 → Fin NI)
    (hinitS : ∀ m, init (iniS m) = SymC5.symInit (SymC5.sw a r four L target) r.circuits.length (SymC5.sbnd r) m) :
    Step (W2 NI iMode ini ix ib iOne iniS)
      (2*2^(symLive r L)ᶜ.card+4+1+(SymC5.symCost (SymC5.sw a r four L target) (symRes r.q (symT a r four L target))
        (natBitLength (SymC5.sNS r L target)) (seedScratch (SymC5.sNS r L target))+2))
      (fun _ => 0)
      (Function.update (symBase a r four L target NI pub init rcp C cC hF j) (loopPort NI vL) (symW r L target j hj))
      (fun _ => 0) (symBase a r four L target NI pub init rcp C cC hF (j+1)) := by
  obtain ⟨hv, hd, hg⟩ := sym_blank a r four L target NI pub init rcp C cC hF j hj
  have hne0 : c6Port NI 0 ≠ loopPort NI vL := by
    intro e; have := congrArg Fin.val e; rw [c6Port_val, loopPort_val] at this; simp [vL] at this
  have hne1 : c6Port NI 1 ≠ loopPort NI vL := by
    intro e; have := congrArg Fin.val e; rw [c6Port_val, loopPort_val] at this; simp [vL] at this
  have s1 := erase_work NI (symLive r L)ᶜ.card (symW r L target j hj)
    (by rw [PCJ45bee56da9f34d5a_SelectionWord.gridWord_length])
    (Function.update (symBase a r four L target NI pub init rcp C cC hF j) (loopPort NI vL) (symW r L target j hj))
    (Function.update_self _ _ _) (by rw [Function.update_of_ne hne0, hd]) (by rw [Function.update_of_ne hne1, hg])
  rw [Function.update_idem, ← hv, Function.update_eq_self] at s1
  have hk : j < (RCFive.RowKeys.symKeys r L target).length := by rw [sym_keys_len]; exact hj
  have s2 := CloseoutRowsOriginalSwitch.false_run (ThrC5.thrC5 NI ini ix ib iOne) (SymC5.symC5 NI iniS)
    (initPort NI iMode)
    (SymC5.sym_c5 a r four L target NI pub init rcp C cC hF iniS hinitS j hk)
    (by rw [(sym_base_rc a r four L target NI pub init rcp C cC hF j).2.1, hmode]; rfl)
  exact s1.seq s2

end Sym

end
end RowsConstruction.CompleteRow
