import Proof.Rows.CountFlags
import Proof.Rows.RowsCellInput
import Proof.Rows.RowsCellReload

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution RadixSemantics SignedSortKey
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.CloseoutFinal
noncomputable section

/-! ## 0. Two arithmetic facts -/

theorem binary_mod (w n : Nat) : binary w n = binary w (n % 2^w) := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih =>
    show (n % 2 == 1) :: binary w (n / 2) = (n % 2^(w+1) % 2 == 1) :: binary w (n % 2^(w+1) / 2)
    have h1 : n % 2^(w+1) % 2 = n % 2 :=
      Nat.mod_mod_of_dvd n (Dvd.intro (2^w) (by rw [pow_succ]; ring))
    have h2 : n % 2^(w+1) / 2 = n / 2 % 2^w := by
      rw [pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    rw [h1, h2, ← ih]

/-- The column cursor advances by one, wrapping at `2^w` (no overflow hypothesis). -/
theorem inc_step (w k D : Nat) (hD : 2*w+1 ≤ D) :
    Step PCJ45bee56da9f34d5a_CountFlags.inc (4*w+4) (fun _ => 0)
      (![frame (binary w k), List.replicate D false] : Fin 2 → List Bool)
      (fun _ => 0) (![frame (binary w (k+1)), List.replicate D false] : Fin 2 → List Bool) := by
  rw [binary_mod w k, binary_mod w (k+1)]
  have hk : k % 2^w < 2^w := Nat.mod_lt _ (Nat.pow_pos (by decide))
  let ws := binary w (k % 2^w)
  have hw : ws.length = w := binary_length _ _
  have hsum : Add.sum ws (List.replicate ws.length false) true = binary w ((k+1) % 2^w) := by
    have hl : (Add.sum ws (List.replicate ws.length false) true).length = w := by
      rw [Add.sum_length _ _ _ (by simp), hw]
    have hv : value (Add.sum ws (List.replicate ws.length false) true) = (k+1) % 2^w := by
      rw [FinalPrimeCursor.incr_value, hw, binary_value w _ hk, Nat.add_mod, Nat.mod_mod,
        ← Nat.add_mod]
    have h := BoundedCounter.binary_of_value (Add.sum ws (List.replicate ws.length false) true)
    rw [hl, hv] at h
    exact h.symm
  have h := (FinalPrimeCursor.incr_step ws).mask (cap:=D) (fun _ => true) (by intro i _; rfl)
    (by rw [hw]; exact hD)
  rw [hsum, hw] at h
  have fuel : 2*(2*w+1)+2 = 4*w+4 := by omega
  rw [fuel] at h
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i; fin_cases i <;> rfl

theorem pad_replicate (R n : Nat) (h : n ≤ R) :
    ZeroPadding.pad R (List.replicate n false) = List.replicate R false := by
  simp only [ZeroPadding.pad, List.length_replicate, List.replicate_append_replicate]
  congr 1
  omega

/-! ## 1. Layout -/

abbrev MT : Nat := (257+254)+7

def layout {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (Z : Fin 7 → α) : Fin MT → α :=
  Fin.addCases (m:=257+254) (n:=7) (CellReload.layout X Y) Z

def cellP (i : Fin 257) : Fin MT := (CellReload.cellPort i).castAdd 7
def masterP (k : Fin 254) : Fin MT := (CellReload.masterPort k).castAdd 7
def auxP (j : Fin 7) : Fin MT := j.natAdd (257+254)

@[simp] theorem layout_cell {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (Z : Fin 7 → α)
    (i : Fin 257) : layout X Y Z (cellP i) = X i := by
  simp [layout, cellP]
@[simp] theorem layout_master {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (Z : Fin 7 → α)
    (k : Fin 254) : layout X Y Z (masterP k) = Y k := by
  simp [layout, masterP]
@[simp] theorem layout_aux {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (Z : Fin 7 → α)
    (j : Fin 7) : layout X Y Z (auxP j) = Z j := by
  simp [layout, auxP]

theorem cellP_val (i : Fin 257) : (cellP i).val = i.val := rfl
theorem masterP_val (k : Fin 254) : (masterP k).val = 257+k.val := rfl
theorem auxP_val (j : Fin 7) : (auxP j).val = 511+j.val := rfl

theorem cover {motive : Fin MT → Prop} (hc : ∀ i, motive (cellP i)) (hm : ∀ k, motive (masterP k))
    (ha : ∀ j, motive (auxP j)) (x : Fin MT) : motive x := by
  refine Fin.addCases (m:=257+254) (n:=7) (fun y => ?_) (fun j => ha j) x
  exact Fin.addCases (m:=257) (n:=254) (fun i => hc i) (fun k => hm k) y

/-! ## 2. The four stages -/

def scatterSlots : Fin 8 → Fin MT :=
  ![auxP 0, auxP 1, auxP 2, auxP 3, auxP 4, auxP 5, masterP 109, auxP 6]
theorem scatterSlots_val (j : Fin 8) :
    (scatterSlots j).val = ![511, 512, 513, 514, 515, 516, 366, 517] j := by
  fin_cases j <;> rfl
theorem scatterSlots_injective : Function.Injective scatterSlots := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [scatterSlots_val, scatterSlots_val] at hv
  fin_cases a <;> fin_cases b <;> simp at hv ⊢

def scatterStage := RecoveryFocus.machine scatterSlots PCJ45bee56da9f34d5a_CellScatter.machine

def eraseSlots : Fin 4 → Fin MT := ![masterP 109, auxP 2, cellP 254, cellP 255]
theorem eraseSlots_val (j : Fin 4) : (eraseSlots j).val = ![366, 513, 254, 255] j := by
  fin_cases j <;> rfl
theorem eraseSlots_injective : Function.Injective eraseSlots := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [eraseSlots_val, eraseSlots_val] at hv
  fin_cases a <;> fin_cases b <;> simp at hv ⊢

def eraseStage := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 2)

def incSlots : Fin 2 → Fin MT := ![auxP 1, auxP 4]
theorem incSlots_val (j : Fin 2) : (incSlots j).val = ![512, 515] j := by
  fin_cases j <;> rfl
theorem incSlots_injective : Function.Injective incSlots := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [incSlots_val, incSlots_val] at hv
  fin_cases a <;> fin_cases b <;> simp at hv ⊢

def incStage := RecoveryFocus.machine incSlots PCJ45bee56da9f34d5a_CountFlags.inc

/-! ## 3. The cell state -/

def auxHeads : Fin 7 → ℕ := ![0,0,0,0,0,0,1]

def heads (len : Nat) : Fin MT → ℕ :=
  layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) len) (fun _ => 0) auxHeads

def aux {q : Nat} (live : Finset (Fin q)) (s C D rowN colN : Nat) (bits : List Bool) :
    Fin 7 → List Bool :=
  ![frame (binary ((s+1)/2) rowN), frame (binary (s/2) colN), bits, List.replicate C false,
    List.replicate D false, CloseoutRowsGateSupport.gateMembers liveᶜ, CompareMachine.word q]

def tapes {q : Nat} (live : Finset (Fin q)) (s R C D rowN colN : Nat) (M : Fin 254 → List Bool)
    (out : List Bool) : Fin MT → List Bool :=
  layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out) M
    (aux live s C D rowN colN (List.replicate R false))

/-- The cell's full assignment. -/
def point {q : Nat} (live : Finset (Fin q)) (s : Nat) (ha : (s+1)/2+s/2=liveᶜ.card)
    (rowN colN : Nat) : BitInput q :=
  C10SupplierRowInput.joinInput live (fun _ => false) (C10ExternalRowLoop.printerPoint live s ha rowN colN)

/-! ## 4. Stage lemmas -/

theorem scatter_step {q : Nat} (live : Finset (Fin q)) (s : Nat) (ha : (s+1)/2+s/2=liveᶜ.card)
    (R C D rowN colN : Nat) (M : Fin 254 → List Bool) (hM109 : M 109 = List.replicate R false)
    (X : Fin 257 → List Bool) (HX : Fin 257 → ℕ)
    (hqR : q ≤ R) (hsR : (s+1)/2+s/2 ≤ R)
    (hl : 2*((s+1)/2)+1 ≤ C) (hr : 2*(s/2)+1 ≤ C) (hD : 4*((s+1)/2+s/2)+7 ≤ D) (hQ : 4*q+3 ≤ D) :
    Step scatterStage (8*((s+1)/2+s/2)+8*q+25)
      (layout HX (fun _ => 0) auxHeads)
      (layout X M (aux live s C D rowN colN (List.replicate R false)))
      (layout HX (fun _ => 0) auxHeads)
      (layout X (Function.update M 109 (ZeroPadding.pad R (List.ofFn (point live s ha rowN colN))))
        (aux live s C D rowN colN (ZeroPadding.pad R
          (List.ofFn (C10ExternalRowLoop.printerPoint live s ha rowN colN))))) := by
  have base := PCJ45bee56da9f34d5a_CellScatter.cursor_run live s ha rowN colN C D hl hr hD hQ
  dsimp only at base
  have padded := base.pad (![0,0,R,0,0,0,R,0] : Fin 8 → ℕ)
  have focused := padded.focus scatterSlots scatterSlots_injective
    (layout HX (fun _ => 0) auxHeads)
    (layout X M (aux live s C D rowN colN (List.replicate R false)))
  have hH : dockH scatterSlots (layout HX (fun _ => 0) auxHeads)
      PCJ45bee56da9f34d5a_CellScatter.heads = layout HX (fun _ => 0) auxHeads := by
    apply dockH_existing
    intro j
    fin_cases j <;> rfl
  have hA : install scatterSlots (layout X M (aux live s C D rowN colN (List.replicate R false)))
      (fun i => ZeroPadding.pad ((![0,0,R,0,0,0,R,0] : Fin 8 → ℕ) i)
        (PCJ45bee56da9f34d5a_CellScatter.bank (binary ((s+1)/2) rowN) (binary (s/2) colN)
          (List.replicate ((s+1)/2+s/2) false) (List.replicate q false)
          (CloseoutRowsGateSupport.gateMembers liveᶜ) q C D i)) =
      layout X M (aux live s C D rowN colN (List.replicate R false)) := by
    apply install_existing
    intro j
    fin_cases j
    · change layout X M _ (auxP 0) = _
      simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
    · change layout X M _ (auxP 1) = _
      simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
    · change layout X M _ (auxP 2) = _
      simp only [layout_aux]
      exact (pad_replicate R _ hsR).symm
    · change layout X M _ (auxP 3) = _
      simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
    · change layout X M _ (auxP 4) = _
      simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
    · change layout X M _ (auxP 5) = _
      simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
    · change layout X M _ (masterP 109) = _
      simp only [layout_master, hM109]
      exact (pad_replicate R _ hqR).symm
    · change layout X M _ (auxP 6) = _
      simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
  have hO : install scatterSlots (layout X M (aux live s C D rowN colN (List.replicate R false)))
      (fun i => ZeroPadding.pad ((![0,0,R,0,0,0,R,0] : Fin 8 → ℕ) i)
        (PCJ45bee56da9f34d5a_CellScatter.bank (binary ((s+1)/2) rowN) (binary (s/2) colN)
          (List.ofFn (C10ExternalRowLoop.printerPoint live s ha rowN colN))
          (List.ofFn (point live s ha rowN colN))
          (CloseoutRowsGateSupport.gateMembers liveᶜ) q C D i)) =
      layout X (Function.update M 109 (ZeroPadding.pad R (List.ofFn (point live s ha rowN colN))))
        (aux live s C D rowN colN (ZeroPadding.pad R
          (List.ofFn (C10ExternalRowLoop.printerPoint live s ha rowN colN)))) := by
    funext x
    refine cover (motive := fun x => install scatterSlots
      (layout X M (aux live s C D rowN colN (List.replicate R false)))
      (fun i => ZeroPadding.pad ((![0,0,R,0,0,0,R,0] : Fin 8 → ℕ) i)
        (PCJ45bee56da9f34d5a_CellScatter.bank (binary ((s+1)/2) rowN) (binary (s/2) colN)
          (List.ofFn (C10ExternalRowLoop.printerPoint live s ha rowN colN))
          (List.ofFn (point live s ha rowN colN))
          (CloseoutRowsGateSupport.gateMembers liveᶜ) q C D i)) x =
      layout X (Function.update M 109 (ZeroPadding.pad R (List.ofFn (point live s ha rowN colN))))
        (aux live s C D rowN colN (ZeroPadding.pad R
          (List.ofFn (C10ExternalRowLoop.printerPoint live s ha rowN colN)))) x)
      (fun i => ?_) (fun k => ?_) (fun j => ?_) x
    · rw [install_other _ _ _ _ (fun j h => by
        have hv := congrArg Fin.val h
        rw [scatterSlots_val, cellP_val] at hv
        have := i.isLt
        fin_cases j <;> simp at hv <;> omega)]
      simp
    · by_cases hk : k = 109
      · subst hk
        rw [layout_master, Function.update_self]
        change install scatterSlots _ _ (scatterSlots 6) = _
        rw [install_slot _ scatterSlots_injective]
        rfl
      · rw [install_other _ _ _ _ (fun j h => by
          have hv := congrArg Fin.val h
          rw [scatterSlots_val, masterP_val] at hv
          have hne : k.val ≠ 109 := fun h' => hk (Fin.ext h')
          have := k.isLt
          fin_cases j <;> simp at hv <;> omega)]
        simp [Function.update_of_ne hk]
    · rw [layout_aux]
      fin_cases j
      · change install scatterSlots _ _ (scatterSlots 0) = _
        rw [install_slot _ scatterSlots_injective]
        simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
      · change install scatterSlots _ _ (scatterSlots 1) = _
        rw [install_slot _ scatterSlots_injective]
        simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
      · change install scatterSlots _ _ (scatterSlots 2) = _
        rw [install_slot _ scatterSlots_injective]
        rfl
      · change install scatterSlots _ _ (scatterSlots 3) = _
        rw [install_slot _ scatterSlots_injective]
        simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
      · change install scatterSlots _ _ (scatterSlots 4) = _
        rw [install_slot _ scatterSlots_injective]
        simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
      · change install scatterSlots _ _ (scatterSlots 5) = _
        rw [install_slot _ scatterSlots_injective]
        simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
      · change install scatterSlots _ _ (scatterSlots 7) = _
        rw [install_slot _ scatterSlots_injective]
        simp [aux, PCJ45bee56da9f34d5a_CellScatter.bank]
  rw [hH, hA] at focused
  exact focused.congr rfl hO

theorem erase_step (R : Nat) (X : Fin 257 → List Bool) (HX : Fin 257 → ℕ)
    (M : Fin 254 → List Bool) (Z : Fin 7 → List Bool) (HZ : Fin 7 → ℕ)
    (hX254 : X 254 = List.replicate R true) (hX255 : X 255 = List.replicate (R+1) false)
    (hH109 : HZ 2 = 0) (hHX254 : HX 254 = 0) (hHX255 : HX 255 = 0)
    (hM : (M 109).length ≤ R) (hZ : (Z 2).length ≤ R) :
    Step eraseStage (2*R+4)
      (layout HX (fun _ => 0) HZ) (layout X M Z)
      (layout HX (fun _ => 0) HZ)
      (layout X (Function.update M 109 (List.replicate R false))
        (Function.update Z 2 (List.replicate R false))) := by
  have hb : ∀ i, ((![M 109, Z 2] : Fin 2 → List Bool) i).length ≤ R := by
    intro i
    fin_cases i
    · exact hM
    · exact hZ
  have base := Step.of_ready (RecoveryScratchErase.erase_ready (t:=2) R (R+1) ![M 109, Z 2] hb)
  have focused := base.focus eraseSlots eraseSlots_injective (layout HX (fun _ => 0) HZ) (layout X M Z)
  have hH : dockH eraseSlots (layout HX (fun _ => 0) HZ) (fun _ => 0) =
      layout HX (fun _ => 0) HZ := by
    apply dockH_existing
    intro j
    fin_cases j
    · change layout HX (fun _ => 0) HZ (masterP 109) = 0; simp
    · change layout HX (fun _ => 0) HZ (auxP 2) = 0; simp [hH109]
    · change layout HX (fun _ => 0) HZ (cellP 254) = 0; simp [hHX254]
    · change layout HX (fun _ => 0) HZ (cellP 255) = 0; simp [hHX255]
  have hA : install eraseSlots (layout X M Z)
      (Fin.addCases (motive := fun _ => List Bool)
        (Fin.addCases (motive := fun _ => List Bool) (![M 109, Z 2] : Fin 2 → List Bool)
        (fun _ : Fin 1 => List.replicate R true)) (fun _ : Fin 1 => List.replicate (R+1) false)) =
      layout X M Z := by
    apply install_existing
    intro j
    fin_cases j
    · change layout X M Z (masterP 109) = _; rw [layout_master]; rfl
    · change layout X M Z (auxP 2) = _; rw [layout_aux]; rfl
    · change layout X M Z (cellP 254) = _; rw [layout_cell, hX254]; rfl
    · change layout X M Z (cellP 255) = _; rw [layout_cell, hX255]; rfl
  have hO : install eraseSlots (layout X M Z)
      (Fin.addCases (motive := fun _ => List Bool)
        (Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin 2 => List.replicate R false)
        (fun _ : Fin 1 => List.replicate R true))
        (fun _ : Fin 1 => List.replicate (max (R+1) (R+1)) false)) =
      layout X (Function.update M 109 (List.replicate R false))
        (Function.update Z 2 (List.replicate R false)) := by
    funext x
    refine cover (motive := fun x => install eraseSlots (layout X M Z)
      (Fin.addCases (motive := fun _ => List Bool)
        (Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin 2 => List.replicate R false)
        (fun _ : Fin 1 => List.replicate R true))
        (fun _ : Fin 1 => List.replicate (max (R+1) (R+1)) false)) x =
      layout X (Function.update M 109 (List.replicate R false))
        (Function.update Z 2 (List.replicate R false)) x) (fun i => ?_) (fun k => ?_) (fun j => ?_) x
    · by_cases h254 : i = 254
      · subst h254
        change install eraseSlots _ _ (eraseSlots 2) = _
        rw [install_slot _ eraseSlots_injective, layout_cell, hX254]
        rfl
      · by_cases h255 : i = 255
        · subst h255
          change install eraseSlots _ _ (eraseSlots 3) = _
          rw [install_slot _ eraseSlots_injective, layout_cell, hX255]
          show List.replicate (max (R+1) (R+1)) false = _
          rw [max_self]
        · rw [install_other _ _ _ _ (fun j h => by
            have hv := congrArg Fin.val h
            rw [eraseSlots_val, cellP_val] at hv
            have h1 : i.val ≠ 254 := fun h' => h254 (Fin.ext h')
            have h2 : i.val ≠ 255 := fun h' => h255 (Fin.ext h')
            have := i.isLt
            fin_cases j <;> simp at hv <;> omega)]
          simp
    · by_cases hk : k = 109
      · subst hk
        change install eraseSlots _ _ (eraseSlots 0) = _
        rw [install_slot _ eraseSlots_injective, layout_master, Function.update_self]
        rfl
      · rw [install_other _ _ _ _ (fun j h => by
          have hv := congrArg Fin.val h
          rw [eraseSlots_val, masterP_val] at hv
          have hne : k.val ≠ 109 := fun h' => hk (Fin.ext h')
          have := k.isLt
          fin_cases j <;> simp at hv <;> omega)]
        simp [Function.update_of_ne hk]
    · by_cases hj : j = 2
      · subst hj
        change install eraseSlots _ _ (eraseSlots 1) = _
        rw [install_slot _ eraseSlots_injective, layout_aux, Function.update_self]
        rfl
      · rw [install_other _ _ _ _ (fun j' h => by
          have hv := congrArg Fin.val h
          rw [eraseSlots_val, auxP_val] at hv
          have hne : j.val ≠ 2 := fun h' => hj (Fin.ext h')
          have := j.isLt
          fin_cases j' <;> simp at hv <;> omega)]
        simp [Function.update_of_ne hj]
  rw [hH, hA, hO] at focused
  exact focused

theorem inc_stage_step (X : Fin 257 → List Bool) (HX : Fin 257 → ℕ) (M : Fin 254 → List Bool)
    {q : Nat} (live : Finset (Fin q)) (s R C D rowN colN : Nat) (hDi : 2*(s/2)+1 ≤ D) :
    Step incStage (4*(s/2)+4)
      (layout HX (fun _ => 0) auxHeads) (layout X M (aux live s C D rowN colN (List.replicate R false)))
      (layout HX (fun _ => 0) auxHeads)
      (layout X M (aux live s C D rowN (colN+1) (List.replicate R false))) := by
  have base := inc_step (s/2) colN D hDi
  have focused := base.focus incSlots incSlots_injective (layout HX (fun _ => 0) auxHeads)
    (layout X M (aux live s C D rowN colN (List.replicate R false)))
  have hH : dockH incSlots (layout HX (fun _ => 0) auxHeads) (fun _ => 0) =
      layout HX (fun _ => 0) auxHeads := by
    apply dockH_existing
    intro j
    fin_cases j <;> rfl
  have hA : install incSlots (layout X M (aux live s C D rowN colN (List.replicate R false)))
      (![frame (binary (s/2) colN), List.replicate D false] : Fin 2 → List Bool) =
      layout X M (aux live s C D rowN colN (List.replicate R false)) := by
    apply install_existing
    intro j
    fin_cases j
    · change layout X M _ (auxP 1) = _; simp [aux]
    · change layout X M _ (auxP 4) = _; simp [aux]
  have hO : install incSlots (layout X M (aux live s C D rowN colN (List.replicate R false)))
      (![frame (binary (s/2) (colN+1)), List.replicate D false] : Fin 2 → List Bool) =
      layout X M (aux live s C D rowN (colN+1) (List.replicate R false)) := by
    funext x
    refine cover (motive := fun x => install incSlots
      (layout X M (aux live s C D rowN colN (List.replicate R false)))
      (![frame (binary (s/2) (colN+1)), List.replicate D false] : Fin 2 → List Bool) x =
      layout X M (aux live s C D rowN (colN+1) (List.replicate R false)) x)
      (fun i => ?_) (fun k => ?_) (fun j => ?_) x
    · rw [install_other _ _ _ _ (fun j h => by
        have hv := congrArg Fin.val h
        rw [incSlots_val, cellP_val] at hv
        have := i.isLt
        fin_cases j <;> simp at hv <;> omega)]
      simp
    · rw [install_other _ _ _ _ (fun j h => by
        have hv := congrArg Fin.val h
        rw [incSlots_val, masterP_val] at hv
        have := k.isLt
        fin_cases j <;> simp at hv <;> omega)]
      simp
    · rw [layout_aux]
      by_cases h1 : j = 1
      · subst h1
        change install incSlots _ _ (incSlots 0) = _
        rw [install_slot _ incSlots_injective]
        rfl
      · by_cases h4 : j = 4
        · subst h4
          change install incSlots _ _ (incSlots 1) = _
          rw [install_slot _ incSlots_injective]
          rfl
        · rw [install_other _ _ _ _ (fun j' h => by
            have hv := congrArg Fin.val h
            rw [incSlots_val, auxP_val] at hv
            have e1 : j.val ≠ 1 := fun h' => h1 (Fin.ext h')
            have e4 : j.val ≠ 4 := fun h' => h4 (Fin.ext h')
            have := j.isLt
            fin_cases j' <;> simp at hv <;> omega), layout_aux]
          fin_cases j <;> simp_all [aux]
  rw [hH, hA, hO] at focused
  exact focused

/-! ## 5. One cell -/

/-- Per-cell cost: scatter, reload+verdict at the traversal bound `Bt`, erase, cursor increment. -/
def bodyCost (s q R Bt : Nat) : Nat :=
  8*((s+1)/2+s/2)+8*q+25+1+((2*R+4+1+(1+1+(Bt+4*R+12)))+1+((2*R+4)+1+(4*(s/2)+4)))

theorem aux_erase {q : Nat} (live : Finset (Fin q)) (s R C D rowN colN : Nat) (b : List Bool) :
    Function.update (aux live s C D rowN colN b) 2 (List.replicate R false) =
      aux live s C D rowN colN (List.replicate R false) := by
  funext j
  fin_cases j <;> rfl

end
end RowsConstruction.ThrCell
