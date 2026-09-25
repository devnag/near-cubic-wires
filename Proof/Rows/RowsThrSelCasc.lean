import Proof.Rows.RowsThrSelPure

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrSelCasc
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeyTop RowsConstruction.ThrKey
open RowsConstruction.ThrSel
noncomputable section

section Ports
variable (NI : Nat)

/-- The four child-digit masters. -/
def dPort : Fin 4 → Fin 254 := ![228, 229, 230, 231]

theorem dPort_val (c : Fin 4) : (dPort c).val = 228 + c.val := by
  fin_cases c <;> rfl

theorem masterPort_inj (i k : Fin 254) : masterPort NI i = masterPort NI k ↔ i = k := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [masterPort_val, masterPort_val] at hv
    exact Fin.ext (by omega)
  · intro h; rw [h]

variable (ix : Fin 4 → Fin NI)

/-- Level `c`: digit master `228+c`, bound `init (ix c)`, flag and scratch cells 0–3, clock 254, log 255. -/
def slD (c : Fin 4) : Fin 8 → Fin (2+rowsWork NI) :=
  ![masterPort NI (dPort c), initPort NI (ix c), cellPort NI 0, cellPort NI 1, cellPort NI 2, cellPort NI 3,
    cellPort NI 254, cellPort NI 255]

theorem slD_injective (c : Fin 4) : Function.Injective (slD NI ix c) := by
  intro x y h
  have hv := congrArg Fin.val h
  have hc := (ix c).isLt
  have hd := dPort_val c
  have hc4 := c.isLt
  fin_cases x <;> fin_cases y <;>
    simp [slD, masterPort_val, cellPort_val, initPort_val] at hv ⊢ <;> omega

/-- The final continuation: one step, nothing changes. -/
def idM : Machine (2+rowsWork NI) 2 := DecompositionCountPosition.move (fun _ => HeadMove.stay)

theorem id_step (H : Fin (2+rowsWork NI) → ℕ) (A : Fin (2+rowsWork NI) → List Bool) :
    Step (idM NI) 1 H A H A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run (fun _ : Fin (2+rowsWork NI) => HeadMove.stay) H A
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf])

def K0 := digitStep (slD NI ix 0) (idM NI)
def K1 := digitStep (slD NI ix 1) (K0 NI ix)
def K2 := digitStep (slD NI ix 2) (K1 NI ix)

/-- **The child-digit cascade** (one fixed machine). -/
def selC := digitStep (slD NI ix 3) (K2 NI ix)

/-- The cell blanks every level uses as scratch. -/
structure Cells (R : Nat) (A : Fin (2+rowsWork NI) → List Bool) : Prop where
  c0 : A (cellPort NI 0) = List.replicate R false
  c1 : A (cellPort NI 1) = List.replicate R false
  c2 : A (cellPort NI 2) = List.replicate R false
  c3 : A (cellPort NI 3) = List.replicate R false
  clk : A (cellPort NI 254) = List.replicate R true
  log : A (cellPort NI 255) = List.replicate (R+1) false

theorem cells_update (R : Nat) (A : Fin (2+rowsWork NI) → List Bool) (hc : Cells NI R A) (k : Fin 254)
    (v : List Bool) : Cells NI R (Function.update A (masterPort NI k) v) where
  c0 := by rw [Function.update_of_ne (cell_ne_master NI 0 k)]; exact hc.c0
  c1 := by rw [Function.update_of_ne (cell_ne_master NI 1 k)]; exact hc.c1
  c2 := by rw [Function.update_of_ne (cell_ne_master NI 2 k)]; exact hc.c2
  c3 := by rw [Function.update_of_ne (cell_ne_master NI 3 k)]; exact hc.c3
  clk := by rw [Function.update_of_ne (cell_ne_master NI 254 k)]; exact hc.clk
  log := by rw [Function.update_of_ne (cell_ne_master NI 255 k)]; exact hc.log

theorem ready_of (w R : Nat) (A : Fin (2+rowsWork NI) → List Bool) (hc : Cells NI R A) (hR : 2*w+1 ≤ R)
    (c : Fin 4) : Ready (slD NI ix c) w R (fun _ => 0) A where
  heads := fun _ => rfl
  flag := hc.c0
  capI := hc.c1
  capC := hc.c2
  capL := hc.c3
  drv := hc.clk
  log := hc.log
  hR := hR

theorem upd_init (A : Fin (2+rowsWork NI) → List Bool) (k : Fin 254) (v : List Bool) (i : Fin NI) :
    Function.update A (masterPort NI k) v (initPort NI i) = A (initPort NI i) :=
  Function.update_of_ne (initPort_ne_master NI i k) _ _

/-- A bank that agrees with `A` off the four digit masters and carries `fb w (e c)` on them IS `digBank A w e`. -/
theorem digBank_char (A A' : Fin (2+rowsWork NI) → List Bool) (w : Nat) (e : Fin 4 → ℕ)
    (hoff : ∀ p, p ≠ masterPort NI 228 → p ≠ masterPort NI 229 → p ≠ masterPort NI 230 → p ≠ masterPort NI 231 →
      A' p = A p)
    (h0 : A' (masterPort NI 228) = fb w (e 0)) (h1 : A' (masterPort NI 229) = fb w (e 1))
    (h2 : A' (masterPort NI 230) = fb w (e 2)) (h3 : A' (masterPort NI 231) = fb w (e 3)) :
    digBank NI A w e = A' := by
  funext p
  unfold digBank
  by_cases q3 : p = masterPort NI 231
  · rw [q3, Function.update_self, h3]
  rw [Function.update_of_ne q3]
  by_cases q2 : p = masterPort NI 230
  · rw [q2, Function.update_self, h2]
  rw [Function.update_of_ne q2]
  by_cases q1 : p = masterPort NI 229
  · rw [q1, Function.update_self, h1]
  rw [Function.update_of_ne q1]
  by_cases q0 : p = masterPort NI 228
  · rw [q0, Function.update_self, h0]
  rw [Function.update_of_ne q0]
  exact (hoff p q0 q1 q2 q3).symm

/-- The cost of the cascade (four carried levels, the no-op last). -/
def cascCost (w R : Nat) : Nat := carryCost w R (carryCost w R (carryCost w R (carryCost w R 1)))

/-- **The cascade step.** From any bank with the cell blanks, digits `d c` on 228–231 and bounds `b c` on the four
bound words, the fixed machine `selC` writes `casc b d` on the four digit masters and changes nothing else. -/
theorem casc_step (w R : Nat) (b d : Fin 4 → ℕ) (A : Fin (2+rowsWork NI) → List Bool) (hc : Cells NI R A)
    (hR : 2*w+1 ≤ R) (hd : ∀ c, A (masterPort NI (dPort c)) = fb w (d c))
    (hb : ∀ c, A (initPort NI (ix c)) = fb w (b c)) (hlt : ∀ c, d c < b c) (hbw : ∀ c, b c < 2^w) :
    Step (selC NI ix) (cascCost w R) (fun _ => 0) A (fun _ => 0) (digBank NI A w (casc b d)) := by
  have hd0 : A (masterPort NI 228) = fb w (d 0) := hd 0
  have hd1 : A (masterPort NI 229) = fb w (d 1) := hd 1
  have hd2 : A (masterPort NI 230) = fb w (d 2) := hd 2
  have hd3 : A (masterPort NI 231) = fb w (d 3) := hd 3
  have ne : ∀ i k : Fin 254, i ≠ k → masterPort NI i ≠ masterPort NI k := fun i k h e =>
    h ((masterPort_inj NI i k).mp e)
  unfold casc
  by_cases h3 : d 3 + 1 < b 3
  · rw [if_pos h3]
    have s := digit_noCarry (slD NI ix 3) (slD_injective NI ix 3) (K2 NI ix) w (d 3) (b 3) R (fun _ => 0) A
      (ready_of NI ix w R A hc hR 3) (hd 3) (hb 3) h3 (hbw 3)
    have e : digBank NI A w (Function.update d 3 (d 3 + 1)) =
        Function.update A (masterPort NI 231) (fb w (d 3 + 1)) := by
      apply digBank_char
      · intro p _ _ _ q3; exact Function.update_of_ne q3 _ _
      · rw [Function.update_of_ne (ne 228 231 (by decide)), hd0]; rfl
      · rw [Function.update_of_ne (ne 229 231 (by decide)), hd1]; rfl
      · rw [Function.update_of_ne (ne 230 231 (by decide)), hd2]; rfl
      · rw [Function.update_self]; rfl
    rw [e]
    exact s.enlarge (by unfold cascCost carryCost; omega)
  rw [if_neg h3]
  have x3 : d 3 + 1 = b 3 := by have := hlt 3; omega
  set A3 := Function.update A (masterPort NI 231) (fb w 0) with hA3
  have hc3 := cells_update NI R A hc 231 (fb w 0)
  by_cases h2 : d 2 + 1 < b 2
  · rw [if_pos h2]
    have s2 := digit_noCarry (slD NI ix 2) (slD_injective NI ix 2) (K1 NI ix) w (d 2) (b 2) R (fun _ => 0) A3
      (ready_of NI ix w R A3 hc3 hR 2)
      (by show A3 (masterPort NI 230) = _; rw [hA3, Function.update_of_ne (ne 230 231 (by decide)), hd2])
      (by show A3 (initPort NI (ix 2)) = _; rw [hA3, upd_init, hb 2]) h2 (hbw 2)
    have s := digit_carry (slD NI ix 3) (slD_injective NI ix 3) (K2 NI ix) w (d 3) (b 3) R _ (fun _ => 0) (fun _ => 0) A _
      (ready_of NI ix w R A hc hR 3) (hd 3) (hb 3) x3 (hbw 3) s2
    have e : digBank NI A w (Function.update (Function.update d 3 0) 2 (d 2 + 1)) =
        Function.update A3 (masterPort NI 230) (fb w (d 2 + 1)) := by
      apply digBank_char
      · intro p _ _ q2 q3
        rw [Function.update_of_ne q2, hA3, Function.update_of_ne q3]
      · rw [Function.update_of_ne (ne 228 230 (by decide)), hA3, Function.update_of_ne (ne 228 231 (by decide)), hd0]
        rfl
      · rw [Function.update_of_ne (ne 229 230 (by decide)), hA3, Function.update_of_ne (ne 229 231 (by decide)), hd1]
        rfl
      · rw [Function.update_self]; rfl
      · rw [Function.update_of_ne (ne 231 230 (by decide)), hA3, Function.update_self]; rfl
    rw [e]
    exact s.enlarge (by unfold cascCost carryCost; omega)
  rw [if_neg h2]
  have x2 : d 2 + 1 = b 2 := by have := hlt 2; omega
  set A2 := Function.update A3 (masterPort NI 230) (fb w 0) with hA2
  have hc2 := cells_update NI R A3 hc3 230 (fb w 0)
  by_cases h1 : d 1 + 1 < b 1
  · rw [if_pos h1]
    have s1 := digit_noCarry (slD NI ix 1) (slD_injective NI ix 1) (K0 NI ix) w (d 1) (b 1) R (fun _ => 0) A2
      (ready_of NI ix w R A2 hc2 hR 1)
      (by show A2 (masterPort NI 229) = _; rw [hA2, Function.update_of_ne (ne 229 230 (by decide)), hA3,
        Function.update_of_ne (ne 229 231 (by decide)), hd1])
      (by show A2 (initPort NI (ix 1)) = _; rw [hA2, upd_init, hA3, upd_init, hb 1]) h1 (hbw 1)
    have s2 := digit_carry (slD NI ix 2) (slD_injective NI ix 2) (K1 NI ix) w (d 2) (b 2) R _ (fun _ => 0) (fun _ => 0) A3 _
      (ready_of NI ix w R A3 hc3 hR 2)
      (by show A3 (masterPort NI 230) = _; rw [hA3, Function.update_of_ne (ne 230 231 (by decide)), hd2])
      (by show A3 (initPort NI (ix 2)) = _; rw [hA3, upd_init, hb 2]) x2 (hbw 2) s1
    have s := digit_carry (slD NI ix 3) (slD_injective NI ix 3) (K2 NI ix) w (d 3) (b 3) R _ (fun _ => 0) (fun _ => 0) A _
      (ready_of NI ix w R A hc hR 3) (hd 3) (hb 3) x3 (hbw 3) s2
    have e : digBank NI A w (Function.update (Function.update (Function.update d 3 0) 2 0) 1 (d 1 + 1)) =
        Function.update A2 (masterPort NI 229) (fb w (d 1 + 1)) := by
      apply digBank_char
      · intro p _ q1 q2 q3
        rw [Function.update_of_ne q1, hA2, Function.update_of_ne q2, hA3, Function.update_of_ne q3]
      · rw [Function.update_of_ne (ne 228 229 (by decide)), hA2, Function.update_of_ne (ne 228 230 (by decide)), hA3,
          Function.update_of_ne (ne 228 231 (by decide)), hd0]
        rfl
      · rw [Function.update_self]; rfl
      · rw [Function.update_of_ne (ne 230 229 (by decide)), hA2, Function.update_self]; rfl
      · rw [Function.update_of_ne (ne 231 229 (by decide)), hA2, Function.update_of_ne (ne 231 230 (by decide)), hA3,
          Function.update_self]
        rfl
    rw [e]
    exact s.enlarge (by unfold cascCost carryCost; omega)
  rw [if_neg h1]
  have x1 : d 1 + 1 = b 1 := by have := hlt 1; omega
  set A1 := Function.update A2 (masterPort NI 229) (fb w 0) with hA1
  have hc1 := cells_update NI R A2 hc2 229 (fb w 0)
  have r1 : A2 (masterPort NI 229) = fb w (d 1) := by
    rw [hA2, Function.update_of_ne (ne 229 230 (by decide)), hA3, Function.update_of_ne (ne 229 231 (by decide)), hd1]
  have b1 : A2 (initPort NI (ix 1)) = fb w (b 1) := by rw [hA2, upd_init, hA3, upd_init, hb 1]
  have r2 : A3 (masterPort NI 230) = fb w (d 2) := by
    rw [hA3, Function.update_of_ne (ne 230 231 (by decide)), hd2]
  have b2 : A3 (initPort NI (ix 2)) = fb w (b 2) := by rw [hA3, upd_init, hb 2]
  have r0 : A1 (masterPort NI 228) = fb w (d 0) := by
    rw [hA1, Function.update_of_ne (ne 228 229 (by decide)), hA2, Function.update_of_ne (ne 228 230 (by decide)), hA3,
      Function.update_of_ne (ne 228 231 (by decide)), hd0]
  have b0 : A1 (initPort NI (ix 0)) = fb w (b 0) := by rw [hA1, upd_init, hA2, upd_init, hA3, upd_init, hb 0]
  by_cases h0 : d 0 + 1 < b 0
  · rw [if_pos h0]
    have s0 := digit_noCarry (slD NI ix 0) (slD_injective NI ix 0) (idM NI) w (d 0) (b 0) R (fun _ => 0) A1
      (ready_of NI ix w R A1 hc1 hR 0) r0 b0 h0 (hbw 0)
    have s1 := digit_carry (slD NI ix 1) (slD_injective NI ix 1) (K0 NI ix) w (d 1) (b 1) R _ (fun _ => 0) (fun _ => 0) A2 _
      (ready_of NI ix w R A2 hc2 hR 1) r1 b1 x1 (hbw 1) s0
    have s2 := digit_carry (slD NI ix 2) (slD_injective NI ix 2) (K1 NI ix) w (d 2) (b 2) R _ (fun _ => 0) (fun _ => 0) A3 _
      (ready_of NI ix w R A3 hc3 hR 2) r2 b2 x2 (hbw 2) s1
    have s := digit_carry (slD NI ix 3) (slD_injective NI ix 3) (K2 NI ix) w (d 3) (b 3) R _ (fun _ => 0) (fun _ => 0) A _
      (ready_of NI ix w R A hc hR 3) (hd 3) (hb 3) x3 (hbw 3) s2
    have e : digBank NI A w (Function.update (Function.update (Function.update (Function.update d 3 0) 2 0) 1 0) 0
        (d 0 + 1)) = Function.update A1 (masterPort NI 228) (fb w (d 0 + 1)) := by
      apply digBank_char
      · intro p q0 q1 q2 q3
        rw [Function.update_of_ne q0, hA1, Function.update_of_ne q1, hA2, Function.update_of_ne q2, hA3,
          Function.update_of_ne q3]
      · rw [Function.update_self]; rfl
      · rw [Function.update_of_ne (ne 229 228 (by decide)), hA1, Function.update_self]; rfl
      · rw [Function.update_of_ne (ne 230 228 (by decide)), hA1, Function.update_of_ne (ne 230 229 (by decide)), hA2,
          Function.update_self]
        rfl
      · rw [Function.update_of_ne (ne 231 228 (by decide)), hA1, Function.update_of_ne (ne 231 229 (by decide)), hA2,
          Function.update_of_ne (ne 231 230 (by decide)), hA3, Function.update_self]
        rfl
    rw [e]
    exact s.enlarge (by unfold cascCost carryCost; omega)
  · rw [if_neg h0]
    have x0 : d 0 + 1 = b 0 := by have := hlt 0; omega
    have si := id_step NI (fun _ => 0) (Function.update A1 (masterPort NI 228) (fb w 0))
    have s0 := digit_carry (slD NI ix 0) (slD_injective NI ix 0) (idM NI) w (d 0) (b 0) R _ (fun _ => 0) (fun _ => 0) A1 _
      (ready_of NI ix w R A1 hc1 hR 0) r0 b0 x0 (hbw 0) si
    have s1 := digit_carry (slD NI ix 1) (slD_injective NI ix 1) (K0 NI ix) w (d 1) (b 1) R _ (fun _ => 0) (fun _ => 0) A2 _
      (ready_of NI ix w R A2 hc2 hR 1) r1 b1 x1 (hbw 1) s0
    have s2 := digit_carry (slD NI ix 2) (slD_injective NI ix 2) (K1 NI ix) w (d 2) (b 2) R _ (fun _ => 0) (fun _ => 0) A3 _
      (ready_of NI ix w R A3 hc3 hR 2) r2 b2 x2 (hbw 2) s1
    have s := digit_carry (slD NI ix 3) (slD_injective NI ix 3) (K2 NI ix) w (d 3) (b 3) R _ (fun _ => 0) (fun _ => 0) A _
      (ready_of NI ix w R A hc hR 3) (hd 3) (hb 3) x3 (hbw 3) s2
    have e : digBank NI A w (fun _ => 0) = Function.update A1 (masterPort NI 228) (fb w 0) := by
      apply digBank_char
      · intro p q0 q1 q2 q3
        rw [Function.update_of_ne q0, hA1, Function.update_of_ne q1, hA2, Function.update_of_ne q2, hA3,
          Function.update_of_ne q3]
      · rw [Function.update_self]
      · rw [Function.update_of_ne (ne 229 228 (by decide)), hA1, Function.update_self]
      · rw [Function.update_of_ne (ne 230 228 (by decide)), hA1, Function.update_of_ne (ne 230 229 (by decide)), hA2,
          Function.update_self]
      · rw [Function.update_of_ne (ne 231 228 (by decide)), hA1, Function.update_of_ne (ne 231 229 (by decide)), hA2,
          Function.update_of_ne (ne 231 230 (by decide)), hA3, Function.update_self]
    rw [e]
    exact s.enlarge (by unfold cascCost carryCost; omega)

end Ports

end
end RowsConstruction.ThrSelCasc
