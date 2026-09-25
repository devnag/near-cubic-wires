import Proof.SourceAssembly.SourceFactorSelModes

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.DescF
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierPipeline SourceInterfaces
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest
open Desc (Kind gdesc cp sysW sysCost dT copy_step pad_nil read_true read_blank stop_step sys_run flagS flagO)
open Modes (kindOf bmOf bitsOf thr_descAt sym_descAt tape_length)
noncomputable section

/-! ## The machine -/

/-- The original writer, framed input: `RepairOrdinary.frame bits` (port 3) → 4, 9; template → 5, 10; `1^P` → 6, 11;
`1^W` → 7, 12; `1^L` → 8, 13; flag O → 15. -/
def origWF := Composition.machine (cp 3 15) (Composition.machine (cp 4 16) (Composition.machine (cp 5 17)
  (Composition.machine (cp 6 18) (Composition.machine (cp 7 19) (Composition.machine (cp 3 20)
  (Composition.machine (cp 4 21) (Composition.machine (cp 5 22) (Composition.machine (cp 6 23)
  (Composition.machine (cp 7 24) (cp 1 26))))))))))

/-- **The descriptor writer (framed code)**: flag S → systematic writer; else flag O → original writer; else stop. -/
def machine := CloseoutRowsOriginalSwitch.machine sysW
  (CloseoutRowsOriginalSwitch.machine origWF (CloseoutRowsOriginalSwitch.stop 27) (1 : Fin 27)) (0 : Fin 27)

def origCostF (D : Nat) : Nat := 11 * (2 * D + 4) + 10

def costF : Kind → Nat → Nat
  | .absent, _ => 0 + 2 + 2
  | .sys, D => sysCost D + 2
  | .orig, D => origCostF D + 2 + 2

theorem origF_run (tpl uP uW uL bits : List Bool) (Qf Qc Qt Qp Qw Ql Qd D C R : Nat)
    (E : Fin 27 → List Bool)
    (h1E : E 1 = ZeroPadding.pad Qf [true]) (h3E : E 3 = ZeroPadding.pad Qc (RepairOrdinary.frame bits))
    (h4 : E 4 = ZeroPadding.pad Qt tpl) (h5 : E 5 = ZeroPadding.pad Qp uP)
    (h6 : E 6 = ZeroPadding.pad Qw uW) (h7 : E 7 = ZeroPadding.pad Ql uL)
    (h9 : E 9 = ZeroPadding.pad Qd (List.replicate D true))
    (h10 : E 10 = List.replicate C false) (hout : ∀ j : Fin 27, 11 ≤ j.val → E j = List.replicate R false)
    (hfr : (RepairOrdinary.frame bits).length ≤ D)
    (htpl : tpl.length ≤ D) (huP : uP.length ≤ D) (huW : uW.length ≤ D) (huL : uL.length ≤ D)
    (h1 : 1 ≤ D) (hDR : D ≤ R) (hC : D + 1 ≤ C) :
    Step origWF (origCostF D) (fun _ => 0) E (fun _ => 0)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update E
        15 (ZeroPadding.pad R (RepairOrdinary.frame bits))) 16 (ZeroPadding.pad R tpl)) 17 (ZeroPadding.pad R uP))
        18 (ZeroPadding.pad R uW)) 19 (ZeroPadding.pad R uL)) 20 (ZeroPadding.pad R (RepairOrdinary.frame bits)))
        21 (ZeroPadding.pad R tpl)) 22 (ZeroPadding.pad R uP)) 23 (ZeroPadding.pad R uW))
        24 (ZeroPadding.pad R uL)) 26 (ZeroPadding.pad R [true])) := by
  set E1 := Function.update E 15 (ZeroPadding.pad R (RepairOrdinary.frame bits)) with hE1
  set E2 := Function.update E1 16 (ZeroPadding.pad R tpl) with hE2
  set E3 := Function.update E2 17 (ZeroPadding.pad R uP) with hE3
  set E4 := Function.update E3 18 (ZeroPadding.pad R uW) with hE4
  set E5 := Function.update E4 19 (ZeroPadding.pad R uL) with hE5
  set E6 := Function.update E5 20 (ZeroPadding.pad R (RepairOrdinary.frame bits)) with hE6
  set E7 := Function.update E6 21 (ZeroPadding.pad R tpl) with hE7
  set E8 := Function.update E7 22 (ZeroPadding.pad R uP) with hE8
  set E9 := Function.update E8 23 (ZeroPadding.pad R uW) with hE9
  set E10 := Function.update E9 24 (ZeroPadding.pad R uL) with hE10
  have s1 := copy_step (3 : Fin 27) 15 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qc Qd D C R (RepairOrdinary.frame bits) hfr hDR hC (fun _ => 0) E rfl rfl rfl rfl h3E
    (hout 15 (by decide)) h9 h10
  have s2 := copy_step (4 : Fin 27) 16 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qt Qd D C R tpl htpl hDR hC (fun _ => 0) E1 rfl rfl rfl rfl
    (by simp [E1, h4]) (by simp [E1, hout 16 (by decide)]) (by simp [E1, h9]) (by simp [E1, h10])
  have s3 := copy_step (5 : Fin 27) 17 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qp Qd D C R uP huP hDR hC (fun _ => 0) E2 rfl rfl rfl rfl
    (by simp [E1, E2, h5]) (by simp [E1, E2, hout 17 (by decide)]) (by simp [E1, E2, h9])
    (by simp [E1, E2, h10])
  have s4 := copy_step (6 : Fin 27) 18 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qw Qd D C R uW huW hDR hC (fun _ => 0) E3 rfl rfl rfl rfl
    (by simp [E1, E2, E3, h6]) (by simp [E1, E2, E3, hout 18 (by decide)]) (by simp [E1, E2, E3, h9])
    (by simp [E1, E2, E3, h10])
  have s5 := copy_step (7 : Fin 27) 19 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Ql Qd D C R uL huL hDR hC (fun _ => 0) E4 rfl rfl rfl rfl
    (by simp [E1, E2, E3, E4, h7]) (by simp [E1, E2, E3, E4, hout 19 (by decide)])
    (by simp [E1, E2, E3, E4, h9]) (by simp [E1, E2, E3, E4, h10])
  have s6 := copy_step (3 : Fin 27) 20 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qc Qd D C R (RepairOrdinary.frame bits) hfr hDR hC (fun _ => 0) E5 rfl rfl rfl rfl
    (by simp [E1, E2, E3, E4, E5, h3E]) (by simp [E1, E2, E3, E4, E5, hout 20 (by decide)])
    (by simp [E1, E2, E3, E4, E5, h9]) (by simp [E1, E2, E3, E4, E5, h10])
  have s7 := copy_step (4 : Fin 27) 21 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qt Qd D C R tpl htpl hDR hC (fun _ => 0) E6 rfl rfl rfl rfl
    (by simp [E1, E2, E3, E4, E5, E6, h4]) (by simp [E1, E2, E3, E4, E5, E6, hout 21 (by decide)])
    (by simp [E1, E2, E3, E4, E5, E6, h9]) (by simp [E1, E2, E3, E4, E5, E6, h10])
  have s8 := copy_step (5 : Fin 27) 22 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qp Qd D C R uP huP hDR hC (fun _ => 0) E7 rfl rfl rfl rfl
    (by simp [E1, E2, E3, E4, E5, E6, E7, h5])
    (by simp [E1, E2, E3, E4, E5, E6, E7, hout 22 (by decide)])
    (by simp [E1, E2, E3, E4, E5, E6, E7, h9]) (by simp [E1, E2, E3, E4, E5, E6, E7, h10])
  have s9 := copy_step (6 : Fin 27) 23 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qw Qd D C R uW huW hDR hC (fun _ => 0) E8 rfl rfl rfl rfl
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, h6])
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, hout 23 (by decide)])
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, h9]) (by simp [E1, E2, E3, E4, E5, E6, E7, E8, h10])
  have s10 := copy_step (7 : Fin 27) 24 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Ql Qd D C R uL huL hDR hC (fun _ => 0) E9 rfl rfl rfl rfl
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, E9, h7])
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, E9, hout 24 (by decide)])
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, E9, h9])
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, E9, h10])
  have s11 := copy_step (1 : Fin 27) 26 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qf Qd D C R [true] (by simpa using h1) hDR hC (fun _ => 0) E10 rfl rfl rfl rfl
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, h1E])
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, hout 26 (by decide)])
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, h9])
    (by simp [E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, h10])
  have hall : Step origWF _ _ _ _ _ := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq
    (s9.seq (s10.seq s11)))))))))
  exact hall.enlarge (by unfold origCostF; omega)

/-- **The descriptor writer (framed code), local form.** As `Desc.run`, with the original slot's FRAMED code
word on port 3 (`|RepairOrdinary.frame bits| ≤ D`) and no `1^|bits|` port. -/
theorem run (k : Kind) (tpl uP uW uL bm bits : List Bool) (Qf Qb Qc Qt Qp Qw Ql Qd D C R : Nat)
    (E : Fin 27 → List Bool)
    (hfS : E 0 = ZeroPadding.pad Qf (flagS k)) (hfO : E 1 = ZeroPadding.pad Qf (flagO k))
    (hsys : k = .sys → E 2 = ZeroPadding.pad Qb bm ∧ bm.length ≤ D)
    (horig : k = .orig → E 3 = ZeroPadding.pad Qc (RepairOrdinary.frame bits) ∧ (RepairOrdinary.frame bits).length ≤ D)
    (h4 : E 4 = ZeroPadding.pad Qt tpl) (h5 : E 5 = ZeroPadding.pad Qp uP)
    (h6 : E 6 = ZeroPadding.pad Qw uW) (h7 : E 7 = ZeroPadding.pad Ql uL)
    (h9 : E 9 = ZeroPadding.pad Qd (List.replicate D true))
    (h10 : E 10 = List.replicate C false) (hout : ∀ j : Fin 27, 11 ≤ j.val → E j = List.replicate R false)
    (htpl : tpl.length ≤ D) (huP : uP.length ≤ D) (huW : uW.length ≤ D) (huL : uL.length ≤ D)
    (h1 : 1 ≤ D) (hDR : D ≤ R) (hC : D + 1 ≤ C) :
    ∃ E' : Fin 27 → List Bool,
      Step machine (costF k D) (fun _ => 0) E (fun _ => 0) E' ∧
      (∀ n : Fin 16, E' (dT n) = ZeroPadding.pad R (gdesc tpl uP uW uL bm bits k n.val)) ∧
      (∀ j : Fin 27, j.val < 11 → E' j = E j) := by
  cases k with
  | absent =>
    have hs : Step machine (0 + 2 + 2) (fun _ => 0) E (fun _ => 0) E :=
      CloseoutRowsOriginalSwitch.false_run _ _ _
        (CloseoutRowsOriginalSwitch.false_run _ _ _ (stop_step E) (by rw [hfO]; exact read_blank Qf))
        (by rw [hfS]; exact read_blank Qf)
    refine ⟨E, hs, ?_, fun _ _ => rfl⟩
    intro n
    rw [hout (dT n) (by simp [dT])]
    exact (pad_nil R).symm
  | sys =>
    obtain ⟨h2, hbm⟩ := hsys rfl
    have hw := sys_run tpl bm Qf Qb Qt Qd D C R E hfS h2 h4 h9 h10 hout hbm htpl h1 hDR hC
    have hs : Step machine (sysCost D + 2) (fun _ => 0) E (fun _ => 0) _ :=
      CloseoutRowsOriginalSwitch.true_run _ _ _ hw (by rw [hfS]; exact read_true Qf)
    refine ⟨_, hs, ?_, ?_⟩
    · intro n
      fin_cases n <;> simp [dT, gdesc, pad_nil] <;> exact hout _ (by decide)
    · intro j hj
      simp only [Function.update_apply]
      have hne : ∀ c : Fin 27, 11 ≤ c.val → j ≠ c := fun c hc e => by rw [e] at hj; omega
      simp [hne 25 (by decide), hne 14 (by decide), hne 13 (by decide), hne 12 (by decide),
        hne 11 (by decide)]
  | orig =>
    obtain ⟨h3E, hfr⟩ := horig rfl
    have hw := origF_run tpl uP uW uL bits Qf Qc Qt Qp Qw Ql Qd D C R E hfO h3E h4 h5 h6 h7 h9 h10
      hout hfr htpl huP huW huL h1 hDR hC
    have hs : Step machine (origCostF D + 2 + 2) (fun _ => 0) E (fun _ => 0) _ :=
      CloseoutRowsOriginalSwitch.false_run _ _ _
        (CloseoutRowsOriginalSwitch.true_run _ _ _ hw (by rw [hfO]; exact read_true Qf))
        (by rw [hfS]; exact read_blank Qf)
    refine ⟨_, hs, ?_, ?_⟩
    · intro n
      fin_cases n <;> simp [dT, gdesc, pad_nil] <;> exact hout _ (by decide)
    · intro j hj
      simp only [Function.update_apply]
      have hne : ∀ c : Fin 27, 11 ≤ c.val → j ≠ c := fun c hc e => by rw [e] at hj; omega
      simp [hne 26 (by decide), hne 24 (by decide), hne 23 (by decide), hne 22 (by decide),
        hne 21 (by decide), hne 20 (by decide), hne 19 (by decide), hne 18 (by decide),
        hne 17 (by decide), hne 16 (by decide), hne 15 (by decide)]

/-- **The descriptor writer (framed code), docked** by an injective `sl : Fin 27 → Fin U` (ports as `Desc.slot_step`;
port `sl 3` holds the framed code word, `sl 8` is not read). -/
theorem slot_step {U : Nat} (sl : Fin 27 → Fin U) (hsl : Function.Injective sl)
    (k : Kind) (tpl uP uW uL bm bits : List Bool) (Qf Qb Qc Qt Qp Qw Ql Qd D C R : Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hfS : A (sl 0) = ZeroPadding.pad Qf (flagS k)) (hfO : A (sl 1) = ZeroPadding.pad Qf (flagO k))
    (hsys : k = .sys → A (sl 2) = ZeroPadding.pad Qb bm ∧ bm.length ≤ D)
    (horig : k = .orig → A (sl 3) = ZeroPadding.pad Qc (RepairOrdinary.frame bits) ∧ (RepairOrdinary.frame bits).length ≤ D)
    (h4 : A (sl 4) = ZeroPadding.pad Qt tpl) (h5 : A (sl 5) = ZeroPadding.pad Qp uP)
    (h6 : A (sl 6) = ZeroPadding.pad Qw uW) (h7 : A (sl 7) = ZeroPadding.pad Ql uL)
    (h9 : A (sl 9) = ZeroPadding.pad Qd (List.replicate D true))
    (h10 : A (sl 10) = List.replicate C false)
    (hout : ∀ n : Fin 16, A (sl (dT n)) = List.replicate R false)
    (htpl : tpl.length ≤ D) (huP : uP.length ≤ D) (huW : uW.length ≤ D) (huL : uL.length ≤ D)
    (h1 : 1 ≤ D) (hDR : D ≤ R) (hC : D + 1 ≤ C) :
    ∃ A' : Fin U → List Bool,
      Step (RecoveryFocus.machine sl machine) (costF k D) H A H A' ∧
      (∀ n : Fin 16, A' (sl (dT n)) = ZeroPadding.pad R (gdesc tpl uP uW uL bm bits k n.val)) ∧
      (∀ x, (∀ n : Fin 16, sl (dT n) ≠ x) → A' x = A x) := by
  have hout' : ∀ j : Fin 27, 11 ≤ j.val → A (sl j) = List.replicate R false := by
    intro j hj
    have e : j = dT ⟨j.val - 11, by omega⟩ := Fin.ext (by simp [dT]; omega)
    rw [e]
    exact hout _
  obtain ⟨E', hs, hE, hkeep⟩ := run k tpl uP uW uL bm bits Qf Qb Qc Qt Qp Qw Ql Qd D C R
    (fun j => A (sl j)) hfS hfO hsys horig h4 h5 h6 h7 h9 h10 hout' htpl huP huW huL h1 hDR hC
  have d := hs.dock sl hsl H A (fun j => hH j) (fun j => rfl)
  rw [dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, fun n => by rw [install_slot sl hsl]; exact hE n, ?_⟩
  intro x hx
  by_cases hp : ∃ j, sl j = x
  · obtain ⟨j, rfl⟩ := hp
    rw [install_slot sl hsl]
    have hj : j.val < 11 := by
      by_contra hc
      exact hx ⟨j.val - 11, by omega⟩ (congrArg sl (Fin.ext (by simp [dT]; omega)))
    exact hkeep j hj
  · exact install_other sl A E' x (fun j e => hp ⟨j, e⟩)

/-! ## Per mode -/

section

end


end
end NearCubicWires.SourceFactorSel.DescF
