import Proof.Rows.RowsCellReload

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CellGeneric
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction.CellReload
noncomputable section

def reusable {s : Nat} (V : Machine 254 s) :=
  Composition.machine (TapeEmbedding.machine 3 V) PCJ45bee56da9f34d5a_VerdictFinish.machine

theorem reusable_run {s n : Nat} {V : Machine 254 s} {H J : Fin 254 → ℕ} {A B : Fin 254 → List Bool}
    (h : Step V n H A J B) (R : Nat) (out : List Bool) (b : Bool)
    (hH : ∀ i, H i ≤ 1) (hA : ∀ i, (A i).length ≤ R) (hn : n+2 ≤ R) (hJ : J 253 = 0)
    (hbit : readTapeBit (B 253) 0 = b) :
    Step (reusable V) (n+4*R+12)
      (PCJ45bee56da9f34d5a_VerdictFinish.heads H out.length)
      (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun i => ZeroPadding.pad R (A i)) R out)
      (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) (out++[b]).length)
      (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R (out++[b])) := by
  obtain ⟨hJR, hBR⟩ := PCJ45bee56da9f34d5a_VerdictFinish.bounds h R hH hA hn
  have padded : ∀ i, (ZeroPadding.pad R (B i)).length ≤ R := by
    intro i
    rw [ZeroPadding.pad_length]
    exact max_le (le_refl _) (hBR i)
  have bit : readTapeBit (ZeroPadding.pad R (B 253)) 0 = b := by
    rw [ZeroPadding.read_pad]
    exact hbit
  have one := (h.pad (fun _ => R)).embed (![0, 0, out.length] : Fin 3 → ℕ)
    (![List.replicate R true, List.replicate (R+1) false, out] : Fin 3 → List Bool)
  have two := PCJ45bee56da9f34d5a_VerdictFinish.run J (fun i => ZeroPadding.pad R (B i)) R out b hJ bit hJR
    padded
  have all := one.seq two
  rw [show n+1+(4*R+11) = n+4*R+12 by omega] at all
  exact all

/-! ## Heads to an arbitrary `H0 ≤ 1` in one step -/

def cellDirs (H0 : Fin 254 → ℕ) : Fin 257 → HeadMove :=
  Fin.addCases (m:=254) (n:=3) (motive := fun _ => HeadMove)
    (fun i => if H0 i = 1 then HeadMove.right else HeadMove.stay) (fun _ => HeadMove.stay)

def dirs (H0 : Fin 254 → ℕ) : Fin CT → HeadMove := layout (cellDirs H0) (fun _ => HeadMove.stay)

def advanceTo (H0 : Fin 254 → ℕ) := DecompositionCountPosition.move (dirs H0)

theorem advanceTo_step (H0 : Fin 254 → ℕ) (hle : ∀ i, H0 i ≤ 1) (len : Nat) (A : Fin CT → List Bool) :
    Step (advanceTo H0) 1
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) len) (fun _ => 0)) A
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.heads H0 len) (fun _ => 0)) A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run (dirs H0)
    (layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) len) (fun _ => 0)) A
  refine Step.of_run hr ?_ (by rw [hf])
  rw [hf]
  funext x
  refine cover (motive := fun x => (dirs H0 x).apply
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) len) (fun _ => 0) x) =
    layout (PCJ45bee56da9f34d5a_VerdictFinish.heads H0 len) (fun _ => 0) x)
    (fun i => ?_) (fun k => ?_) x
  · simp only [dirs, layout_cell]
    refine Fin.addCases (m:=254) (n:=3) (motive := fun i =>
      (cellDirs H0 i).apply (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) len i) =
      PCJ45bee56da9f34d5a_VerdictFinish.heads H0 len i) (fun c => ?_) (fun c => ?_) i
    · simp only [cellDirs, PCJ45bee56da9f34d5a_VerdictFinish.heads, Fin.addCases_left]
      have hle' := hle c
      by_cases h1 : H0 c = 1
      · rw [if_pos h1, h1]; rfl
      · rw [if_neg h1]
        change 0 = _
        omega
    · simp only [cellDirs, PCJ45bee56da9f34d5a_VerdictFinish.heads, Fin.addCases_right]
      rfl
  · simp only [dirs, layout_master]
    rfl

/-! ## The generic reloadable cell -/

/-- **The fixed per-cell machine for verdict machine `V` with start heads `H0`.** -/
def cellMachine {s : Nat} (V : Machine 254 s) (H0 : Fin 254 → ℕ) :=
  Composition.machine fanStage
    (Composition.machine (advanceTo H0) (TapeEmbedding.machine 254 (reusable V)))

/-- **One cell from resident masters, any verdict machine.** The loop invariant of
`RowsCellReload.cell_step`, with the verdict machine's run as the only hypothesis. -/
theorem cell_step {s : Nat} (V : Machine 254 s) (H0 : Fin 254 → ℕ) (hle : ∀ i, H0 i ≤ 1)
    (R : Nat) (out : List Bool) (M A0 : Fin 254 → List Bool) (n : Nat) (J : Fin 254 → ℕ)
    (B : Fin 254 → List Bool) (b : Bool) (h : Step V n H0 A0 J B) (hJ : J 253 = 0)
    (hbit : readTapeBit (B 253) 0 = b) (hMl : ∀ i, (M i).length ≤ R)
    (hM : ∀ i, ZeroPadding.pad R (M i) = ZeroPadding.pad R (A0 i)) (hn : n+2 ≤ R) :
    Step (cellMachine V H0) (2*R+4+1+(1+1+(n+4*R+12)))
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) out.length) (fun _ => 0))
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out) M)
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) (out++[b]).length) (fun _ => 0))
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R (out++[b])) M) := by
  have hA0 : ∀ i, (A0 i).length ≤ R := by
    intro i
    have h' := congrArg List.length (hM i)
    rw [ZeroPadding.pad_length, ZeroPadding.pad_length, max_eq_left (hMl i)] at h'
    omega
  have s1 := fan_step R out M hMl
  rw [show (fun i => ZeroPadding.pad R (M i)) = (fun i => ZeroPadding.pad R (A0 i)) from funext hM] at s1
  have s2 := advanceTo_step H0 hle out.length
    (layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun i => ZeroPadding.pad R (A0 i)) R out) M)
  have s3 := (reusable_run h R out b hle hA0 hn hJ hbit).embed (fun _ : Fin 254 => 0) M
  exact s1.seq (s2.seq s3)

end
end RowsConstruction.CellGeneric
