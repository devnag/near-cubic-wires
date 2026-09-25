import Proof.Packets.PacketsCursorFlags
import Proof.Packets.PacketsSetupR

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Cursor
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent
open NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsMeta.Keys
open NearCubicWires.PacketsGlue.CursorKit NearCubicWires.PacketsGlue.CursorChain NearCubicWires.BlockPlatform
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

variable {a : DecompositionAlgorithm}

/-! ## The stage world's layout -/

section Layout
variable (eV kE : ℕ)

/-- `0–8` metaEntry, `9–17` the nine words, `[18, 18+eV)` the vector's private tapes, `18+eV` the mask log,
then the erase log `L`, the driver `D` and `kE+1` driver counters. -/
def TS : ℕ := 9 + 9 + eV + 4 + kE
def iL : ℕ := 9 + 9 + eV + 1
def iD : ℕ := 9 + 9 + eV + 2

def tL : Fin (TS eV kE) := ⟨iL eV, by unfold TS iL; omega⟩
def tD : Fin (TS eV kE) := ⟨iD eV, by unfold TS iD; omega⟩
def tK : Fin (TS eV kE) := ⟨16, by unfold TS; omega⟩

theorem tL_val : (tL eV kE).val = iL eV := rfl
theorem tD_val : (tD eV kE).val = iD eV := rfl
theorem tK_val : (tK eV kE).val = 16 := rfl

def ι1 (j : Fin (9 + 9 + eV + 1)) : Fin (TS eV kE) := ⟨j.val, by have := j.isLt; unfold TS; omega⟩

def δv (j : ℕ) : ℕ := if j = 0 then iL eV else if j = 1 then iD eV else if j = 2 then 17 else 9 + 9 + eV + j

def δ (j : Fin (4 + kE)) : Fin (TS eV kE) :=
  ⟨δv eV j.val, by have := j.isLt; unfold δv TS iL iD; split_ifs <;> omega⟩

theorem ι1_inj : Function.Injective (ι1 eV kE) := by
  intro x y h
  have hv : (ι1 eV kE x).val = (ι1 eV kE y).val := congrArg Fin.val h
  exact Fin.ext hv

theorem δ_val (j : Fin (4 + kE)) : (δ eV kE j).val = δv eV j.val := rfl

theorem δ_inj : Function.Injective (δ eV kE) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [δ_val, δ_val] at hv
  unfold δv iL iD at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def mask1 (i : Fin (TS eV kE)) : Bool := decide (17 ≤ i.val ∧ i.val ≠ iL eV ∧ i.val ≠ iD eV)
def mask2 (i : Fin (TS eV kE)) : Bool := decide (9 ≤ i.val ∧ i.val < 17)

/-- The carry walk's tapes: ports `f+1`, flags `9+f`, cap 17, log 18 (both erased blanks). -/
def ports : NearCubicWires.PacketsGlue.CursorChain.Ports (TS eV kE) where
  port := fun f => ⟨f.val + 1, by have := f.isLt; unfold TS; omega⟩
  flag := fun f => ⟨9 + f.val, by have := f.isLt; unfold TS; omega⟩
  cap := ⟨17, by unfold TS; omega⟩
  lg := ⟨18, by unfold TS; omega⟩
  port_inj := by
    intro f g h
    have hv : f.val + 1 = g.val + 1 := congrArg Fin.val h
    exact Fin.ext (by omega)
  cap_lg := by
    intro h
    have hv : (17 : ℕ) = 18 := congrArg Fin.val h
    omega
  port_cap := by
    intro f h
    have hv : f.val + 1 = 17 := congrArg Fin.val h
    have := f.isLt
    omega
  port_lg := by
    intro f h
    have hv : f.val + 1 = 18 := congrArg Fin.val h
    have := f.isLt
    omega
  port_flag := by
    intro f g h
    have hv : f.val + 1 = 9 + g.val := congrArg Fin.val h
    have := f.isLt
    omega

end Layout

/-! ## The machine -/

section Machine
variable {base : Request → ℕ} (V : KeyVec a 9 (cursorOuts a base)) (cE kE : ℕ)

def st1 := RecoveryFocus.machine (ι1 V.extra kE) (MaskedReset.machine V.machine (fun _ => true))
def st2 := RecoveryFocus.machine (δ V.extra kE) (PacketsGlue.DriverPhase.machine cE kE)
def st3 := CloseoutWitness.SelectedErase.machine (mask1 V.extra kE) (tD V.extra kE) (tL V.extra kE)
def st4 := CloseoutRowsOriginalSwitch.machine (chainM (ports V.extra kE) thrChain).2
  (chainM (ports V.extra kE) symChain).2 (tK V.extra kE)
def st5 := CloseoutWitness.SelectedErase.machine (mask2 V.extra kE) (tD V.extra kE) (tL V.extra kE)
def st6 := RecoveryFocus.machine (fun _ : Fin 1 => tD V.extra kE) DErase.machine

/-- **The cursor's stage machine.** -/
def stageM := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (st1 V kE) (st2 V cE kE)) (st3 V kE)) (st4 V kE)) (st5 V kE)) (st6 V kE)

end Machine

/-! ## The banks -/

/-- The erase driver's length. -/
def Ev (cE kE : ℕ) (base : Request → ℕ) (r : Request) : ℕ := cE * (base r + 1) ^ (kE + 1)

section Banks
variable (a) (base : Request → ℕ) (eV kE : ℕ) (r : Request) (k : rcKey a r) (E : ℕ)

def sEntry (i : Fin (TS eV kE)) : List Bool :=
  if i.val < 9 then PacketsCombine.metaEntry a r (some k) (TS eV kE) i
  else if i.val = iL eV then List.replicate (E + 1) false else []

def s3 (i : Fin (TS eV kE)) : List Bool :=
  if i.val < 9 then PacketsCombine.metaEntry a r (some k) (TS eV kE) i
  else if i.val < 17 then cursorOuts a base (i.val - 9) r k
  else if i.val = iL eV then List.replicate (E + 1) false
  else if i.val = iD eV then List.replicate E true else List.replicate E false

def s4 (i : Fin (TS eV kE)) : List Bool :=
  if h : 1 ≤ i.val ∧ i.val ≤ 8 then
    fb (PacketsConstruction.fieldWidth a r) (PacketsGlue.succDigits a r (keyDigits a r (some k)) ⟨i.val - 1, by omega⟩)
  else s3 a base eV kE r k E i

def s5 (i : Fin (TS eV kE)) : List Bool :=
  if 9 ≤ i.val ∧ i.val < 17 then List.replicate E false else s4 a base eV kE r k E i

/-- **The stage world's exit**: input, the successor's digits, every scratch tape all-false. -/
def sExit (i : Fin (TS eV kE)) : List Bool :=
  if i.val = iD eV then List.replicate E false else s5 a base eV kE r k E i

end Banks

/-! ## Facts -/

theorem digit_fit (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) (f : Fin 8) :
    keyDigits a r (some k) f + 1 < 2 ^ PacketsConstruction.fieldWidth a r := by
  have h1 := digit_lt_bound a r (some k) (Or.inr ⟨k, hk, rfl⟩) f
  have h2 : digitBound a r < 2 ^ PacketsConstruction.fieldWidth a r :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  omega

theorem cursorOuts_len (base : Request → ℕ) (j : ℕ) (hj : j < 8) (r : Request) (k : rcKey a r) :
    (cursorOuts a base j r k).length ≤ 1 := by
  unfold cursorOuts
  split_ifs with h h7
  · simp only [List.length_replicate]; exact carryV_le _ _
  · simp only [List.length_replicate]; cases r <;> simp [thrFlag]
  · omega

theorem cursorOuts_kind (base : Request → ℕ) (r : Request) (k : rcKey a r) :
    cursorOuts a base 7 r k = List.replicate (thrFlag r) true := by
  simp [cursorOuts]

theorem cursorOuts_src (base : Request → ℕ) (r : Request) (k : rcKey a r) :
    cursorOuts a base 8 r k = List.replicate (base r + 1) true := by
  simp [cursorOuts]

theorem thrFlag_le (r : Request) : thrFlag r ≤ 1 := by cases r <;> simp [thrFlag]

theorem chain_mem (r : Request) (f : Fin 8) (hf : f ∈ chainOf r) : f.val < 7 := by
  unfold chainOf at hf
  split_ifs at hf
  · simp only [thrChain, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [symChain, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> decide

end
end NearCubicWires.PacketsConstruction.Cursor
