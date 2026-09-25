import Proof.MachineModel.Layout

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceSkeleton.InitMove

/-- SI's tape `v` ↦ S's tape. -/
def piV (b X NR v : Nat) : Nat :=
  if v < b then v
  else if v < b + 3 then v + NR + X
  else if v < b + 3 + X then v + NR - 3
  else if v < b + 3 + X + NR then v - 3 - X
  else v

/-- S's tape `v` ↦ SI's tape (the inverse). -/
def rhoV (b X NR v : Nat) : Nat :=
  if v < b then v
  else if v < b + NR then v + 3 + X
  else if v < b + NR + X then v + 3 - NR
  else if v < b + NR + X + 3 then v - NR - X
  else v

section vals
variable (b X NR : Nat)

theorem rho_pi (v : Nat) : rhoV b X NR (piV b X NR v) = v := by
  unfold piV rhoV; split_ifs <;> omega

theorem pi_rho (v : Nat) : piV b X NR (rhoV b X NR v) = v := by
  unfold piV rhoV; split_ifs <;> omega

theorem piV_lt (T v : Nat) (hv : v < T) (hT : b + 3 + X + NR ≤ T) : piV b X NR v < T := by
  unfold piV; split_ifs <;> omega

theorem rhoV_lt (T v : Nat) (hv : v < T) (hT : b + 3 + X + NR ≤ T) : rhoV b X NR v < T := by
  unfold rhoV; split_ifs <;> omega

/-- Off the block, both maps are the identity. -/
theorem piV_fix (v : Nat) (h : v < b ∨ b + 3 + X + NR ≤ v) : piV b X NR v = v := by
  unfold piV; split_ifs <;> omega

theorem rhoV_fix (v : Nat) (h : v < b ∨ b + 3 + X + NR ≤ v) : rhoV b X NR v = v := by
  unfold rhoV; split_ifs <;> omega

/-- S's resident `b + i` (`i < NR`) is SI's `zT i = b + 3 + X + i`. -/
theorem rhoV_res (v : Nat) (h1 : b ≤ v) (h2 : v < b + NR) : rhoV b X NR v = v + 3 + X := by
  unfold rhoV; split_ifs <;> omega

/-- S's workspace `b + NR + j` (`j < X`) is SI's workspace `b + 3 + j`. -/
theorem rhoV_ws (v : Nat) (h1 : b + NR ≤ v) (h2 : v < b + NR + X) : rhoV b X NR v = v + 3 - NR := by
  unfold rhoV; split_ifs <;> omega

/-- S's `b + NR + X + j` (`j < 3`) is SI's unused `b + j`. -/
theorem rhoV_u (v : Nat) (h1 : b + NR + X ≤ v) (h2 : v < b + NR + X + 3) : rhoV b X NR v = v - NR - X := by
  unfold rhoV; split_ifs <;> omega

theorem piV_mem (lo hi v : Nat) (hlo : lo ≤ b) (hhi : b + 3 + X + NR ≤ hi) (h1 : lo ≤ v) (h2 : v < hi) :
    lo ≤ piV b X NR v ∧ piV b X NR v < hi := by
  unfold piV; split_ifs <;> omega

end vals

variable (b X NR T : Nat) (hT : b + 3 + X + NR ≤ T)

/-- The slot map of the relocation (SI's tape ↦ S's tape). -/
def piF : Fin T → Fin T := fun x => ⟨piV b X NR x.val, piV_lt b X NR T x.val x.isLt hT⟩

/-- Its inverse (S's tape ↦ SI's tape). -/
def rhoF : Fin T → Fin T := fun x => ⟨rhoV b X NR x.val, rhoV_lt b X NR T x.val x.isLt hT⟩

theorem rhoF_val (x : Fin T) : (rhoF b X NR T hT x).val = rhoV b X NR x.val := rfl

theorem piF_rhoF (y : Fin T) : piF b X NR T hT (rhoF b X NR T hT y) = y :=
  Fin.ext (pi_rho b X NR y.val)

theorem rhoF_piF (x : Fin T) : rhoF b X NR T hT (piF b X NR T hT x) = x :=
  Fin.ext (rho_pi b X NR x.val)

theorem piF_injective : Function.Injective (piF b X NR T hT) := by
  intro x y h
  have := congrArg (rhoF b X NR T hT) h
  rwa [rhoF_piF, rhoF_piF] at this

/-- **The relocation.** A run of `M` on the SI-placed bank `(H ∘ piF, A ∘ piF)` is a run of the relocated machine on `(H, A)`
at the same cost; its exit is SI's exit read through `rhoF`. -/
theorem relocate {s : Nat} {M : Machine T s} {n : Nat} {H : Fin T → Nat} {A : Fin T → List Bool}
    {H1 : Fin T → Nat} {A1 : Fin T → List Bool}
    (h : Step M n (fun x => H (piF b X NR T hT x)) (fun x => A (piF b X NR T hT x)) H1 A1) :
    Step (RecoveryFocus.machine (piF b X NR T hT) M) n H A
      (fun y => H1 (rhoF b X NR T hT y)) (fun y => A1 (rhoF b X NR T hT y)) := by
  have hd := h.dock (piF b X NR T hT) (piF_injective b X NR T hT) H A (fun _ => rfl) (fun _ => rfl)
  refine hd.congr ?_ ?_
  · funext y
    have e := dockH_slot (piF b X NR T hT) (piF_injective b X NR T hT) H H1 (rhoF b X NR T hT y)
    rwa [piF_rhoF] at e
  · funext y
    have e := install_slot (piF b X NR T hT) (piF_injective b X NR T hT) A A1 (rhoF b X NR T hT y)
    rwa [piF_rhoF] at e

end NearCubicWires.SourceSkeleton.InitMove
end
