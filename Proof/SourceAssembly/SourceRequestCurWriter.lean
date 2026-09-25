import Proof.SourceAssembly.SourceRequestCurContract

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.CurWriter
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp
noncomputable section

inductive Wr where
  | c (d : Fin 128) (w : List Bool)
  | cp (a d : Fin 128) (n : Nat)

/-- A write's machine shape (the copy's value `n` is data, not part of the machine). -/
inductive WrS where
  | c (d : Fin 128) (w : List Bool)
  | cp (a d : Fin 128)

def Wr.shape : Wr → WrS
  | .c d w => .c d w
  | .cp a d _ => .cp a d

def WrS.mach : WrS → (Σ s, Machine 128 s)
  | .c d w => ⟨_, constM w d 5⟩
  | .cp a d => ⟨_, copyM a d 5⟩

def Wr.cost : Wr → Nat
  | .c _ w => 2 * w.length + 2
  | .cp _ _ n => 2 * n + 4

def Wr.dst : Wr → Fin 128
  | .c d _ => d
  | .cp _ d _ => d

def Wr.out (S : Nat) : Wr → List Bool
  | .c _ w => ZeroPadding.pad S w
  | .cp _ _ n => ZeroPadding.pad S (List.replicate n true)

def Wr.app (S : Nat) (x : Wr) (A : Fin 128 → List Bool) : Fin 128 → List Bool :=
  Function.update A x.dst (x.out S)

/-- One write's preconditions (destination blank at `S`, source holding its unary word, log size). -/
def Wr.Pre (S C : Nat) (A : Fin 128 → List Bool) : Wr → Prop
  | .c d w => d ≠ 5 ∧ w.length ≤ C ∧ A d = List.replicate S false
  | .cp a d n => a ≠ d ∧ a ≠ 5 ∧ d ≠ 5 ∧ n + 1 ≤ C ∧
      (∃ Qa, A a = ZeroPadding.pad Qa (List.replicate n true)) ∧ A d = List.replicate S false

def chainM : List WrS → (Σ s, Machine 128 s)
  | [] => ⟨_, CloseoutRowsOriginalSwitch.stop 128⟩
  | x :: xs => ⟨_, Composition.machine x.mach.2 (chainM xs).2⟩

def chainCost : List Wr → Nat
  | [] => 0
  | x :: xs => x.cost + 1 + chainCost xs

def chainApp (S : Nat) : List Wr → (Fin 128 → List Bool) → (Fin 128 → List Bool)
  | [], A => A
  | x :: xs, A => chainApp S xs (x.app S A)

def ChainPre (S C : Nat) : List Wr → (Fin 128 → List Bool) → Prop
  | [], _ => True
  | x :: xs, A => x.Pre S C A ∧ ChainPre S C xs (x.app S A)

theorem Wr.pre_log {S C : Nat} {A : Fin 128 → List Bool} {x : Wr} (h : x.Pre S C A) : x.dst ≠ 5 := by
  cases x with
  | c d w => exact h.1
  | cp a d n => exact h.2.2.1

theorem Wr.step (S C : Nat) (x : Wr) (A : Fin 128 → List Bool) (hl : A 5 = List.replicate C false)
    (hp : x.Pre S C A) : Step x.shape.mach.2 x.cost (fun _ => 0) A (fun _ => 0) (x.app S A) := by
  cases x with
  | c d w =>
    obtain ⟨h5, hw, hd⟩ := hp
    exact const_step w d 5 h5 S C hw (fun _ => 0) A rfl rfl hd hl
  | cp a d n =>
    obtain ⟨had, ha5, hd5, hn, ⟨Qa, ha⟩, hd⟩ := hp
    exact copy_step a d 5 had ha5 hd5 n Qa S C hn (fun _ => 0) A (fun _ _ => rfl) ha hd hl

theorem chain_step (S C : Nat) (ws : List Wr) (A : Fin 128 → List Bool) (hl : A 5 = List.replicate C false)
    (hp : ChainPre S C ws A) :
    Step (chainM (ws.map Wr.shape)).2 (chainCost ws) (fun _ => 0) A (fun _ => 0) (chainApp S ws A) := by
  induction ws generalizing A with
  | nil => exact ⟨_, rfl, rfl, rfl, le_refl _⟩
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := hp
    have s1 := Wr.step S C x A hl hx
    have hl' : x.app S A 5 = List.replicate C false := by
      unfold Wr.app; rw [Function.update_of_ne (Ne.symm (Wr.pre_log hx))]; exact hl
    exact s1.seq (ih (x.app S A) hl' hxs)

/-- Ports no write touches keep their value. -/
theorem chainApp_other (S : Nat) (ws : List Wr) (A : Fin 128 → List Bool) (z : Fin 128)
    (hz : ∀ x ∈ ws, x.dst ≠ z) : chainApp S ws A z = A z := by
  induction ws generalizing A with
  | nil => rfl
  | cons x xs ih =>
    show chainApp S xs (x.app S A) z = A z
    rw [ih (x.app S A) (fun y hy => hz y (List.mem_cons_of_mem x hy))]
    unfold Wr.app
    exact Function.update_of_ne (Ne.symm (hz x List.mem_cons_self)) _ _

end
end NearCubicWires.SourceRequest.CurWriter

