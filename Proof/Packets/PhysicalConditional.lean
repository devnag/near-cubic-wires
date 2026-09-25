import Proof.Amplification.RecoveryCursorCalls

/-! Execute a fixed continuation exactly when the first machine's actual
terminal control accepts. Both return transitions are paid. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.PhysicalConditional
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound

def sizes (a b : Nat) : Fin 2 → Nat := ![a,b]
def programs {t a b : Nat} (p : Machine t a) (q : Machine t b) :
    (j : Fin 2) → Machine t (sizes a b j)
  | 0 => p
  | 1 => q
def next {t a b : Nat} (accept : Fin a → Bool) :
    (j : Fin 2) → Fin (sizes a b j) → (Fin t → Bool) → Option (Fin 2)
  | 0, state, _ => if accept state then some 1 else none
  | 1, _, _ => none
noncomputable def machine {t a b : Nat} (p : Machine t a) (q : Machine t b) (accept : Fin a → Bool) :=
  RecoveryCalls.machine (sizes a b) (programs p q) 0 (next accept)

theorem accepted {t a b : Nat} (p : Machine t a) (q : Machine t b) (accept : Fin a → Bool)
    (pfuel qfuel : Nat) (heads : Fin t → Nat) (data : Fin t → List Bool)
    (prior : ExecutionReceipt t a) (last : ExecutionReceipt t b)
    (hp : runFrom p pfuel ⟨p.start,heads,data⟩=some prior)
    (hq : runFrom q qfuel ⟨q.start,prior.final.heads,prior.final.tapes⟩=some last)
    (ha : accept prior.final.control=true) :
    ∃ actual, runFrom (machine p q accept) (pfuel+1+qfuel+1)
      ⟨(machine p q accept).start,heads,data⟩=some actual ∧
      actual.steps≤pfuel+1+qfuel+1 ∧
      actual.final.heads=last.final.heads ∧ actual.final.tapes=last.final.tapes := by
  obtain ⟨u,hu,first⟩ := call_receipt (sizes a b) (programs p q) 0 (next accept) 0 1 pfuel _ prior hp (by
    change (if accept prior.final.control then some (1 : Fin 2) else none)=some 1
    rw [ha]; rfl)
  obtain ⟨v,hv,tail⟩ := stop_receipt (sizes a b) (programs p q) 0 (next accept) 1 qfuel _ last hq rfl
  obtain ⟨actual,hr,hf,hs⟩ := (first.trans tail).run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have bound : u+v≤pfuel+1+qfuel+1 := by omega
  have more := runFrom_moreFuel (machine p q accept) (u+v) (pfuel+1+qfuel+1-(u+v)) _ actual hr
  rw [Nat.add_sub_of_le bound] at more
  exact ⟨actual,more,hs.le.trans bound,by rw [hf]; rfl,by rw [hf]; rfl⟩

theorem rejected {t a b : Nat} (p : Machine t a) (q : Machine t b) (accept : Fin a → Bool)
    (fuel : Nat) (heads : Fin t → Nat) (data : Fin t → List Bool)
    (prior : ExecutionReceipt t a)
    (hp : runFrom p fuel ⟨p.start,heads,data⟩=some prior)
    (ha : accept prior.final.control=false) :
    ∃ actual, runFrom (machine p q accept) (fuel+1)
      ⟨(machine p q accept).start,heads,data⟩=some actual ∧ actual.steps≤fuel+1 ∧
      actual.final.heads=prior.final.heads ∧ actual.final.tapes=prior.final.tapes := by
  obtain ⟨u,hu,trace⟩ := stop_receipt (sizes a b) (programs p q) 0 (next accept) 0 fuel _ prior hp (by
    change (if accept prior.final.control then some (1 : Fin 2) else none)=none
    rw [ha]; rfl)
  obtain ⟨actual,hr,hf,hs⟩ := trace.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have more := runFrom_moreFuel (machine p q accept) u (fuel+1-u) _ actual hr
  rw [Nat.add_sub_of_le hu] at more
  exact ⟨actual,more,hs.le.trans hu,by rw [hf]; rfl,by rw [hf]; rfl⟩

end PCJ9eff70d512234a4c_Fixed.PhysicalConditional
