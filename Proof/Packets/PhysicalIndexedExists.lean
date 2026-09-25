import Proof.Packets.PhysicalRepeatExists
import Proof.Packets.PhysicalIndexedAt

/-! Actual indexed loops with an existential tape invariant. The resident
index is advanced by the finite program; worker implementations may hide
private scratch through the invariant instead of naming a whole trajectory. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalIndexedExists
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem run {t s : Nat} (port : Fin t) (worker : Machine t s) (N E R : Nat)
    (H : Fin t→Nat) (hhead : H port=1)
    (P : Nat→(Fin t→List Bool)→Prop) (A : Fin t→List Bool) (ha : P 0 A)
    (hindex : ∀i,i≤N→∀a,P i a→a port=ZeroPadding.pad R (CompareMachine.word i))
    (step : ∀i,i<N→∀a,P i a→∃b,Step worker E H a H b ∧
      b port=ZeroPadding.pad R (CompareMachine.word i) ∧
      P (i+1) (Function.update b port (ZeroPadding.pad R (CompareMachine.word (i+1))))) :
    ∃B,Step (PhysicalIndexedAt.machine port worker) (N*(E+2*N+6)+3)
      (Fin.addCases H (fun _ : Fin 1=>1))
      (Fin.addCases A (fun _ : Fin 1=>CompareMachine.word N))
      (Fin.addCases H (fun _ : Fin 1=>1))
      (Fin.addCases B (fun _ : Fin 1=>CompareMachine.word N)) ∧
      P N B ∧ B port=ZeroPadding.pad R (CompareMachine.word N) := by
  have heads : PhysicalIndexedAt.H port H=H := by
    exact Function.update_eq_self_iff.mpr hhead.symm
  have bodyStep (i : Nat) (hi : i<N) (a : Fin t→List Bool) (hpa : P i a) :
      ∃b,Step (PhysicalIndexedAt.body port worker) (E+2*N+3) H a H b ∧ P (i+1) b := by
    obtain ⟨b,hb,hbi,hpb⟩:=step i hi a hpa
    have advance:=PhysicalIndexedAt.advance_run port R i H b
    have before : PhysicalIndexedAt.A port R i b=b := by
      exact Function.update_eq_self_iff.mpr hbi.symm
    rw [heads,before] at advance
    refine ⟨Function.update b port (ZeroPadding.pad R (CompareMachine.word (i+1))),?_,hpb⟩
    exact (hb.seq advance).enlarge (by omega)
  obtain ⟨B,hb,hp⟩:=PhysicalRepeatExists.run (PhysicalIndexedAt.body port worker) N (E+2*N+3) H P A ha bodyStep
  have fuel : N*((E+2*N+3)+3)+3=N*(E+2*N+6)+3 := by ring
  rw [fuel] at hb
  exact ⟨B,hb,hp,hindex N le_rfl B hp⟩

 theorem run_down {t s : Nat} (port : Fin t) (worker : Machine t s) (N E R : Nat)
    (H : Fin t→Nat) (hhead : H port=1) (hR : N+1≤R)
    (P : Nat→(Fin t→List Bool)→Prop) (A : Fin t→List Bool) (ha : P 0 A)
    (hindex : ∀i,i≤N→∀a,P i a→a port=ZeroPadding.pad R (CompareMachine.word (N-i)))
    (step : ∀i,i<N→∀a,P i a→∃b,
      Step worker E H (Function.update a port (ZeroPadding.pad R (CompareMachine.word (N-(i+1))))) H b ∧ P (i+1) b) :
    ∃B,Step (PhysicalIndexedAt.downMachine port worker) (N*(E+2*N+6)+3)
      (Fin.addCases H (fun _ : Fin 1=>1))
      (Fin.addCases A (fun _ : Fin 1=>CompareMachine.word N))
      (Fin.addCases H (fun _ : Fin 1=>1))
      (Fin.addCases B (fun _ : Fin 1=>CompareMachine.word N)) ∧
      P N B ∧ B port=ZeroPadding.pad R (CompareMachine.word 0) := by
  have heads : PhysicalIndexedAt.H port H=H := by
    exact Function.update_eq_self_iff.mpr hhead.symm
  have bodyStep (i : Nat) (hi : i<N) (a : Fin t→List Bool) (hpa : P i a) :
      ∃b,Step (PhysicalIndexedAt.downBody port worker) (E+2*N+3) H a H b ∧ P (i+1) b := by
    have retreat:=PhysicalIndexedAt.retreat_run port R (N-(i+1)) H a (by omega)
    have before : PhysicalIndexedAt.A port R (N-(i+1)+1) a=a := by
      have idx:=hindex i (by omega) a hpa
      have he:N-(i+1)+1=N-i := by omega
      rw [he]
      exact Function.update_eq_self_iff.mpr idx.symm
    rw [heads,before] at retreat
    obtain ⟨b,hb,hpb⟩:=step i hi a hpa
    exact ⟨b,(retreat.seq hb).enlarge (by omega),hpb⟩
  obtain ⟨B,hb,hp⟩:=PhysicalRepeatExists.run (PhysicalIndexedAt.downBody port worker) N (E+2*N+3) H P A ha bodyStep
  have fuel : N*((E+2*N+3)+3)+3=N*(E+2*N+6)+3 := by ring
  rw [fuel] at hb
  exact ⟨B,hb,hp,by simpa only [Nat.sub_self] using hindex N le_rfl B hp⟩

def driverCapacity {t : Nat} (R : Nat) : Fin (t+1)→Nat := Fin.addCases (fun _ : Fin t=>0) (fun _ : Fin 1=>R)

theorem driver_padding {t : Nat} (R : Nat) (A : Fin t→List Bool) (w : List Bool) :
    (fun i=>ZeroPadding.pad (driverCapacity (t:=t) R i) ((Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) A (fun _ : Fin 1=>w)) i))=
      Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) A (fun _ : Fin 1=>ZeroPadding.pad R w) := by
  funext i
  refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [driverCapacity,Fin.addCases_left,ZeroPadding.pad_zero]
  · simp only [driverCapacity,Fin.addCases_right]

theorem run_padded {t s : Nat} (port : Fin t) (worker : Machine t s) (N E R : Nat)
    (H : Fin t→Nat) (hhead : H port=1)
    (P : Nat→(Fin t→List Bool)→Prop) (A : Fin t→List Bool) (ha : P 0 A)
    (hindex : ∀i,i≤N→∀a,P i a→a port=ZeroPadding.pad R (CompareMachine.word i))
    (step : ∀i,i<N→∀a,P i a→∃b,Step worker E H a H b ∧
      b port=ZeroPadding.pad R (CompareMachine.word i) ∧
      P (i+1) (Function.update b port (ZeroPadding.pad R (CompareMachine.word (i+1))))) :
    ∃B,Step (PhysicalIndexedAt.machine port worker) (N*(E+2*N+6)+3)
      (Fin.addCases H (fun _ : Fin 1=>1))
      (Fin.addCases A (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word N)))
      (Fin.addCases H (fun _ : Fin 1=>1))
      (Fin.addCases B (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word N))) ∧
      P N B ∧ B port=ZeroPadding.pad R (CompareMachine.word N) := by
  obtain ⟨B,hb,hp,hi⟩:=run port worker N E R H hhead P A ha hindex step
  have padded:=hb.pad (driverCapacity R)
  rw [driver_padding,driver_padding] at padded
  exact ⟨B,padded,hp,hi⟩

theorem run_down_padded {t s : Nat} (port : Fin t) (worker : Machine t s) (N E R : Nat)
    (H : Fin t→Nat) (hhead : H port=1) (hR : N+1≤R)
    (P : Nat→(Fin t→List Bool)→Prop) (A : Fin t→List Bool) (ha : P 0 A)
    (hindex : ∀i,i≤N→∀a,P i a→a port=ZeroPadding.pad R (CompareMachine.word (N-i)))
    (step : ∀i,i<N→∀a,P i a→∃b,
      Step worker E H (Function.update a port (ZeroPadding.pad R (CompareMachine.word (N-(i+1))))) H b ∧ P (i+1) b) :
    ∃B,Step (PhysicalIndexedAt.downMachine port worker) (N*(E+2*N+6)+3)
      (Fin.addCases H (fun _ : Fin 1=>1))
      (Fin.addCases A (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word N)))
      (Fin.addCases H (fun _ : Fin 1=>1))
      (Fin.addCases B (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word N))) ∧
      P N B ∧ B port=ZeroPadding.pad R (CompareMachine.word 0) := by
  obtain ⟨B,hb,hp,hi⟩:=run_down port worker N E R H hhead hR P A ha hindex step
  have padded:=hb.pad (driverCapacity R)
  rw [driver_padding,driver_padding] at padded
  exact ⟨B,padded,hp,hi⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalIndexedExists
