import Proof.Packets.PacketsXModeCacheCommon
import Proof.Packets.WindowSeedClear
import Proof.Packets.PhysicalBoundedLeftRewind

/-! Complete reusable delta-cache call: physically clear the old output,
produce both original sibling/child halves, retain the actual child count,
and return the new source cursor. All protected parameter masters may have
common-R zero backing supplied by their actual producers. -/
set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 1000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
attribute [local irreducible] ModeCacheCommon.delta RecoveryScratchErase.resetMachine

def caps (R : Nat) (i : Fin 28) := if i=27 then R+3 else
  if i=0∨i=2∨i=3∨i=5∨i=9∨i=11∨i=12∨i=20∨i=21∨i=24 then R else 0
def H (pos : Nat) : Fin 29→Nat := Fin.addCases (m:=28) (n:=1)
  (fun i=>if i=20 then pos else 0) (fun _=>1)
def A (p : Parameters) (M R : Nat) (out : List Bool) (priv : Fin 15→List Bool) : Fin 29→List Bool :=
  Fin.addCases (m:=28) (n:=1)
    (fun i=>ZeroPadding.pad (caps R i) (reuseData p M (R+3) R out priv i))
    (fun _=>UnaryTemplate.tape R)
def word (p : Parameters) (M : Nat) := CloseoutRowsRawPairSeek.cacheWord (pairs 1 p M++pairs 2 p M)
def clearSlots : Fin 3→Fin 29 := ![20,26,27]
def backSlots : Fin 2→Fin 29 := ![28,20]
noncomputable def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def delta := TapeEmbedding.machine 1 ModeCacheCommon.delta
noncomputable def back := RecoveryFocus.machine backSlots Completion.PhysicalBoundedLeftRewind.machine
noncomputable def machine := Composition.machine clear (Composition.machine delta back)
def budget (p : Parameters) (M R : Nat) := 4*R+2*ModeCacheCommon.budget p M R+9
attribute [local irreducible] machine delta

private theorem reuse_data_outside (p : Parameters) (M R : Nat) (out : List Bool)
    (priv : Fin 15→List Bool) (j : Fin 28) (hi : j≠20) :
    reuseData p M (R+3) R [] priv j=reuseData p M (R+3) R out priv j := by
  fin_cases j <;>simp_all [reuseData]

private theorem A_outside (p : Parameters) (M R : Nat) (out : List Bool) (priv : Fin 15→List Bool)
    (i : Fin 29) (hi : i≠20) : A p M R [] priv i=A p M R out priv i := by
  revert hi
  refine Fin.addCases (m:=28) (n:=1) (fun j=>?_) (fun j=>?_) i
  · intro hi
    simp only [A,Fin.addCases_left]
    exact congrArg (ZeroPadding.pad (caps R j))
      (reuse_data_outside p M R out priv j (by intro he;subst j;exact hi rfl))
  · intro _
    simp only [A,Fin.addCases_right]

theorem clear_run (p : Parameters) (M R : Nat) (out : List Bool) (priv : Fin 15→List Bool)
    (ho : out.length≤R) :
    Step clear (2*R+4) (H 0) (A p M R out priv) (H 0) (A p M R [] priv) := by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3)
    (fun _ : Fin 1=>ZeroPadding.pad R out)
    (by intro i;rw [ZeroPadding.pad_length,Nat.max_eq_left ho]))
  have hm:max (R+3) (R+1)=R+3:=by omega
  rw [hm] at h
  apply PhysicalFocusBoundary.focus h clearSlots (by decide)
    (H 0) (H 0) (A p M R out priv) (A p M R [] priv)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [A,caps,clearSlots,reuseData,Fin.addCases,ZeroPadding.pad_zero,
      Rewind.Workspace.pad_zeros,Nat.max_eq_left (by omega : R+1≤R+3)]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [A,caps,clearSlots,reuseData,Fin.addCases,ZeroPadding.pad_zero,
      Rewind.Workspace.pad_zeros,Nat.max_eq_left (by omega : R+1≤R+3),ZeroPadding.pad]
    rw [show R+3=(R+1)+2 by omega,List.replicate_add]
    rfl
  · intro i away
    exact ⟨rfl,(A_outside p M R out priv i (Ne.symm (away 0))).symm⟩

theorem delta_run (p : Parameters) (M R : Nat) (priv : Fin 15→List Bool)
    (hl : p.level≤p.rank) (hC : p.rank+2≤p.C)
    (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C)
    (hi : M≤2^p.rank) (hlog : sourceBudget p M≤R+3)
    (hD : reuseCapacity p M≤R) (hprivate : ∀i,(priv i).length≤R) :
    Step delta (2*ModeCacheCommon.budget p M R+1) (H 0) (A p M R [] priv)
      (H (word p M).length) (A p M R (word p M) (reuseFinal 2 p M R)) := by
  have h:=((ModeCacheCommon.delta_run p M R [] priv hl hC hb hi hlog hD hprivate).pad (caps R)).embed
    (fun _ : Fin 1=>1) (fun _=>UnaryTemplate.tape R)
  have hin : Fin.addCases (m:=28) (n:=1) (reuseHeads []) (fun _=>1)=H 0 := rfl
  have hout : Fin.addCases (m:=28) (n:=1) (reuseHeads (word p M)) (fun _=>1)=H (word p M).length := rfl
  have tin : (Fin.addCases (m:=28) (n:=1)
      (fun i=>ZeroPadding.pad (caps R i) (reuseData p M (R+3) R [] priv i))
      (fun _=>UnaryTemplate.tape R))=A p M R [] priv := rfl
  have tout : (Fin.addCases (m:=28) (n:=1)
      (fun i=>ZeroPadding.pad (caps R i) (reuseData p M (R+3) R (word p M) (reuseFinal 2 p M R) i))
      (fun _=>UnaryTemplate.tape R))=A p M R (word p M) (reuseFinal 2 p M R) := rfl
  rw [List.nil_append] at h
  unfold delta
  exact (h.congr_in hin tin).congr hout tout

theorem back_run (p : Parameters) (M R : Nat) (priv : Fin 15→List Bool)
    (hword : (word p M).length≤R) :
    Step back (2*R+2) (H (word p M).length) (A p M R (word p M) priv)
      (H 0) (A p M R (word p M) priv) := by
  obtain ⟨r,rr,rf,_⟩:=Completion.PhysicalBoundedLeftRewind.run R (word p M).length
    (ZeroPadding.pad R (word p M)) hword
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  apply PhysicalFocusBoundary.focus h backSlots (by decide)
    (H (word p M).length) (H 0) (A p M R (word p M) priv) (A p M R (word p M) priv)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away;fin_cases i <;>first | exact False.elim (away 1 rfl) | exact ⟨rfl,rfl⟩

theorem run (p : Parameters) (M R : Nat) (out : List Bool) (priv : Fin 15→List Bool)
    (hl : p.level≤p.rank) (hC : p.rank+2≤p.C)
    (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C)
    (hi : M≤2^p.rank) (hlog : sourceBudget p M≤R+3)
    (hD : reuseCapacity p M≤R) (hprivate : ∀i,(priv i).length≤R)
    (hout : out.length≤R) (hword : (word p M).length≤R) :
    Step machine (budget p M R) (H 0) (A p M R out priv)
      (H 0) (A p M R (word p M) (reuseFinal 2 p M R)) := by
  have h:=(clear_run p M R out priv hout).seq
    ((delta_run p M R priv hl hC hb hi hlog hD hprivate).seq
      (back_run p M R _ hword))
  have hf : (2*R+4)+1+((2*ModeCacheCommon.budget p M R+1)+1+(2*R+2))=budget p M R := by
    unfold budget;omega
  simpa only [machine,hf] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheReady
