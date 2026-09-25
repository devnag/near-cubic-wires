import Proof.Assembly.MaskReturn
import Proof.Assembly.Scan

/-! One actual framed support row: scan its membership bits and physically
return the three mask cursors, retaining the source cursor and accumulated score. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Row
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan

def returnSlots : Fin 4 → Fin 8 := ![7,1,2,3]
theorem returnSlots_injective : Function.Injective returnSlots := by decide

noncomputable def machine : Machine 8 6 :=
  Composition.machine (TapeEmbedding.machine 1 CloseoutRowsTouching.SupportScan.machine)
    (RecoveryFocus.machine returnSlots MaskReturn.machine)

def cfg (state : Fin 3) (q : Nat) (source : List Bool) (pos : Nat)
    (mask : Fin 3 → List Bool) (j n : Nat) (hit cur : Bool) : Configuration 8 3 :=
  ⟨state, ![pos,j,j,j,n+1,0,0,1],
    ![source,mask 0,mask 1,mask 2,CompareMachine.word n,[hit],[cur],CompareMachine.word q]⟩

theorem embed_cfg (state : Fin 3) (q : Nat) (source : List Bool) (pos : Nat)
    (mask : Fin 3 → List Bool) (j n : Nat) (hit cur : Bool) :
    TapeEmbedding.config (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word q)
      (prefixedCfg [false] state source pos mask j n hit cur) =
      cfg state q source pos mask j n hit cur := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeEmbedding.config,prefixedCfg,cfg,Nat.add_comm] <;> rfl
  · funext i; fin_cases i <;> rfl

theorem return_focused (q : Nat) (source : List Bool) (pos : Nat)
    (mask : Fin 3 → List Bool) (j n : Nat) (hit cur : Bool) :
    ∃ r, runFrom (RecoveryFocus.machine returnSlots MaskReturn.machine) (2*q+2)
      (cfg 0 q source pos mask (j+q) n hit cur) = some r ∧
      r.final = cfg 2 q source pos mask j n hit cur ∧ r.steps = 2*q+2 := by
  obtain ⟨s,hs,hf,ht⟩ := MaskReturn.return_run q j mask
  have hh : ∀ k, (cfg 0 q source pos mask (j+q) n hit cur).heads (returnSlots k) =
      (MaskReturn.scanCfg q j mask 0).heads k := by
    intro k; fin_cases k <;> simp [cfg,returnSlots,MaskReturn.scanCfg]
  have hb : ∀ k, (cfg 0 q source pos mask (j+q) n hit cur).tapes (returnSlots k) =
      (MaskReturn.scanCfg q j mask 0).tapes k := by
    intro k; fin_cases k <;> rfl
  obtain ⟨r,hr,hc,hsteps,hheads,htapes,hother⟩ := RecoveryFocus.dock returnSlots
    returnSlots_injective MaskReturn.machine (2*q+2)
    (cfg 0 q source pos mask (j+q) n hit cur).heads
    (cfg 0 q source pos mask (j+q) n hit cur).tapes
    (MaskReturn.scanCfg q j mask 0) hh hb s hs
  refine ⟨r,hr,?_,hsteps.trans ht⟩
  rw [hf] at hc hheads htapes
  apply configuration_ext
  · exact hc
  · funext i
    fin_cases i
    · exact (hother 0 (by intro k; fin_cases k <;> decide)).1
    · exact hheads 1
    · exact hheads 2
    · exact hheads 3
    · exact (hother 4 (by intro k; fin_cases k <;> decide)).1
    · exact (hother 5 (by intro k; fin_cases k <;> decide)).1
    · exact (hother 6 (by intro k; fin_cases k <;> decide)).1
    · exact hheads 0
  · funext i
    fin_cases i
    · exact (hother 0 (by intro k; fin_cases k <;> decide)).2
    · exact htapes 1
    · exact htapes 2
    · exact htapes 3
    · exact (hother 4 (by intro k; fin_cases k <;> decide)).2
    · exact (hother 5 (by intro k; fin_cases k <;> decide)).2
    · exact (hother 6 (by intro k; fin_cases k <;> decide)).2
    · exact htapes 0

theorem row_run (pre bs tail : List Bool) (mask : Fin 3 → List Bool)
    (j n : Nat) (hit cur : Bool) :
    ∃ r, runFrom machine (4*bs.length+4)
      (Composition.leftConfig 3 (cfg 0 bs.length (pre++frame bs++tail)
        pre.length mask j n hit cur)) = some r ∧
      r.final = Composition.rightConfig 3
        (cfg 2 bs.length (pre++frame bs++tail) (pre.length+2*bs.length+1)
          mask j (n+count (Scan.cells mask j bs))
          (hit||(Scan.cells mask j bs).any touched)
          (cur||(Scan.cells mask j bs).any current)) ∧ r.steps = 4*bs.length+4 := by
  obtain ⟨s,hs,hf,ht⟩ := Scan.offset_run [false] pre bs tail mask j n hit cur
  let e := TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word bs.length) s
  have he := TapeEmbedding.run_embed CloseoutRowsTouching.SupportScan.machine
    (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word bs.length) _ _ s hs
  rw [embed_cfg] at he
  have hef : e.final = cfg 2 bs.length (pre++frame bs++tail)
      (pre.length+2*bs.length+1) mask (j+bs.length) (n+count (Scan.cells mask j bs))
      (hit||(Scan.cells mask j bs).any touched) (cur||(Scan.cells mask j bs).any current) := by
    dsimp only [e,TapeEmbedding.receipt]
    rw [hf,embed_cfg]
  obtain ⟨r,hr,hrf,hrt⟩ := return_focused bs.length (pre++frame bs++tail)
    (pre.length+2*bs.length+1) mask j (n+count (Scan.cells mask j bs))
    (hit||(Scan.cells mask j bs).any touched) (cur||(Scan.cells mask j bs).any current)
  have hjoin : Composition.restart e.final
      (RecoveryFocus.machine returnSlots MaskReturn.machine).start =
      cfg 0 bs.length (pre++frame bs++tail) (pre.length+2*bs.length+1)
        mask (j+bs.length) (n+count (Scan.cells mask j bs))
        (hit||(Scan.cells mask j bs).any touched) (cur||(Scan.cells mask j bs).any current) := by
    rw [hef]; rfl
  rw [←hjoin] at hr
  have joined := Composition.run_join (TapeEmbedding.machine 1 CloseoutRowsTouching.SupportScan.machine)
    (RecoveryFocus.machine returnSlots MaskReturn.machine) _ _ _ e r he hr
  have htime : (2*bs.length+1)+1+(2*bs.length+2) = 4*bs.length+4 := by omega
  rw [htime] at joined
  refine ⟨Composition.joinedReceipt e r,joined,?_,?_⟩
  · change Composition.rightConfig 3 r.final = _
    rw [hrf]
  · change s.steps+1+r.steps = _
    rw [ht,hrt,htime]

end PCJ93d4cfe17dc847a3.Row
