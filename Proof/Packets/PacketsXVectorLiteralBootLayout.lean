import Proof.Packets.PacketsXVectorControllerInitialize
import Proof.Packets.PacketsXVectorLiteralLevelState
import Proof.Packets.PacketsXVectorTerminalTyped

/-! Exact output layout of the physical controller initializer. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def coldData (C R : Nat) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool) : Fin 299 → List Bool :=
  Fin.addCases (m:=298) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=296) (n:=2) (motive:=fun _=>List Bool)
      (A C R 0 0 0 [] [] [] [] [] fields extra) (fun _=>List.replicate R false))
    (fun _=>List.replicate R false)
def bootFields (R M : Nat) (fields : Fin 222 → List Bool) :=
  Function.update (Function.update (Function.update fields 150 (WindowSeed.source R (2*M)))
    151 (WindowSeed.source R (Nat.log 2 (2*M)+1))) 127 (WindowSeed.source R M)
def bootExtra (R M : Nat) (extra : Fin 32 → List Bool) := Function.update extra 17 (WindowSeed.source R M)
def bootData (C R M depth : Nat) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool) : Fin 299 → List Bool :=
  Fin.addCases (m:=298) (n:=1) (motive:=fun _=>List Bool)
    (levelData C R (M+1) 0 0 depth [List.replicate C false] []
      (PacketVector.bank R ([List.replicate C false]::List.replicate M []))
      (PacketVector.bank R (List.replicate (M+1) [])) (bootFields R M fields) (bootExtra R M extra))
    (fun _=>WindowSeed.source R depth)

theorem initialized_cold_data (C R M depth : Nat) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (hR : 1≤R) :
    VectorNumericArena.initialized R C M depth (coldData C R fields extra)=bootData C R M depth fields extra := by
  funext i
  refine Fin.addCases (m:=298) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=296) (n:=2) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=264) (n:=32) (fun l=>?_) (fun l=>?_) k
      · refine Fin.addCases (m:=256) (n:=8) (fun q=>?_) (fun q=>?_) l
        · refine Fin.addCases (m:=34) (n:=222) (fun r=>?_) (fun r=>?_) q
          · by_cases h25 : r=25
            · subst r
              change ZeroPadding.pad R (List.replicate C false)=ZeroPadding.pad R ([List.replicate C false].flatten)
              simp
            by_cases h28 : r=28
            · subst r;rfl
            have same : ReusableArithmetic.state C R [] [] r=
                ReusableArithmetic.state C R [List.replicate C false] [] r := by
              simpa only [VectorAccumulator.tapes_engine] using
                VectorAccumulator.tapes_left_outside C R [] [] [List.replicate C false] [] (r.castAdd 2)
                  (by intro he;exact h25 (Fin.ext (congrArg (fun k : Fin 36=>k.val) he)))
                  (by intro he;exact h28 (Fin.ext (congrArg (fun k : Fin 36=>k.val) he)))
            have ne (n : Fin 299) (hn : n.val=257 ∨ n.val=28 ∨ n.val=25 ∨ n.val=256 ∨ n.val=161 ∨ n.val=298 ∨ n.val=297 ∨ n.val=296 ∨ n.val=281 ∨ n.val=260 ∨ n.val=185 ∨ n.val=184) :
                ((((r.castAdd 222).castAdd 8).castAdd 32).castAdd 2).castAdd 1≠n := by
              intro he
              have hv:=congrArg (fun z : Fin 299=>z.val) he
              dsimp at hv
              norm_num [Fin.ext_iff] at h25 h28
              have bound:=r.isLt
              omega
            simp only [VectorNumericArena.initialized,VectorNumericArena.terminalOutput,
              VectorNumericArena.bootOutput,VectorNumericArena.driverData,VectorNumericArena.populationData,
              VectorNumericArena.phaseOutput,coldData,bootData,levelData,A,VectorController.A,
              Fin.addCases_left,Fin.addCases_right,
              Function.update_of_ne (ne 257 (by decide)),
              Function.update_of_ne (ne 28 (by decide)),
              Function.update_of_ne (ne 25 (by decide)),
              Function.update_of_ne (ne 256 (by decide)),
              Function.update_of_ne (ne 161 (by decide)),
              Function.update_of_ne (ne 298 (by decide)),
              Function.update_of_ne (ne 297 (by decide)),
              Function.update_of_ne (ne 296 (by decide)),
              Function.update_of_ne (ne 281 (by decide)),
              Function.update_of_ne (ne 260 (by decide)),
              Function.update_of_ne (ne 185 (by decide)),
              Function.update_of_ne (ne 184 (by decide))]
            exact same
          · by_cases h127 : r=127
            · subst r;rfl
            by_cases h150 : r=150
            · subst r;rfl
            by_cases h151 : r=151
            · subst r;rfl
            have ne (n : Fin 299) (hn : n.val=257 ∨ n.val=28 ∨ n.val=25 ∨ n.val=256 ∨ n.val=161 ∨ n.val=298 ∨ n.val=297 ∨ n.val=296 ∨ n.val=281 ∨ n.val=260 ∨ n.val=185 ∨ n.val=184) :
                ((((r.natAdd 34).castAdd 8).castAdd 32).castAdd 2).castAdd 1≠n := by
              intro he
              have hv:=congrArg (fun z : Fin 299=>z.val) he
              dsimp at hv
              norm_num [Fin.ext_iff] at h127 h150 h151
              have bound:=r.isLt
              omega
            simp only [VectorNumericArena.initialized,VectorNumericArena.terminalOutput,
              VectorNumericArena.bootOutput,VectorNumericArena.driverData,VectorNumericArena.populationData,
              VectorNumericArena.phaseOutput,coldData,bootData,levelData,A,VectorController.A,
              Fin.addCases_left,Fin.addCases_right,
              Function.update_of_ne (ne 257 (by decide)),
              Function.update_of_ne (ne 28 (by decide)),
              Function.update_of_ne (ne 25 (by decide)),
              Function.update_of_ne (ne 256 (by decide)),
              Function.update_of_ne (ne 161 (by decide)),
              Function.update_of_ne (ne 298 (by decide)),
              Function.update_of_ne (ne 297 (by decide)),
              Function.update_of_ne (ne 296 (by decide)),
              Function.update_of_ne (ne 281 (by decide)),
              Function.update_of_ne (ne 260 (by decide)),
              Function.update_of_ne (ne 185 (by decide)),
              Function.update_of_ne (ne 184 (by decide)),
              bootFields,Function.update_of_ne h127,Function.update_of_ne h150,Function.update_of_ne h151]
        · fin_cases q <;> first | rfl | simp [VectorNumericArena.initialized,VectorNumericArena.terminalOutput,
            VectorNumericArena.bootOutput,VectorNumericArena.driverData,VectorNumericArena.populationData,
            VectorNumericArena.phaseOutput,coldData,bootData,levelData,A,VectorController.A,Fin.addCases,
            VectorController.extraTapes,Function.update,VectorTerminalBank.result_bank R C M hR,
            VectorTerminalBank.empty_bank R (M+1) hR,WindowSeed.source]
      · by_cases h17 : l=17
        · subst l;rfl
        have ne (n : Fin 299) (hn : n.val=257 ∨ n.val=28 ∨ n.val=25 ∨ n.val=256 ∨ n.val=161 ∨ n.val=298 ∨ n.val=297 ∨ n.val=296 ∨ n.val=281 ∨ n.val=260 ∨ n.val=185 ∨ n.val=184) :
            ((l.natAdd 264).castAdd 2).castAdd 1≠n := by
          intro he
          have hv:=congrArg (fun z : Fin 299=>z.val) he
          dsimp at hv
          norm_num [Fin.ext_iff] at h17
          have bound:=l.isLt
          omega
        simp only [VectorNumericArena.initialized,VectorNumericArena.terminalOutput,
          VectorNumericArena.bootOutput,VectorNumericArena.driverData,VectorNumericArena.populationData,
          VectorNumericArena.phaseOutput,coldData,bootData,levelData,A,VectorController.A,
          Fin.addCases_left,Fin.addCases_right,
          Function.update_of_ne (ne 257 (by decide)),
          Function.update_of_ne (ne 28 (by decide)),
          Function.update_of_ne (ne 25 (by decide)),
          Function.update_of_ne (ne 256 (by decide)),
          Function.update_of_ne (ne 161 (by decide)),
          Function.update_of_ne (ne 298 (by decide)),
          Function.update_of_ne (ne 297 (by decide)),
          Function.update_of_ne (ne 296 (by decide)),
          Function.update_of_ne (ne 281 (by decide)),
          Function.update_of_ne (ne 260 (by decide)),
          Function.update_of_ne (ne 185 (by decide)),
          Function.update_of_ne (ne 184 (by decide)),
          bootExtra,Function.update_of_ne h17]
    · fin_cases k <;> rfl
  · fin_cases j
    rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
