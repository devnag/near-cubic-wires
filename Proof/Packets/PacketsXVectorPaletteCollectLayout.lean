import Proof.Packets.PacketsXVectorPaletteCollect

/-! Exact collector boundary for the literal program's retained output ports. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def collectData (palette : Fin 15 → List Bool) (S : Nat) (work : Fin 299 → List Bool)
    (transcript : List Bool) : Fin 317 → List Bool :=
  Fin.addCases (m:=316) (n:=1) (motive:=fun _=>List Bool) (paletteData palette S work) (fun _=>transcript)

theorem palette_update_work (palette : Fin 15 → List Bool) (S : Nat)
    (work : Fin 299 → List Bool) (j : Fin 299) (word : List Bool) :
    Function.update (paletteData palette S work) (paletteArenaSlots j) word =
      paletteData palette S (Function.update work j word) := by
  change Function.update (paletteData palette S work) (((j.castAdd 1).natAdd 15).castAdd 1) word=_
  unfold paletteData
  rw [PhysicalAppendUpdate.left,PhysicalAppendUpdate.right,PhysicalAppendUpdate.left]

theorem collect_output_layout (palette : Fin 15 → List Bool) (S : Nat)
    (work : Fin 299 → List Bool) (old word : List Bool) :
    collectOutput S (collectData palette S work old) word=
      collectData palette S (Function.update work 257 (List.replicate S false)) word := by
  unfold collectOutput collectData
  change Function.update (Function.update
    (Fin.addCases (m:=316) (n:=1) (motive:=fun _=>List Bool)
      (paletteData palette S work) (fun _=>old))
    ((paletteArenaSlots 257).castAdd 1) (List.replicate S false))
    ((0 : Fin 1).natAdd 316) word=_
  rw [PhysicalAppendUpdate.left,palette_update_work,PhysicalAppendUpdate.right]
  congr 1
  funext i;fin_cases i;rfl

theorem collect_palette_run (R S : Nat) (packets : List PacketVector.Packet) (pre rest : List Bool)
    (palette : Fin 15 → List Bool) (output : Fin 299 → List Bool)
    (hR : 1 ≤ R) (hRS : R ≤ S) (hpackets : ∀P∈packets,PacketVector.Fits R P)
    (hbank : (PacketVector.bank R packets).length ≤ S)
    (hcoordinates : output 257=PacketVector.bank R packets)
    (hwidth : output 31=UnaryTemplate.tape R)
    (hcount : output 297=ZeroPadding.pad R (CompareMachine.word packets.length))
    (hscratch : output 261=ZeroPadding.pad R [])
    (hzero : output 263=List.replicate R false) :
    Step collectMachine (PacketVectorAppend.budget R packets.length) (collectHeads pre.length)
      (collectData palette S (fun i=>ZeroPadding.pad S (output i))
        (pre++List.replicate (packets.length*(2*R)) false++rest))
      (collectHeads (pre.length+packets.length*(2*R)))
      (collectData palette S
        (Function.update (fun i=>ZeroPadding.pad S (output i)) 257 (List.replicate S false))
        (pre++PacketVector.bank R packets++rest)) := by
  have hpin : ∀j,collectData palette S (fun i=>ZeroPadding.pad S (output i))
      (pre++List.replicate (packets.length*(2*R)) false++rest) (collectSlots j)=
      PacketVectorAppend.paddedTapes R packets.length S (ZeroPadding.pad S (PacketVector.bank R packets))
        (pre++List.replicate (packets.length*(2*R)) false++rest) j := by
    intro j;fin_cases j
    · change ZeroPadding.pad S (output 31)=_;rw [hwidth];rfl
    · change ZeroPadding.pad S (output 257)=_;rw [hcoordinates];rfl
    · rfl
    · change ZeroPadding.pad S (output 263)=_
      rw [hzero,Rewind.Workspace.pad_zeros,Nat.max_eq_left hRS];rfl
    · change ZeroPadding.pad S (output 261)=_
      rw [hscratch,MatrixBucketRootPower.pad_pad R S _ hRS]
      simp [PacketVectorAppend.paddedTapes,ZeroPadding.pad]
    · change ZeroPadding.pad S (output 297)=_
      rw [hcount,MatrixBucketRootPower.pad_pad R S _ hRS];rfl
  have run:=collect_run R S packets pre rest _ hR hRS hpackets hbank hpin
  rw [collect_output_layout] at run
  exact run

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
