import Proof.Rows.CircuitFlagLoad

/-! Consume the loaded circuit, then rewind and erase exactly its raw payload,
count, and isolated frame. The original outer source remains resident. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitFlagBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds PCJ45bee56da9f34d5a_CircuitFlagBank
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload flags)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeCircuitFlags.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_HeaderRewind.clear

def body:=TapeEmbedding.machine 3 PCJ45bee56da9f34d5a_NativeCircuitFlags.machine
def clearSlots : Fin 5→Fin 127:=![114,123,125,105,106]
def clear:=RecoveryFocus.machine clearSlots (PCJ45bee56da9f34d5a_HeaderRewind.clear 3)

theorem body_run {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q)
 (source top out : List Bool) (B Q cursor : Nat) (hn : gs.length≤B)
 (hb : ∀g∈gs,(PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B) :
 Step body (PCJ45bee56da9f34d5a_NativeCircuitFlags.budget gs.length B q top.length)
  (heads 0 cursor out Q 0)
  (bank live x B source (payload gs top) (frame (payload gs top)) out (List.replicate (U B q (B+1)) false) Q)
  (heads (payload gs top).length cursor (out++flags gs live x) (Q+gs.length+1) 1)
  (bank live x B source (payload gs top) (frame (payload gs top)) (out++flags gs live x)
    (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word gs.length)) (Q+gs.length+1)) := by
 have h:=(PCJ45bee56da9f34d5a_NativeCircuitFlags.run gs live x top [] out B Q hn hb).pad (caps (U B q (B+1)))
 simp only [List.append_nil] at h
 rw [inner_pad,inner_pad] at h
 exact h.embed (![cursor,0,0] : Fin 3→Nat)
  (![source,ZeroPadding.pad (U B q (B+1)) (frame (payload gs top)),List.replicate (U B q (B+1)) false] : Fin 3→List Bool)

theorem clear_heads_away (pos cursor Q : Nat) (out : List Bool) (i : Fin 127)
 (hi : i≠114) (hc : i≠123) :heads pos cursor out Q 1 i=heads 0 cursor out Q 0 i := by
 revert hi hc
 refine Fin.addCases (m:=124) (n:=3) (fun j hj hk=>?_) (fun _ _ _=>?_) i
 · simp only [heads,Fin.addCases_left]
   have hj' : j≠114:=fun he=>hj (congrArg (fun k :Fin 124=>k.castAdd 3) he)
   have hk' : j≠123:=fun he=>hk (congrArg (fun k :Fin 124=>k.castAdd 3) he)
   exact (PCJ45bee56da9f34d5a_NativeCircuitSkip.heads_away pos 0 Q 1 out j hj').trans
    (PCJ45bee56da9f34d5a_NativeCircuitCount.heads_away 0 Q 1 0 out j hk')
 · simp only [heads,Fin.addCases_right]

theorem clear_bank_away {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q : Nat)
 (source raw framed out count : List Bool) (i : Fin 127) (hi : i≠114) (hc : i≠123) (hf : i≠125) :
 bank live x B source raw framed out count Q i=
 bank live x B source [] [] out (List.replicate (U B q (B+1)) false) Q i := by
 revert hi hc hf
 refine Fin.addCases (m:=124) (n:=3) (fun j hj hk _=>?_) (fun j _ _ hj=>?_) i
 · simp only [bank,Fin.addCases_left]
   have hj' : j≠114:=fun he=>hj (congrArg (fun k :Fin 124=>k.castAdd 3) he)
   have hk' : j≠123:=fun he=>hk (congrArg (fun k :Fin 124=>k.castAdd 3) he)
   exact (inner_source_away live x _ _ _ _ Q _ _ _ _ _ _ j hj').trans
    (PCJ45bee56da9f34d5a_NativeCircuitCount.bank_away live x _ _ _ _ Q _ _ _ _ _ _ j hk')
 · fin_cases j <;>first | exact False.elim (hj rfl) | rfl

theorem clear_run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q cursor n : Nat)
 (source raw out : List Bool) (hr : (frame raw).length≤U B q (B+1)) (hn : n+1≤U B q (B+1)) :
 Step clear (4*U B q (B+1)+9) (heads raw.length cursor out Q 1)
  (bank live x B source raw (frame raw) out (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word n)) Q)
  (heads 0 cursor out Q 0)
  (bank live x B source [] [] out (List.replicate (U B q (B+1)) false) Q) := by
 have hraw : raw.length≤U B q (B+1) :=by rw [frame_length] at hr;omega
 have hone : 1≤U B q (B+1):=by omega
 have hcount : (CompareMachine.word n).length≤U B q (B+1):=by simpa [CompareMachine.word] using hn
 have h:=(PCJ45bee56da9f34d5a_HeaderRewind.clear_run 3 (![raw.length,1,0] :Fin 3→Nat)
  (![ZeroPadding.pad (U B q (B+1)) raw,ZeroPadding.pad (U B q (B+1)) (CompareMachine.word n),
    ZeroPadding.pad (U B q (B+1)) (frame raw)] :Fin 3→List Bool) (U B q (B+1))
  (by intro i;fin_cases i <;>first | exact hraw | exact hone | exact Nat.zero_le _)
  (by
   intro i
   fin_cases i
   · change (ZeroPadding.pad (U B q (B+1)) raw).length ≤ U B q (B+1)
     rw [ZeroPadding.pad_length];exact max_le (le_refl _) hraw
   · change (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word n)).length ≤ U B q (B+1)
     rw [ZeroPadding.pad_length];exact max_le (le_refl _) hcount
   · change (ZeroPadding.pad (U B q (B+1)) (frame raw)).length ≤ U B q (B+1)
     rw [ZeroPadding.pad_length];exact max_le (le_refl _) hr)).dock
  clearSlots (by decide) (heads raw.length cursor out Q 1)
  (bank live x B source raw (frame raw) out (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word n)) Q)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads clearSlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact clear_heads_away _ _ Q out i (fun he=>hi 0 he.symm) (fun he=>hi 1 he.symm)
 · apply HierarchyAllocation.install_eq clearSlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact (clear_bank_away live x B Q _ _ _ _ _ i
      (fun he=>hi 0 he.symm) (fun he=>hi 1 he.symm) (fun he=>hi 2 he.symm)).symm
end
end PCJ45bee56da9f34d5a_CircuitFlagBody
