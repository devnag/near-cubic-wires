import Proof.Packets.PacketsXWindowEmitDock
import Proof.Packets.PacketsXWindowLevelAtoms
import Proof.Packets.PacketsXWindowLiteralConsume

/-! Ready arithmetic and raw-renaming views after the actual emitter. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (cacheWord)
open NormalizedFiniteTransport WindowNativeOrder

theorem seed_heads : ∀i,heads (seedPorts i)=0 := by decide
theorem native_range : ∀i,(nativePorts i).val<34 ∨ (96≤(nativePorts i).val ∧ (nativePorts i).val<150) := by decide

theorem emitted_raw (R v u M offset W target : Nat) (A : Fin 256→ List Bool) :
    emittedOutput R v u M offset W target A 32=List.replicate R true := by
  change emittedOutput R v u M offset W target A (seedPorts 50)=_
  rw [emittedOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot seedPorts seed_injective]
  exact WindowSeed.after_raw _ _ _ _ _ _ _ _

theorem emitted_log (R v u M offset W target : Nat) (A : Fin 256→ List Bool) :
    emittedOutput R v u M offset W target A 33=List.replicate (R+3) false := by
  change emittedOutput R v u M offset W target A (seedPorts 51)=_
  rw [emittedOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot seedPorts seed_injective]
  exact WindowSeed.after_log _ _ _ _ _ _ _ _

theorem emitted_core (R v u M offset W target : Nat) (A : Fin 256→ List Bool)
    (araw : A 32=List.replicate R true) (alog : A 33=List.replicate (R+3) false)
    (i : Fin 256) (hi : i.val<34) : emittedOutput R v u M offset W target A i=A i := by
  by_cases h32 : i=32
  · subst i;rw [emitted_raw,araw]
  by_cases h33 : i=33
  · subst i;rw [emitted_log,alog]
  exact seed_emitted_preserved _ _ _ _ _ _ _ A i (seed_away_small i hi h32 h33)

theorem emitted_native (C R v u M offset W target : Nat) (left : List (List Bool)) (A : Fin 256→ List Bool)
    (ha : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left [] i) :
    ∀i,emittedOutput R v u M offset W target (Workspace.cleared R A) (nativePorts i)=
      ReusableNative.ready C R [] i := by
  have raw : Workspace.cleared R A 32=List.replicate R true :=
    (Workspace.core_retained R A 32).trans (ha 32)
  have log : Workspace.cleared R A 33=List.replicate (R+3) false :=
    (Workspace.core_retained R A 33).trans (ha 33)
  intro i
  have retained : emittedOutput R v u M offset W target (Workspace.cleared R A) (nativePorts i)=
      Workspace.cleared R A (nativePorts i) := by
    rcases native_range i with small|middle
    · exact emitted_core _ _ _ _ _ _ _ _ raw log _ small
    · exact seed_emitted_preserved _ _ _ _ _ _ _ _ _ (seed_away_middle _ middle.1 middle.2)
  exact retained.trans (Workspace.native_ready C R left [] A ha i)

theorem emitted_raw_ready (C R v u offset W target : Nat) (codes : List Nat)
    (left : List (List Bool)) (A : Fin 256→ List Bool)
    (ha : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left [] i)
    (acache : A 186=ZeroPadding.pad R (cacheWord (literalPairs codes)))
    (hstream : (ExtIncidence.stream (positionalWindow v codes.length offset (2*W) target)).length≤ R) :
    ∀i,emittedOutput R v u codes.length offset W target (Workspace.cleared R A) (rawPorts i)=
      RawSingletonSubstitution.bank R
        (ExtIncidence.stream (positionalWindow v codes.length offset (2*W) target))
        (ZeroPadding.pad R (cacheWord (literalPairs codes))) [] i := by
  have a30 : A 30=List.replicate (R+3) false:=ha 30
  have source:=seed_emitted_source R v u codes.length offset W target (Workspace.cleared R A)
  have term : ((positionalWindow v codes.length offset (2*W) target).flatMap ExtIncidence.monomialWord).length+1≤ R := by
    simpa only [ExtIncidence.stream,List.length_append,List.length_singleton] using hstream
  have a78 : emittedOutput R v u codes.length offset W target (Workspace.cleared R A) 78=
      ZeroPadding.pad R (ExtIncidence.stream (positionalWindow v codes.length offset (2*W) target)) :=
    source.trans (padded_terminator R _ term)
  have a186 : emittedOutput R v u codes.length offset W target (Workspace.cleared R A) 186=
      ZeroPadding.pad R (cacheWord (literalPairs codes)) := by
    rw [seed_emitted_preserved _ _ _ _ _ _ _ _ _ seed_away_cache]
    simpa [Workspace.cleared,Workspace.selected] using acache
  have mid (i : Fin 256) (lo : 96≤ i.val) (hi : i.val<150) :
      emittedOutput R v u codes.length offset W target (Workspace.cleared R A) i=Workspace.cleared R A i :=
    seed_emitted_preserved _ _ _ _ _ _ _ _ _ (seed_away_middle i lo hi)
  have endlog : emittedOutput R v u codes.length offset W target (Workspace.cleared R A) 30=List.replicate (R+3) false := by
    rw [seed_emitted_preserved _ _ _ _ _ _ _ _ _ (seed_away_small 30 (by decide) (by decide) (by decide))]
    simpa [Workspace.cleared,Workspace.selected] using a30
  intro i
  fin_cases i <;>simp only [rawPorts,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.head_cons]
  all_goals simp [RawSingletonSubstitution.bank,RawSingletonSubstitution.words,Fin.addCases,
    a78,a186,endlog,mid,Workspace.cleared,Workspace.selected,ZeroPadding.pad]

theorem consume_native_heads (v M offset W target : Nat) :
    ∀i,ReusableNative.heads i=Function.update (emittedHeads v M offset W target heads) 78 0 (nativePorts i) := by
  intro i
  fin_cases i <;>simp [ReusableNative.heads,emittedHeads,heads,nativePorts]

theorem consume_raw_heads (v M offset W target : Nat) :
    ∀i,Function.update (emittedHeads v M offset W target heads) 78 0 (rawPorts i)=0 := by
  intro i
  fin_cases i <;>simp [emittedHeads,heads,rawPorts]

theorem consume_final_heads (v M offset W target : Nat) :
    Function.update (Function.update (emittedHeads v M offset W target heads) 78 0) 95 0=heads := by
  funext i
  by_cases h78:i=78
  · subst i;simp [emittedHeads,heads]
  by_cases h95:i=95
  · subst i;simp [emittedHeads,heads]
  simp [emittedHeads,h78,h95]

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
