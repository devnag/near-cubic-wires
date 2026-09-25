import Proof.SourceAssembly.SourceRestStages
import Proof.SourceAssembly.SourceRestLayout

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

namespace Dims
open NearCubicWires.SourceConstruction.Dims
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- F6's dock, by value, over plain numbers (`s11` the clear driver `scr 11`, `s11+1` its log `scr 12`). -/
def gVn (B F rt s11 eX pX gW i : Nat) : Nat :=
  if i < 61 then B + 19 + i
  else if i = 61 then B + 19 + (71 + eX + pX + gW) + 3
  else if i = 62 then B + 19 + (71 + eX + pX + gW) + 4
  else if i = 63 then F + rt + 4
  else if i = 64 then s11
  else if i = 65 then s11 + 1
  else if i < 69 then B + 19 + 61 + (i - 66)
  else F + rt + (i - 69)

theorem gVn_inj (B F rt s11 eX pX gW i j : Nat) (hi : i < 72) (hj : j < 72)
    (h1 : F + rt + 13 ≤ s11) (h2 : s11 + 2 ≤ B)
    (h : gVn B F rt s11 eX pX gW i = gVn B F rt s11 eX pX gW j) : i = j := by
  unfold gVn at h
  split_ifs at h <;> omega

def g : Fin 72 → Fin V := fun i =>
  ⟨gVn d.B d.F d.rt (d.scrV 11) eX pX gW i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres
    simp only [gVn, scrV, restPc, SourceConstruction.Dims.B, SourceConstruction.Dims.U,
      SourceConstruction.Dims.G, SourceConstruction.Dims.prepT] at *
    split_ifs <;> omega) hV⟩

def slE : Fin (2 + eX) → Fin V := fun j =>
  ⟨if j.val = 0 then d.B + 19 + 66 else if j.val = 1 then d.B + 19 + 59 else d.B + 19 + 71 + (j.val - 2),
    Nat.lt_of_lt_of_le (by
      have := j.isLt; have := e.hres
      simp only [restPc, SourceConstruction.Dims.B, SourceConstruction.Dims.U, SourceConstruction.Dims.G,
        SourceConstruction.Dims.prepT] at *
      split_ifs <;> omega) hV⟩

def slP : Fin (2 + pX) → Fin V := fun j =>
  ⟨if j.val = 0 then d.B + 19 + 66 else if j.val = 1 then d.B + 19 + 60 else d.B + 19 + 71 + eX + (j.val - 2),
    Nat.lt_of_lt_of_le (by
      have := j.isLt; have := e.hres
      simp only [restPc, SourceConstruction.Dims.B, SourceConstruction.Dims.U, SourceConstruction.Dims.G,
        SourceConstruction.Dims.prepT] at *
      split_ifs <;> omega) hV⟩

theorem g_injective : Function.Injective (g e hV) := fun a b h =>
  Fin.ext (gVn_inj d.B d.F d.rt (d.scrV 11) eX pX gW a.val b.val a.isLt b.isLt
    (by simp only [scrV, SourceConstruction.Dims.G]; omega)
    (by simp only [scrV, SourceConstruction.Dims.B, SourceConstruction.Dims.G]; omega)
    (congrArg Fin.val h))

theorem slE_injective : Function.Injective (slE e hV) := by
  intro a b h
  have hv := congrArg Fin.val h
  have ha := a.isLt; have hb := b.isLt
  simp only [slE] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem slP_injective : Function.Injective (slP e hV) := by
  intro a b h
  have hv := congrArg Fin.val h
  have ha := a.isLt; have hb := b.isLt
  simp only [slP] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-! ### The docks, tape by tape -/

theorem slE_zero : slE e hV ⟨0, by omega⟩ = d.pcT e hV ⟨66, by unfold restPc; omega⟩ := Fin.ext (by simp [slE, pcT])
theorem slE_one : slE e hV ⟨1, by omega⟩ = d.pcT e hV ⟨59, by unfold restPc; omega⟩ := Fin.ext (by simp [slE, pcT])
theorem slE_priv (j : Fin (2 + eX)) (h0 : j.val ≠ 0) (h1 : j.val ≠ 1) :
    slE e hV j = d.pcT e hV ⟨71 + (j.val - 2), by have := j.isLt; have := e.hres; unfold restPc; omega⟩ :=
  Fin.ext (by simp [slE, pcT, h0, h1]; omega)
theorem slE_off (x : Fin V) (hx : x.val ≠ d.B + 19 + 66) (hx1 : x.val ≠ d.B + 19 + 59)
    (hx2 : ¬ (d.B + 19 + 71 ≤ x.val ∧ x.val < d.B + 19 + 71 + eX)) : ∀ j, slE e hV j ≠ x := by
  intro j h
  have hv := congrArg Fin.val h
  have := j.isLt
  simp only [slE] at hv
  split_ifs at hv <;> omega

theorem slP_zero : slP e hV ⟨0, by omega⟩ = d.pcT e hV ⟨66, by unfold restPc; omega⟩ := Fin.ext (by simp [slP, pcT])
theorem slP_one : slP e hV ⟨1, by omega⟩ = d.pcT e hV ⟨60, by unfold restPc; omega⟩ := Fin.ext (by simp [slP, pcT])
theorem slP_priv (j : Fin (2 + pX)) (h0 : j.val ≠ 0) (h1 : j.val ≠ 1) :
    slP e hV j = d.pcT e hV ⟨71 + eX + (j.val - 2), by have := j.isLt; have := e.hres; unfold restPc; omega⟩ :=
  Fin.ext (by simp [slP, pcT, h0, h1]; omega)
theorem slP_off (x : Fin V) (hx : x.val ≠ d.B + 19 + 66) (hx1 : x.val ≠ d.B + 19 + 60)
    (hx2 : ¬ (d.B + 19 + 71 + eX ≤ x.val ∧ x.val < d.B + 19 + 71 + eX + pX)) : ∀ j, slP e hV j ≠ x := by
  intro j h
  have hv := congrArg Fin.val h
  have := j.isLt
  simp only [slP] at hv
  split_ifs at hv <;> omega

theorem g_lt61 (i : Fin 72) (hi : i.val < 61) :
    g e hV i = d.pcT e hV ⟨i.val, by have := e.hres; unfold restPc; omega⟩ := Fin.ext (by simp [g, gVn, pcT, hi])
theorem g_61 : g e hV 61 = d.rsT e hV 3 := Fin.ext (by simp [g, gVn, rsT, restPc])
theorem g_62 : g e hV 62 = d.rsT e hV 4 := Fin.ext (by simp [g, gVn, rsT, restPc])
theorem g_63 : g e hV 63 = d.encT hV 4 := Fin.ext (by simp [g, gVn, encT])
theorem g_64 : g e hV 64 = d.scr hV 11 := Fin.ext (by simp [g, gVn, SourceConstruction.Dims.scr])
theorem g_65 : g e hV 65 = d.scr hV 12 :=
  Fin.ext (by simp [g, gVn, SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV])
theorem g_coef (k : Fin 3) : g e hV ⟨66 + k.val, by omega⟩ = d.pcT e hV ⟨61 + k.val, by unfold restPc; omega⟩ :=
  Fin.ext (by have := k.isLt; simp [g, gVn, pcT]; split_ifs <;> omega)
theorem g_enc (k : Fin 3) : g e hV ⟨69 + k.val, by omega⟩ = d.encT hV ⟨k.val, by omega⟩ :=
  Fin.ext (by have := k.isLt; simp [g, gVn, encT]; split_ifs <;> omega)
theorem g_off (x : Fin V) (a1 : ¬ (d.B + 19 ≤ x.val ∧ x.val < d.B + 19 + 64))
    (a2 : x.val ≠ d.B + 19 + restPc eX pX gW + 3) (a3 : x.val ≠ d.B + 19 + restPc eX pX gW + 4)
    (a4 : ¬ (d.F + d.rt ≤ x.val ∧ x.val ≤ d.F + d.rt + 4 ∧ x.val ≠ d.F + d.rt + 3))
    (a5 : x.val ≠ d.scrV 11) (a6 : x.val ≠ d.scrV 11 + 1) : ∀ i, g e hV i ≠ x := by
  intro i h
  have hv := congrArg Fin.val h
  have := i.isLt
  simp only [restPc] at a2 a3
  simp only [g, gVn] at hv
  split_ifs at hv <;> omega

end Dims

/-- The back half's first three stages: frame the input, then the two metadata stages. -/
def stagesMachine {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt se.extra sp.extra gW) {V : Nat}
    (hV : d.U ≤ V) :=
  Composition.machine
    (SLoad.MaskFrame.machine (d.scr hV 5) (d.scr hV 6) (d.pcT e hV ⟨66, by unfold restPc; omega⟩)
      (d.pcT e hV ⟨67, by unfold restPc; omega⟩))
    (Composition.machine (RecoveryFocus.machine (Dims.slE e hV) se.machine)
      (RecoveryFocus.machine (Dims.slP e hV) sp.machine))

/-- The back half's machine. -/
def backMachine {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt se.extra sp.extra gW) {V : Nat}
    (hV : d.U ≤ V) :=
  Composition.machine (stagesMachine se sp e hV)
    (Composition.machine (Prologue.f6Full (Dims.g e hV))
      (Prologue.slopeMachine (Dims.lenTape e.ext hV) (d.rsT e hV 0) (d.rsT e hV 1)
        (Dims.csSlots e.ext hV 1) (d.pcT e hV ⟨68, by unfold restPc; omega⟩)
        (d.pcT e hV ⟨69, by unfold restPc; omega⟩)))

end
end NearCubicWires.SourceConstruction.Rest
end
