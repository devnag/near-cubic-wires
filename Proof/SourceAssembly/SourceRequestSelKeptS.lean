import Proof.SourceAssembly.SourceRequestSelDockP
import Proof.SourceAssembly.SourceSkelInitXA
import Proof.SourceAssembly.SourceSkelParams

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton.InitS (initResVal valAllX cwidOf)
open NearCubicWires.SourceRequest.SelFront (NF)
noncomputable section

theorem initRes_resW (Rc q L CP DP CW DW CL DL tg DD CD Dcw Ccw b : Nat) (MB : List Bool) (i : Nat) (hi : i < 10) :
    initResVal Rc q L CP DP CW DW CL DL false tg (valAllX false L q Rc DD CD Dcw Ccw CL DL b MB) i =
      ZeroPadding.pad Rc (resW q (CP*(q+1)^DP) (CW*(q+1)^DW) (CL*(q+1)^DL) L tg (cwidOf false (CL*(q+1)^DL))
        (Ccw*(q+1)^Dcw) i) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

theorem initRes_resWS (Rc q L CP DP CW DW CL DL tg DD CD Dcw Ccw b : Nat) (MB : List Bool) (i : Nat) (hi : i < 10) :
    initResVal Rc q L CP DP CW DW CL DL true tg (valAllX true L q Rc DD CD Dcw Ccw CL DL b MB) i =
      ZeroPadding.pad Rc (resWS q (CP*(q+1)^DP) (CW*(q+1)^DW) (CL*(q+1)^DL) L tg (cwidOf true (CL*(q+1)^DL))
        (Ccw*(q+1)^Dcw) i) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

theorem initRes_D (Rc q L CP DP CW DW CL DL : Nat) (mode : Bool) (tg DD CD Dcw Ccw b : Nat) (MB : List Bool) :
    initResVal Rc q L CP DP CW DW CL DL mode tg (valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB) 12 =
      ZeroPadding.pad Rc (List.replicate (CD*(q+1)^DD) true) := rfl

theorem initRes_b (Rc q L CP DP CW DW CL DL : Nat) (mode : Bool) (tg DD CD Dcw Ccw b : Nat) (MB : List Bool) :
    initResVal Rc q L CP DP CW DW CL DL mode tg (valAllX mode L q Rc DD CD Dcw Ccw CL DL b MB) 19 =
      ZeroPadding.pad Rc (List.replicate b true) := rfl

section kept
variable {d : SourceConstruction.Dims} {eX pX gW V : Nat} (cacheT : Fin 19 → Fin V) (terminal : Fin V)
  (K0 : Fin V → List Bool) (KH0 : Fin V → Nat) (NR : Nat) (val : Nat → List Bool)
  (hKhigh : ∀ x : Fin V, Rest.srcK4 (d := d) (eX := eX) (pX := pX) (gW := gW) cacheT terminal x → d.F ≤ x.val →
    ∃ i, i < NR ∧ x.val = d.B + 29 + restPc eX pX gW + i ∧ K0 x = val i ∧ KH0 x = 0)

/-- `hrT i` (`i < 10`) is in `srcK4`. -/
theorem srcK4_hrT (i : Nat) (hi : i < 10) (x : Fin V) (hx : x.val = d.B + 29 + restPc eX pX gW + i) :
    Rest.srcK4 (d := d) (eX := eX) (pX := pX) (gW := gW) cacheT terminal x := by
  left; right; right; right
  unfold SourceConstruction.Dims.HiRes
  omega

/-- `hrD = B+41+Pc` is in `srcK4`. -/
theorem srcK4_hrD (x : Fin V) (hx : x.val = d.B + 41 + restPc eX pX gW) :
    Rest.srcK4 (d := d) (eX := eX) (pX := pX) (gW := gW) cacheT terminal x := by
  right; right; right; left; exact hx

/-- `hrG 5 = B+48+Pc` is in `srcK4`. -/
theorem srcK4_hrG5 (x : Fin V) (hx : x.val = d.B + 48 + restPc eX pX gW) :
    Rest.srcK4 (d := d) (eX := eX) (pX := pX) (gW := gW) cacheT terminal x := by
  right; right; right; right; left; omega

end kept

theorem hres_resOfX {a : RepairRepresentation.DecompositionAlgorithm} (D : SourceSkeleton.RestData a) (xR : Nat) (h : 10 ≤ xR) :
    49 + restPc D.se.extra D.sp.extra D.gW ≤ SourceSkeleton.resOfX D xR := by
  unfold SourceSkeleton.resOfX; omega

theorem ten_le_xROf (hR hV : SourceBudget.ParNat) (sources : RepairSource.EightSources) (gamma : Real) (hg : 0 < gamma)
    (hh : gamma < 1/2) (p : RepairSource.CloseoutFinal.Parameters sources gamma) :
    10 ≤ SourceSkeleton.Params.xROf hR hV sources gamma hg hh p := by
  unfold SourceSkeleton.Params.xROf; omega

theorem hG_thr (sources : RepairSource.EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : RepairSource.CloseoutFinal.Parameters sources gamma) :
    NF + (19 + 4 * tT (RepairSource.CloseoutFinal.decompositionOf sources)) ≤
      SourceSkeleton.Params.gG7 sources gamma hg hh p := by
  have e : tT (RepairSource.CloseoutFinal.decompositionOf sources) =
      3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (RepairSource.CloseoutFinal.decompositionOf sources) := rfl
  have hm := le_max_left (3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (RepairSource.CloseoutFinal.decompositionOf sources)) 3778
  show NF + (19 + 4 * tT (RepairSource.CloseoutFinal.decompositionOf sources)) ≤
    7000 + 19 + 4 * max (3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (RepairSource.CloseoutFinal.decompositionOf sources)) 3778
  rw [e]; unfold NF; omega

theorem hG_sym (sources : RepairSource.EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : RepairSource.CloseoutFinal.Parameters sources gamma) :
    NF + (19 + 4 * tS) ≤ SourceSkeleton.Params.gG7 sources gamma hg hh p := by
  have hm := le_max_right (3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (RepairSource.CloseoutFinal.decompositionOf sources)) 3778
  show NF + (19 + 4 * tS) ≤
    7000 + 19 + 4 * max (3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (RepairSource.CloseoutFinal.decompositionOf sources)) 3778
  unfold NF tS; omega

end
end NearCubicWires.SourceRequest.SelLocal

