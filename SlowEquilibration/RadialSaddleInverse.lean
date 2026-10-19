-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

/-! The genuine smooth exterior inverse of d*k+sqrt(k^2-4*b), derived
directly from its explicit smaller quadratic root. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.RadialSaddleInverse
open Set
open scoped ContDiff
set_option maxHeartbeats 400000

def inverse (b d t : ℝ) : ℝ :=
  (d*t-Real.sqrt (t^2-4*b*(d^2-1)))/(d^2-1)

theorem discriminant_pos {b d t : ℝ} (hb : 0 < b) (hd : 1 < d)
    (ht : 2*d*Real.sqrt b < t) : 0 < t^2-4*b*(d^2-1) := by
  have htpos : 0 < t := lt_trans (by positivity) ht
  have hsq := (sq_lt_sq₀ (by positivity : 0 ≤ 2*d*Real.sqrt b) htpos.le).mpr ht
  rw [mul_pow,mul_pow,Real.sq_sqrt hb.le] at hsq
  norm_num only [OfNat.ofNat,Int.cast_ofNat] at hsq
  nlinarith

/-- The explicit root is strictly outside the edge and solves the true
unsquared radial equation, including the correct square-root branch. -/
theorem inverse_facts {b d t : ℝ} (hb : 0 < b) (hd : 1 < d)
    (ht : 2*d*Real.sqrt b < t) :
    2*Real.sqrt b < inverse b d t ∧
      d*inverse b d t+Real.sqrt ((inverse b d t)^2-4*b)=t := by
  let D := d^2-1
  let r := Real.sqrt (t^2-4*b*D)
  let k := inverse b d t
  have hD : 0 < D := by dsimp [D]; nlinarith
  have hdpos : 0 < d := by linarith
  have htpos : 0 < t := lt_trans (by positivity) ht
  have hDisc : 0 < t^2-4*b*D := discriminant_pos hb hd ht
  have hr : 0 < r := Real.sqrt_pos.mpr hDisc
  have hrSq : r^2=t^2-4*b*D := Real.sq_sqrt hDisc.le
  have hrlt : r < t := by nlinarith [mul_pos hb hD]
  have hdt : t < d*t := by nlinarith [mul_pos (sub_pos.mpr hd) htpos]
  have hk : 0 < k := div_pos (by change 0 < d*t-r;linarith) hD
  have hTSq := (sq_lt_sq₀ (by positivity : 0 ≤ 2*d*Real.sqrt b) htpos.le).mpr ht
  rw [mul_pow,mul_pow,Real.sq_sqrt hb.le] at hTSq
  have hGap : 0 < t^2-4*b*d^2 := by nlinarith
  have hRootComparison : (d*r)^2-t^2=D*(t^2-4*b*d^2) := by
    rw [mul_pow,hrSq]
    dsimp [D]
    ring
  have hRootGreater : t < d*r := by
    have hh : 0 < (d*r)^2-t^2 := by rw [hRootComparison];exact mul_pos hD hGap
    nlinarith [mul_pos hdpos hr]
  have hSlackEq : t-d*k=(d*r-t)/D := by
    dsimp [k,inverse]
    change t-d*((d*t-r)/D)=(d*r-t)/D
    field_simp [hD.ne']
    dsimp [D]
    ring
  have hSlack : 0 < t-d*k := by rw [hSlackEq];exact div_pos (sub_pos.mpr hRootGreater) hD
  have hIdentity : k^2-4*b-(t-d*k)^2=-(r^2-t^2+4*b*D)/D := by
    dsimp [k,inverse]
    change ((d*t-r)/D)^2-4*b-(t-d*((d*t-r)/D))^2=-(r^2-t^2+4*b*D)/D
    field_simp [hD.ne']
    dsimp [D]
    ring
  have hSquares : k^2-4*b=(t-d*k)^2 := by
    apply sub_eq_zero.mp
    rw [hIdentity,hrSq]
    ring
  have hEdge : 2*Real.sqrt b < k := by
    have hh := sq_pos_of_pos hSlack
    have hs := Real.sq_sqrt hb.le
    nlinarith [Real.sqrt_nonneg b,hSquares]
  refine ⟨hEdge,?_⟩
  change d*k+Real.sqrt (k^2-4*b)=t
  rw [hSquares,Real.sqrt_sq_eq_abs,abs_of_pos hSlack]
  ring

theorem inverse_unique {b d t : ℝ} (hb : 0 < b) (hd : 1 < d)
    (ht : 2*d*Real.sqrt b < t) {k : ℝ} (hk : 2*Real.sqrt b < k)
    (heq : d*k+Real.sqrt (k^2-4*b)=t) : k=inverse b d t := by
  obtain ⟨hRoot,hEq⟩ := inverse_facts hb hd ht
  have hkpos : 0 < k := lt_trans (by positivity) hk
  have hrpos : 0 < inverse b d t := lt_trans (by positivity) hRoot
  have hdpos : 0 < d := by linarith
  rcases lt_trichotomy k (inverse b d t) with hlt|he|hlt
  · have hs : Real.sqrt (k^2-4*b) ≤ Real.sqrt ((inverse b d t)^2-4*b) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hp := mul_lt_mul_of_pos_left hlt hdpos
    linarith
  · exact he
  · have hs : Real.sqrt ((inverse b d t)^2-4*b) ≤ Real.sqrt (k^2-4*b) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hp := mul_lt_mul_of_pos_left hlt hdpos
    linarith

/-- Infinite differentiability is proved for the actual explicit inverse
throughout its exterior domain, rather than supplied as an inverse premise. -/
theorem inverse_contDiffOn {b d : ℝ} (hb : 0 < b) (hd : 1 < d) :
    ContDiffOn ℝ ∞ (inverse b d) (Ioi (2*d*Real.sqrt b)) := by
  intro t ht
  have hDisc := discriminant_pos hb hd ht
  have hPoly : ContDiffAt ℝ ∞ (fun v : ℝ => v^2-4*b*(d^2-1)) t := by fun_prop
  have hRoot := hPoly.sqrt hDisc.ne'
  have hLinear : ContDiffAt ℝ ∞ (fun v : ℝ => d*v) t := by fun_prop
  exact ((hLinear.sub hRoot).div_const (d^2-1)).contDiffWithinAt

end SlowEquilibration.RadialSaddleInverse
