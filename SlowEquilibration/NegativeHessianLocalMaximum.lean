-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NegativeDefiniteOperators
public import Mathlib.Analysis.Calculus.DerivativeTest

/-! Genuine second-derivative tests for finite-dimensional real fields. -/
@[expose] public section
namespace SlowEquilibration.NegativeDefiniteOperators
open Set Filter Metric
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

lemma second_deriv_nonpos_of_localMax {f : ℝ → ℝ} {x : ℝ}
    (hf : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra! hp
  have hm := isLocalMin_of_deriv_deriv_pos hp hf.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hf,hm] with y hy hy'
    exact le_antisymm hy hy'
  have hh := he.deriv.deriv_eq
  simp at hh
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A critical point with negative-definite derivative of its true gradient
is a local maximum. The gradient relation holds on a genuine neighborhood. -/
theorem isLocalMax_of_negative_gradient {f : E → ℝ} {G : E → E} {x : E}
    (hgrad : ∀ᶠ y in 𝓝 x, HasFDerivAt f (innerSL ℝ (G y)) y ∧ DifferentiableAt ℝ G y)
    (hcont : ContinuousAt (fderiv ℝ G) x) (hzero : G x=0)
    (hneg : NegativeDefinite (fderiv ℝ G x)) : IsLocalMax f x := by
  have hn := hcont.eventually (isOpen_negativeDefinite.mem_nhds hneg)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hgrad.and hn)
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨r,hr,?_⟩
  intro y hy
  let d := y-x
  let γ : ℝ → E := fun t => x+t • d
  have hdγ (t : ℝ) : HasDerivAt γ d t := by
    simpa only [one_smul, id_eq, γ] using ((hasDerivAt_id t).smul_const d).const_add x
  have hγ (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : dist (γ t) x < r := by
    change dist (x+t • (y-x)) x < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt (by simpa only [dist_eq_norm] using hy)
  let g : ℝ → ℝ := f ∘ γ
  let q : ℝ → ℝ := fun t => inner ℝ (G (γ t)) d
  have hdg (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt g (q t) t := by
    exact (hball (hγ t ht)).1.1.comp_hasDerivAt t (hdγ t)
  have hdq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt q (inner ℝ ((fderiv ℝ G (γ t)) d) d) t := by
    simpa only [inner_zero_right, zero_add, Function.comp_def, q] using
      (((hball (hγ t ht)).1.2.hasFDerivAt.comp_hasDerivAt t (hdγ t)).inner ℝ (hasDerivAt_const t d))
  have hqnonpos (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      inner ℝ ((fderiv ℝ G (γ t)) d) d ≤ 0 := by
    by_cases hd : d=0
    · simp [hd]
    · rw [real_inner_comm]
      exact ((hball (hγ t ht)).2 d hd).le
  have hqa : AntitoneOn q (Icc (0:ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t ht => (hdq t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hdq t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hqnonpos t (interior_subset ht))
  have hga : AntitoneOn g (Icc (0:ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t ht => (hdg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hdg t (interior_subset ht)).hasDerivWithinAt) (by
        intro t ht
        have hh := hqa (show (0:ℝ) ∈ Icc (0:ℝ) 1 by simp) (interior_subset ht) (interior_subset ht).1
        simpa only [q,γ,zero_smul,add_zero,hzero,inner_zero_left] using hh)
  have hh := hga (show (0:ℝ) ∈ Icc (0:ℝ) 1 by simp) (show (1:ℝ) ∈ Icc (0:ℝ) 1 by simp) (by norm_num)
  simpa only [g,γ,d,Function.comp_def,one_smul,zero_smul,add_sub_cancel,add_zero] using hh

omit [FiniteDimensional ℝ E] in
/-- Every directional quadratic Hessian at an actual local maximum is nonpositive. -/
theorem gradient_quadratic_nonpos_of_localMax {f : E → ℝ} {G : E → E} {x : E}
    (hgrad : ∀ᶠ y in 𝓝 x, HasFDerivAt f (innerSL ℝ (G y)) y ∧ DifferentiableAt ℝ G y)
    (hmax : IsLocalMax f x) (v : E) : inner ℝ v ((fderiv ℝ G x) v) ≤ 0 := by
  let γ : ℝ → E := fun t => x+t • v
  let g : ℝ → ℝ := f ∘ γ
  let q : ℝ → ℝ := fun t => inner ℝ (G (γ t)) v
  have hdγ (t : ℝ) : HasDerivAt γ v t := by
    simpa only [one_smul, id_eq, γ] using ((hasDerivAt_id t).smul_const v).const_add x
  have hγ0 : γ 0=x := by simp [γ]
  have ht : Tendsto γ (𝓝 0) (𝓝 x) := hγ0 ▸ (hdγ 0).continuousAt
  have he : deriv g =ᶠ[𝓝 0] q := by
    filter_upwards [ht.eventually hgrad] with t ht
    exact (ht.1.comp_hasDerivAt t (hdγ t)).deriv
  have hq : HasDerivAt q (inner ℝ ((fderiv ℝ G x) v) v) 0 := by
    have hdG := (hgrad.self_of_nhds).2.hasFDerivAt
    rw [← hγ0] at hdG
    simpa only [inner_zero_right, zero_add, Function.comp_def, q, hγ0] using
      (hdG.comp_hasDerivAt 0 (hdγ 0)).inner ℝ (hasDerivAt_const (0:ℝ) v)
  have hm : IsLocalMax g 0 := by
    apply IsLocalMax.comp_continuous (g := γ) (b := 0)
    · rw [hγ0]
      exact hmax
    · exact (hdγ 0).continuousAt
  have hc : ContinuousAt g 0 := by
    change Tendsto (f ∘ γ) (𝓝 0) (𝓝 (f (γ 0)))
    rw [hγ0]
    exact ((hgrad.self_of_nhds).1.continuousAt.tendsto.comp ht)
  have hh := second_deriv_nonpos_of_localMax hm hc
  rw [he.deriv_eq,hq.deriv,real_inner_comm] at hh
  exact hh

lemma negativeDefinite_of_nonpos_of_det_ne_zero (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) (hd : T.det ≠ 0)
    (hn : ∀ v : E, inner ℝ v (T v) ≤ 0) : NegativeDefinite T := by
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    exact not_ne_iff.mp (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hd)
  have he (i : Fin (Module.finrank ℝ E)) : hT.eigenvalues rfl i < 0 := by
    let B := hT.eigenvectorBasis rfl
    have hB : ‖B i‖=1 := B.norm_eq_one i
    have hEig : T (B i)=hT.eigenvalues rfl i • B i := hT.apply_eigenvectorBasis rfl i
    have hn' := hn (B i)
    rw [hEig,real_inner_smul_right,real_inner_self_eq_norm_sq,hB] at hn'
    have hne : hT.eigenvalues rfl i ≠ 0 := by
      intro h0
      have hz : T (B i)=T 0 := by simp only [hEig,h0,zero_smul,map_zero]
      exact B.orthonormal.ne_zero i (hinj hz)
    exact lt_of_le_of_ne (by simpa using hn') hne
  simpa only [zero_smul,sub_zero] using (negativeDefinite_shift_iff T hT rfl 0).mpr he

end
end SlowEquilibration.NegativeDefiniteOperators
