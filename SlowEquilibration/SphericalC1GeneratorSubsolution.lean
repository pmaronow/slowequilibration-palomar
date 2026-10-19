-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalC1Dynkin
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Actual C1-gradient spherical transition expectations obey scalar
generator subsolution bounds. This is derived from the physical Dynkin
formula, continuous paths and compact-sphere domination. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalC1Dynamics
open MeasureTheory ProbabilityTheory Set Filter Topology StochasticCalculus
open SphericalAging HardSphereDynamics LocalSDE SphericalModel SphericalDynamics
open ActualC2Dynkin SharpRadialMoment PredictableDriftTime
open SphericalReversibility.Ito
open scoped NNReal ContDiff
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

lemma expectation_hasDerivAt_pos (hN : N≠0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (hx : OnSphere x) {f : State N → ℝ}
    (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => expectation β g hg s.toNNReal f x)
      (expectation β g hg t.toNNReal (coefficientGenerator β g f) x) t :=
  Ito.physical_C2_hasDerivAt (FixedCoefficients.canonicalDriver N) β g hg
    (fun T => process_randomStrongSolution hN β g hg x hx T)
    (process_onSphere hN β g hg x hx) (cutoffRadius N) (cutoffRadius_pos N)
    (cutoffRadius_contains_sphere N) hf t ht

lemma expectation_continuous_time (hN : N≠0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (hx : OnSphere x) {f : State N → ℝ} (hf : Continuous f) :
    Continuous (fun t : ℝ≥0 => expectation β g hg t f x) := by
  have hX := process_randomStrongSolution hN β g hg x hx 0
  obtain ⟨K,hK⟩ := sphere_observable_bound f hf (cutoffRadius N) (cutoffRadius_pos N)
    (cutoffRadius_contains_sphere N) (process β g hg x) (process_onSphere hN β g hg x hx)
  exact SphericalAging.SharpRadialMoment.firstMoment_continuous (P := VectorBrownian.law N)
    (fun t omega => f (process β g hg x t omega))
    (fun t => hf.comp_stronglyMeasurable (hX.2.1 t))
    (hX.2.2.1.mono (fun _ hc => hf.comp hc)) K hK

lemma expectation_generator_le (hN : N≠0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (hx : OnSphere x) {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (a : ℝ) (hgen : ∀ y,OnSphere y → coefficientGenerator β g f y≤a*f y)
    (t : ℝ≥0) :
    expectation β g hg t (coefficientGenerator β g f) x≤a*expectation β g hg t f x := by
  have hX := process_randomStrongSolution hN β g hg x hx 0
  have hs := process_onSphere hN β g hg x hx
  obtain ⟨Kf,hKf⟩ := sphere_observable_bound f hf.continuous (cutoffRadius N)
    (cutoffRadius_pos N) (cutoffRadius_contains_sphere N) (process β g hg x) hs
  obtain ⟨KG,hKG⟩ := sphere_observable_bound _ (Ito.generator_continuous β g hg hf)
    (cutoffRadius N) (cutoffRadius_pos N) (cutoffRadius_contains_sphere N) (process β g hg x) hs
  have hiF : Integrable (fun omega => f (process β g hg x t omega)) (VectorBrownian.law N) :=
    Integrable.of_bound ((hf.continuous.comp_stronglyMeasurable (hX.2.1 t)).mono
      ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le t)).aestronglyMeasurable Kf
      (hKf.mono (fun _ h => h t))
  have hiG : Integrable (fun omega => coefficientGenerator β g f (process β g hg x t omega))
      (VectorBrownian.law N) :=
    Integrable.of_bound (((Ito.generator_continuous β g hg hf).comp_stronglyMeasurable
      (hX.2.1 t)).mono ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le t)).aestronglyMeasurable
      KG (hKG.mono (fun _ h => h t))
  have hb := integral_mono_ae hiG (hiF.const_mul a) (hs.mono (fun _ h => hgen _ (h t)))
  simpa only [expectation,integral_const_mul] using hb

/-- Actual generator subsolutions satisfy the exponential semigroup bound.
The differential inequality is derived from physical Dynkin, rather than
supplied as a transition estimate. -/
theorem expectation_le_exp_mul (hN : N ≠ 0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (hx : OnSphere x) {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (a : ℝ) (hgen : ∀ y, OnSphere y → coefficientGenerator β g f y ≤ a * f y)
    (t : ℝ≥0) : expectation β g hg t f x ≤ Real.exp (a * (t : ℝ)) * f x := by
  let E : ℝ → ℝ := fun s => expectation β g hg s.toNNReal f x
  let G : ℝ → ℝ := fun s => expectation β g hg s.toNNReal (coefficientGenerator β g f) x
  have hEc : Continuous E :=
    (expectation_continuous_time hN β g hg x hx hf.continuous).comp continuous_real_toNNReal
  have hF : Continuous (fun s : ℝ => Real.exp (-a * s) * E s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hEc
  have hD (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun r : ℝ => Real.exp (-a * r) * E r)
        (Real.exp (-a * s) * (G s - a * E s)) s := by
    have hExp := (((hasDerivAt_id s).const_mul (-a)).exp)
    have hE := expectation_hasDerivAt_pos hN β g hg x hx hf s hs
    convert hExp.mul hE using 1
    · funext r
      rfl
    · dsimp only [E,G,id_eq]
      ring
  have hmono : AntitoneOn (fun s : ℝ => Real.exp (-a * s) * E s) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hF.continuousOn
      (f' := fun s => Real.exp (-a * s) * (G s - a * E s))
    · intro s hs
      rw [interior_Ici,mem_Ioi] at hs
      exact (hD s hs).hasDerivWithinAt
    · intro s hs
      have hgE := expectation_generator_le hN β g hg x hx hf a hgen s.toNNReal
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hgE)
  have hzero : E 0 = f x := by
    dsimp [E]
    rw [Real.toNNReal_zero,expectation_dynkin hN β g hg x hx hf 0]
    simp
  have hb := hmono (by simp : (0 : ℝ) ∈ Ici 0)
    (show (t : ℝ) ∈ Ici 0 from t.coe_nonneg) t.coe_nonneg
  simp only [mul_zero,Real.exp_zero,one_mul,hzero] at hb
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos (a * (t : ℝ))).le
  rw [← mul_assoc,← Real.exp_add] at hm
  have he : a * (t : ℝ) + -a * (t : ℝ) = 0 := by ring
  rw [he,Real.exp_zero,one_mul] at hm
  simpa only [E,Real.toNNReal_coe] using hm

lemma coefficientGenerator_fun_neg (β : ℝ) (g : State N → State N) (f : State N → ℝ) (x : State N) :
    coefficientGenerator β g (fun y => -f y) x = -coefficientGenerator β g f x := by
  have he : fderiv ℝ (fun y => -f y) = fun y => -fderiv ℝ f y := by
    funext y
    exact fderiv_fun_neg
  unfold coefficientGenerator SphericalAging.MultivariateTaylor.Hessian
  rw [fderiv_fun_neg,he,fderiv_fun_neg]
  simp only [_root_.neg_apply,Finset.sum_neg_distrib]
  ring

theorem expectation_ge_exp_mul (hN : N ≠ 0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (hx : OnSphere x) {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (a : ℝ) (hgen : ∀ y,OnSphere y → a * f y ≤ coefficientGenerator β g f y)
    (t : ℝ≥0) : Real.exp (a * (t : ℝ)) * f x ≤ expectation β g hg t f x := by
  have hi := expectation_le_exp_mul hN β g hg x hx hf.neg a (fun y hy => by
    rw [coefficientGenerator_fun_neg]
    nlinarith [hgen y hy]) t
  have he : expectation β g hg t (fun y => -f y) x = -expectation β g hg t f x :=
    integral_neg _
  rw [he] at hi
  nlinarith

end SlowEquilibration.SphericalC1Dynamics
