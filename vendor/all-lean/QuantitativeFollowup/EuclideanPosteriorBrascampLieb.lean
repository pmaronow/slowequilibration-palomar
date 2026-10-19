module
public import QuantitativeFollowup.PosteriorBrascampLieb
public import QuantitativeFollowup.EuclideanPrekopa

@[expose] public section

/-! Actual inverse-Hessian posterior variance in Euclidean coordinates.
Volume is the canonical Euclidean volume, not an assumed abstract law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativeFollowup

theorem posterior_variance_le_of_joint_convex_quadraticTilt_euclidean {d : ℕ}
    (V f g : (EuclideanSpace ℝ (Fin (d+1))) → ℝ)
    [IsProbabilityMeasure (posteriorDensityMeasure V)]
    (hV : Measurable V) (hf : Measurable f) (hg : Measurable g)
    (Kf Kg : ℝ) (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg)
    (hfb : ∀ x, |f x| ≤ Kf) (hgb : ∀ x, |g x| ≤ Kg)
    (ε : ℝ) (hε : 0 < ε)
    (hW : ConvexOn ℝ (Ioo (-ε) ε ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (d+1)))))
      (Function.uncurry (quadraticPosteriorPotential V f g))) :
    variance f (posteriorDensityMeasure V) ≤ ∫ x, g x ∂posteriorDensityMeasure V := by
  have hI (t : ℝ) : Integrable (fun x => Real.exp (-quadraticPosteriorPotential V f g t x)) := by
    have hi := integrable_quadraticTiltWeight (posteriorDensityMeasure V)
      f g hf hg Kf Kg hKf hKg hfb hgb t
    rw [posteriorDensityMeasure,integrable_withDensity_iff_integrable_smul'
      (by fun_prop : Measurable (fun x => ENNReal.ofReal (Real.exp (-V x))))
      (.of_forall fun x => ENNReal.ofReal_lt_top),posterior_quadratic_weight_eq] at hi
    exact hi
  have hc := concaveOn_log_integral_exp_neg_euclidean (Ioo (-ε) ε) (convex_Ioo _ _)
    (quadraticPosteriorPotential V f g) hW
    (fun t _ht => by unfold quadraticPosteriorPotential; fun_prop) (fun t _ht => hI t)
  apply variance_le_of_concave_quadraticTilt (posteriorDensityMeasure V)
    f g hf hg Kf Kg hKf hKg hfb hgb ε hε
  convert hc using 1
  funext t
  rw [integral_posterior_quadraticTilt V f g hV]


theorem posterior_brascamp_lieb_euclidean {d : ℕ}
    (V f : (EuclideanSpace ℝ (Fin (d+1))) → ℝ) (v : (EuclideanSpace ℝ (Fin (d+1))) → (EuclideanSpace ℝ (Fin (d+1))))
    [IsProbabilityMeasure (posteriorDensityMeasure V)]
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 (inverseHessianEnergy f v))
    (r Kv Kf Kg KF KG₁ KG₂ : ℝ)
    (hr : 0 < r) (hKv : 0 ≤ Kv) (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg)
    (hKF : 0 ≤ KF) (hKG₁ : 0 ≤ KG₁) (hKG₂ : 0 ≤ KG₂)
    (hcoercive : ∀ x z, r*‖z‖^2 ≤ directionalHessian V x z)
    (hsymmetric : ∀ x z w, fderiv ℝ (fderiv ℝ V) x z w =
      fderiv ℝ (fderiv ℝ V) x w z)
    (hsolve : ∀ x z, fderiv ℝ (fderiv ℝ V) x (v x) z=fderiv ℝ f x z)
    (hvb : ∀ x, ‖v x‖ ≤ Kv)
    (hfb : ∀ x, |f x| ≤ Kf)
    (hgb : ∀ x, |inverseHessianEnergy f v x| ≤ Kg)
    (hF : ∀ x z, |directionalHessian f x z| ≤ KF*‖z‖^2)
    (hG₁ : ∀ x z, |fderiv ℝ (inverseHessianEnergy f v) x z| ≤ KG₁*‖z‖)
    (hG₂ : ∀ x z, |directionalHessian (inverseHessianEnergy f v) x z| ≤ KG₂*‖z‖^2) :
    variance f (posteriorDensityMeasure V) ≤
      ∫ x, inverseHessianEnergy f v x ∂posteriorDensityMeasure V := by
  let g := inverseHessianEnergy f v
  have hi : Integrable g (posteriorDensityMeasure V) := by
    apply Integrable.mono' (integrable_const Kg) hg.continuous.aestronglyMeasurable
    exact .of_forall (fun x => by simpa only [Real.norm_eq_abs] using hgb x)
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨m,hm,hmr,hmδ⟩ := exists_strict_hessian_block_bound r δ Kv hr hδ hKv
  let ε := min 1 (m/(KF+KG₁+KG₂+1))
  have hden : 0<KF+KG₁+KG₂+1 := by positivity
  have hε : 0<ε := lt_min (by norm_num) (div_pos hm hden)
  have hε₁ : ε ≤ 1 := min_le_left _ _
  have hsmall : ε*(KF+KG₁+KG₂) ≤ m := by
    have hh : ε*(KF+KG₁+KG₂+1) ≤ m :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith [hε.le]
  let gδ := fun x => g x+δ
  have hgδ : ContDiff ℝ 2 gδ := hg.add contDiff_const
  have hgd₁ (x z : EuclideanSpace ℝ (Fin (d+1))) : fderiv ℝ gδ x z=fderiv ℝ g x z := by
    rw [show gδ=(fun x => g x+δ) by rfl,fderiv_add_const]
  have hgd₂ (x z : EuclideanSpace ℝ (Fin (d+1))) : directionalHessian gδ x z=directionalHessian g x z := by
    have heq : fderiv ℝ gδ=fderiv ℝ g := by
      funext y
      exact ContinuousLinearMap.ext (fun w => hgd₁ y w)
    unfold directionalHessian
    rw [heq]
  have hbase (x z : EuclideanSpace ℝ (Fin (d+1))) (τ : ℝ) :
      m*(‖z‖^2+τ^2) ≤ directionalHessian V x z-
        2*τ*fderiv ℝ f x z+τ^2*gδ x := by
    have hh := strict_bilinear_block_bound (fderiv ℝ (fderiv ℝ V) x)
      (v x) z τ r δ Kv m hKv hm.le (hcoercive x) (hsymmetric x)
      (hvb x) hmr hmδ
    simpa only [directionalHessian,hsolve,gδ,g,inverseHessianEnergy] using hh
  have hW := convexOn_quadraticTilt_of_hessian_bounds V f gδ hV hf hgδ
    m KF KG₁ KG₂ ε hm.le hKF hKG₁ hKG₂ hε hε₁ hsmall hbase hF
    (fun x z => by rw [hgd₁]; exact hG₁ x z)
    (fun x z => by rw [hgd₂]; exact hG₂ x z)
  have hb (x : EuclideanSpace ℝ (Fin (d+1))) : |gδ x| ≤ Kg+δ := by
    calc
      |g x+δ| ≤ |g x|+|δ| := abs_add_le _ _
      _ ≤ Kg+δ := by
        rw [abs_of_pos hδ]
        simpa only [g,add_comm] using add_le_add_right (hgb x) δ
  have hv := posterior_variance_le_of_joint_convex_quadraticTilt_euclidean V f gδ
    hV.continuous.measurable hf.continuous.measurable hgδ.continuous.measurable
    Kf (Kg+δ) hKf (by positivity) hfb hb ε hε hW
  have heq : (∫ x, gδ x ∂posteriorDensityMeasure V) =
      (∫ x, g x ∂posteriorDensityMeasure V)+δ := by
    rw [show gδ=(fun x => g x+δ) by rfl,integral_add hi (integrable_const δ)]
    simp
  rw [heq] at hv
  exact hv


end QuantitativeFollowup
