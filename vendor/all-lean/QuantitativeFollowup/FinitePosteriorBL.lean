module
public import QuantitativeFollowup.FiniteEuclideanPrekopa
public import QuantitativeFollowup.CanonicalJetBounds

@[expose] public section

/-! Genuine Brascamp--Lieb on any nonempty finite Euclidean index set.
Only the Prékopa marginal step uses a volume-preserving reindexing; the
quadratic-tilt and constructed inverse-Hessian proof stays on the actual
original coordinate space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativeFollowup
set_option maxSynthPendingDepth 128
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem posterior_variance_le_of_joint_convex_quadraticTilt_finite     (V f g : (EuclideanSpace ℝ ι) → ℝ)
    [IsProbabilityMeasure (posteriorDensityMeasure V)]
    (hV : Measurable V) (hf : Measurable f) (hg : Measurable g)
    (Kf Kg : ℝ) (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg)
    (hfb : ∀ x, |f x| ≤ Kf) (hgb : ∀ x, |g x| ≤ Kg)
    (ε : ℝ) (hε : 0 < ε)
    (hW : ConvexOn ℝ (Ioo (-ε) ε ×ˢ (univ : Set (EuclideanSpace ℝ ι)))
      (Function.uncurry (quadraticPosteriorPotential V f g))) :
    variance f (posteriorDensityMeasure V) ≤ ∫ x, g x ∂posteriorDensityMeasure V := by
  have hI (t : ℝ) : Integrable (fun x => Real.exp (-quadraticPosteriorPotential V f g t x)) := by
    have hi := integrable_quadraticTiltWeight (posteriorDensityMeasure V)
      f g hf hg Kf Kg hKf hKg hfb hgb t
    rw [posteriorDensityMeasure,integrable_withDensity_iff_integrable_smul'
      (by fun_prop : Measurable (fun x => ENNReal.ofReal (Real.exp (-V x))))
      (.of_forall fun x => ENNReal.ofReal_lt_top),posterior_quadratic_weight_eq] at hi
    exact hi
  have hc := concaveOn_log_integral_exp_neg_finite_euclidean (Ioo (-ε) ε) (convex_Ioo _ _)
    (quadraticPosteriorPotential V f g) hW
    (fun t _ht => by unfold quadraticPosteriorPotential; fun_prop) (fun t _ht => hI t)
  apply variance_le_of_concave_quadraticTilt (posteriorDensityMeasure V)
    f g hf hg Kf Kg hKf hKg hfb hgb ε hε
  convert hc using 1
  funext t
  rw [integral_posterior_quadraticTilt V f g hV]


theorem posterior_brascamp_lieb_finite     (V f : (EuclideanSpace ℝ ι) → ℝ) (v : (EuclideanSpace ℝ ι) → (EuclideanSpace ℝ ι))
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
  have hgd₁ (x z : EuclideanSpace ℝ ι) : fderiv ℝ gδ x z=fderiv ℝ g x z := by
    rw [show gδ=(fun x => g x+δ) by rfl,fderiv_add_const]
  have hgd₂ (x z : EuclideanSpace ℝ ι) : directionalHessian gδ x z=directionalHessian g x z := by
    have heq : fderiv ℝ gδ=fderiv ℝ g := by
      funext y
      exact ContinuousLinearMap.ext (fun w => hgd₁ y w)
    unfold directionalHessian
    rw [heq]
  have hbase (x z : EuclideanSpace ℝ ι) (τ : ℝ) :
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
  have hb (x : EuclideanSpace ℝ ι) : |gδ x| ≤ Kg+δ := by
    calc
      |g x+δ| ≤ |g x|+|δ| := abs_add_le _ _
      _ ≤ Kg+δ := by
        rw [abs_of_pos hδ]
        simpa only [g,add_comm] using add_le_add_right (hgb x) δ
  have hv := posterior_variance_le_of_joint_convex_quadraticTilt_finite V f gδ
    hV.continuous.measurable hf.continuous.measurable hgδ.continuous.measurable
    Kf (Kg+δ) hKf (by positivity) hfb hb ε hε hW
  have heq : (∫ x, gδ x ∂posteriorDensityMeasure V) =
      (∫ x, g x ∂posteriorDensityMeasure V)+δ := by
    rw [show gδ=(fun x => g x+δ) by rfl,integral_add hi (integrable_const δ)]
    simp
  rw [heq] at hv
  exact hv


theorem posterior_brascamp_lieb_operator_finite     (V f : EuclideanSpace ℝ ι → ℝ)
    (A : EuclideanSpace ℝ ι →
      EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    [IsProbabilityMeasure (posteriorDensityMeasure V)]
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hA : ContDiff ℝ 2 A) (hb : ContDiff ℝ 2 b)
    (hhessian : ∀ x z w, fderiv ℝ (fderiv ℝ V) x z w=inner ℝ (A x z) w)
    (hgrad : ∀ x z, fderiv ℝ f x z=inner ℝ (b x) z)
    (r A₁ A₂ B₀ B₁ B₂ Kf : ℝ)
    (hr : 0<r) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hKf : 0 ≤ Kf)
    (hcoercive : ∀ x z, r*‖z‖^2 ≤ inner ℝ z (A x z))
    (hfb : ∀ x, |f x| ≤ Kf)
    (ha₁ : ∀ x z, ‖fderiv ℝ A x z‖ ≤ A₁*‖z‖)
    (ha₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ A) x z z‖ ≤ A₂*‖z‖^2)
    (hb₀ : ∀ x, ‖b x‖ ≤ B₀)
    (hb₁ : ∀ x z, ‖fderiv ℝ b x z‖ ≤ B₁*‖z‖)
    (hb₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ b) x z z‖ ≤ B₂*‖z‖^2) :
    variance f (posteriorDensityMeasure V) ≤
      ∫ x, inner ℝ (b x) ((Ring.inverse (A x)) (b x)) ∂posteriorDensityMeasure V := by
  let v := inverseFamily A b
  let L := r⁻¹
  let V₀ := L*B₀
  let V₁ := L*(B₁+A₁*L*B₀)
  let V₂ := L*(B₂+A₂*L*B₀+2*A₁*L*(B₁+A₁*L*B₀))
  have hL : 0 ≤ L := inv_nonneg.mpr hr.le
  have hunit (x : EuclideanSpace ℝ ι) : IsUnit (A x) :=
    isUnit_of_coercive (A x) r hr (hcoercive x)
  have hI (x : EuclideanSpace ℝ ι) : ‖Ring.inverse (A x)‖ ≤ L :=
    norm_ringInverse_le_of_coercive (A x) r hr (hcoercive x)
  have hv : ContDiff ℝ 2 v := contDiff_inverseFamily A b hA hb hunit
  have hv₀ (x : EuclideanSpace ℝ ι) : ‖v x‖ ≤ V₀ :=
    inverseFamily_norm_le A b L B₀ hL hI hb₀ x
  have hv₁ (x z : EuclideanSpace ℝ ι) : ‖fderiv ℝ v x z‖ ≤ V₁*‖z‖ :=
    inverseFamily_directional_norm_le A b hA hb hunit L A₁ B₀ B₁
      hL hA₁ hB₀ hB₁ hI hb₀ ha₁ hb₁ x z
  have hv₂ (x z : EuclideanSpace ℝ ι) :
      ‖fderiv ℝ (fderiv ℝ v) x z z‖ ≤ V₂*‖z‖^2 :=
    inverseFamily_second_directional_norm_le A b hA hb hunit L A₁ A₂ B₀ B₁ B₂
      hL hA₁ hA₂ hB₀ hB₁ hB₂ hI hb₀ ha₁ ha₂ hb₁ hb₂ x z
  have hV₀ : 0 ≤ V₀ := by positivity
  have hV₁ : 0 ≤ V₁ := by positivity
  have hV₂ : 0 ≤ V₂ := by positivity
  have henergy : inverseHessianEnergy f v=(fun x => inner ℝ (b x) (v x)) := by
    funext x
    exact hgrad x (v x)
  obtain ⟨he₀,he₁,he₂⟩ := innerFamily_bounds b v hb hv B₀ B₁ B₂ V₀ V₁ V₂
    hB₀ hB₁ hB₂ hV₀ hV₁ hV₂ hb₀ hv₀ hb₁ hv₁ hb₂ hv₂
  have hF (x z : EuclideanSpace ℝ ι) :
      |directionalHessian f x z| ≤ B₁*‖z‖^2 := by
    rw [directionalHessian_eq_inner_gradient_derivative f b hf hb hgrad]
    calc
      _ ≤ ‖fderiv ℝ b x z‖*‖z‖ := abs_real_inner_le_norm _ _
      _ ≤ (B₁*‖z‖)*‖z‖ := mul_le_mul_of_nonneg_right (hb₁ x z) (norm_nonneg _)
      _ = B₁*‖z‖^2 := by ring
  have hsolve (x z : EuclideanSpace ℝ ι) :
      fderiv ℝ (fderiv ℝ V) x (v x) z=fderiv ℝ f x z := by
    rw [hhessian,inverseFamily_equation A b hunit,hgrad]
  have hco (x z : EuclideanSpace ℝ ι) :
      r*‖z‖^2 ≤ directionalHessian V x z := by
    rw [directionalHessian,hhessian,real_inner_comm z (A x z)]
    exact hcoercive x z
  have hsym (x z w : EuclideanSpace ℝ ι) :
      fderiv ℝ (fderiv ℝ V) x z w=fderiv ℝ (fderiv ℝ V) x w z :=
    (hV.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq z w
  have hh := posterior_brascamp_lieb_finite V f v hV hf
    (by rw [henergy]; exact hb.inner ℝ hv) r V₀ Kf (B₀*V₀)
    B₁ (B₀*V₁+B₁*V₀) (B₀*V₂+2*B₁*V₁+B₂*V₀)
    hr hV₀ hKf (by positivity) hB₁ (by positivity) (by positivity)
    hco hsym hsolve hv₀ hfb
    (by rw [henergy]; exact he₀) hF
    (by rw [henergy]; exact he₁) (by rw [henergy]; exact he₂)
  simpa only [henergy,v,inverseFamily] using hh

theorem posterior_brascamp_lieb_canonical_finite     (V f : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (posteriorDensityMeasure V)]
    (hV : ContDiff ℝ 4 V) (hf : ContDiff ℝ 3 f)
    (r A₁ A₂ B₀ B₁ B₂ Kf : ℝ)
    (hr : 0<r) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hKf : 0 ≤ Kf)
    (hcoercive : ∀ x z, r*‖z‖^2 ≤ directionalHessian V x z)
    (hfb : ∀ x, |f x| ≤ Kf)
    (ha₁ : ∀ x z, ‖fderiv ℝ (hessianOperator V) x z‖ ≤ A₁*‖z‖)
    (ha₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ (hessianOperator V)) x z z‖ ≤ A₂*‖z‖^2)
    (hb₀ : ∀ x, ‖gradient f x‖ ≤ B₀)
    (hb₁ : ∀ x z, ‖fderiv ℝ (gradient f) x z‖ ≤ B₁*‖z‖)
    (hb₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ (gradient f)) x z z‖ ≤ B₂*‖z‖^2) :
    variance f (posteriorDensityMeasure V) ≤
      ∫ x, inner ℝ (gradient f x) ((Ring.inverse (hessianOperator V x))
        (gradient f x)) ∂posteriorDensityMeasure V := by
  apply posterior_brascamp_lieb_operator_finite V f (hessianOperator V) (gradient f)
    (hV.of_le (by norm_num)) (hf.of_le (by norm_num))
    (contDiff_hessianOperator V hV) (contDiff_gradient_two f hf)
    (fun x z w => (inner_hessianOperator V x z w).symm)
    (fun x z => (inner_gradient_left (f := f) (x := x) (y := z)).symm)
    r A₁ A₂ B₀ B₁ B₂ Kf hr hA₁ hA₂ hB₀ hB₁ hB₂ hKf
    (fun x z => by
      rw [real_inner_comm (hessianOperator V x z) z,inner_hessianOperator]
      exact hcoercive x z)
    hfb ha₁ ha₂ hb₀ hb₁ hb₂

theorem posterior_brascamp_lieb_canonical_of_jet_bounds_finite     (V f : EuclideanSpace ℝ ι → ℝ)
    [MeasureTheory.IsProbabilityMeasure (posteriorDensityMeasure V)]
    (hV : ContDiff ℝ 4 V) (hf : ContDiff ℝ 3 f)
    (r A₁ A₂ B₀ B₁ B₂ Kf : ℝ) (hr : 0 < r)
    (hcoercive : ∀x z,r*‖z‖^2 ≤ directionalHessian V x z)
    (hfb : ∀x,|f x| ≤ Kf)
    (ha₁ : ∀x,‖iteratedFDeriv ℝ 3 V x‖ ≤ A₁)
    (ha₂ : ∀x,‖iteratedFDeriv ℝ 4 V x‖ ≤ A₂)
    (hb₀ : ∀x,‖iteratedFDeriv ℝ 1 f x‖ ≤ B₀)
    (hb₁ : ∀x,‖iteratedFDeriv ℝ 2 f x‖ ≤ B₁)
    (hb₂ : ∀x,‖iteratedFDeriv ℝ 3 f x‖ ≤ B₂) :
    ProbabilityTheory.variance f (posteriorDensityMeasure V) ≤
      ∫x,inner ℝ (gradient f x) ((Ring.inverse (hessianOperator V x)) (gradient f x))
        ∂posteriorDensityMeasure V := by
  apply posterior_brascamp_lieb_canonical_finite V f hV hf r A₁ A₂ B₀ B₁ B₂ Kf hr
    ((norm_nonneg _).trans (ha₁ 0)) ((norm_nonneg _).trans (ha₂ 0))
    ((norm_nonneg _).trans (hb₀ 0)) ((norm_nonneg _).trans (hb₁ 0))
    ((norm_nonneg _).trans (hb₂ 0)) ((abs_nonneg _).trans (hfb 0)) hcoercive hfb
  · exact hessian_first_directional_bound V hV A₁ ha₁
  · exact hessian_second_directional_bound V hV A₂ ha₂
  · exact gradient_norm_bound f B₀ hb₀
  · exact gradient_first_directional_bound f B₁ hb₁
  · exact gradient_second_directional_bound f B₂ hb₂

end QuantitativeFollowup
