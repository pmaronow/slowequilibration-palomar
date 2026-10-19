-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeSampledUpper
public import SlowEquilibration.GaussianDensity
public import SlowEquilibration.SphericalParisiBound

@[expose] public section

/-! # Actual annealed latitude endpoint and sampled upper through zero

Jensen's inequality controls the true bank latitude mean near zero. The
annealed endpoint and fixed original Dirac trial coincide at zero and vary
continuously, uniformly over the compact amplitude box.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open SphericalModel
open scoped Topology BigOperators RealInnerProductSpace ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem amplitudeLatitudePoint_exp_integrable (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (r : ℝ) (u : Vector n) :
    Integrable (fun D : BankDisorder n μ => Real.exp (β*amplitudeField μ x (latitudeFrameAt x) p₀ s D
      (latitudeMap x (latitudeFrameAt x) r u))) (bankLaw n μ) := by
  have hG := amplitudeField_hasGaussianLaw μ x (latitudeFrameAt x) p₀ s (latitudeMap x (latitudeFrameAt x) r u)
  exact (show HasLaw (fun D : BankDisorder n μ => amplitudeField μ x (latitudeFrameAt x) p₀ s D
    (latitudeMap x (latitudeFrameAt x) r u))
    (gaussianReal (∫ D,amplitudeField μ x (latitudeFrameAt x) p₀ s D
      (latitudeMap x (latitudeFrameAt x) r u) ∂bankLaw n μ)
      (variance (fun D => amplitudeField μ x (latitudeFrameAt x) p₀ s D
        (latitudeMap x (latitudeFrameAt x) r u)) (bankLaw n μ)).toNNReal)
    (bankLaw n μ) from ⟨hG.aemeasurable,hG.map_eq_gaussianReal⟩).integrable_comp
    (integrable_exp_mul_gaussianReal β)

theorem amplitudeLatitudePoint_exp_integral (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (r : ℝ) (u : Vector n) :
    (∫ D : BankDisorder n μ,Real.exp (β*amplitudeField μ x (latitudeFrameAt x) p₀ s D
      (latitudeMap x (latitudeFrameAt x) r u)) ∂bankLaw n μ)=
      Real.exp (β^2*‖amplitudeLatitudeBankFeature μ x (latitudeFrameAt x) p₀ s r u‖^2/2) := by
  let v := amplitudeLatitudeBankFeature μ x (latitudeFrameAt x) p₀ s r u
  have he (D : BankDisorder n μ) : β*amplitudeField μ x (latitudeFrameAt x) p₀ s D
      (latitudeMap x (latitudeFrameAt x) r u)=β*inner ℝ v (euclideanBank D) := by
    have hh := amplitudeBankLinear_apply μ β x (latitudeFrameAt x) p₀ s
      (latitudeMap x (latitudeFrameAt x) r u) (euclideanBank D)
    rw [unpackBank_euclideanBank] at hh
    simpa only [amplitudeBankLinear,smul_apply,smul_eq_mul,innerSL_apply_apply,v,
      amplitudeLatitudeBankFeature] using hh.symm
  simp_rw [he]
  have hm := (actual_bank_flattened_gaussian n μ).integral_comp
    (f := fun w : EuclideanBank n μ => Real.exp (β*inner ℝ v w)) (by fun_prop)
  dsimp only [Function.comp_apply] at hm
  rw [hm,GaussianDensity.integral_exp_inner_stdGaussian]

theorem amplitudeLatitudePoint_exp_integral_on_sphere (hn : 1≤n) (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) {r : ℝ} (hr : |r|≤1) (u : Vector n) (hu : ‖u‖^2=(n : ℝ)) :
    (∫ D : BankDisorder n μ,Real.exp (β*amplitudeField μ x (latitudeFrameAt x) p₀ s D
      (latitudeMap x (latitudeFrameAt x) r u)) ∂bankLaw n μ)=
      Real.exp (β^2*((n+1 : ℕ) : ℝ)*amplitudeLatitudeCovariance μ p₀ s r 1/2) := by
  rw [amplitudeLatitudePoint_exp_integral]
  have hg := amplitudeLatitudeBankFeature_inner hn μ x hx (latitudeFrameAt x)
    (latitudeFrameAt_orthogonal x hx) p₀ s hr u u
  rw [real_inner_self_eq_norm_sq,overlap_self hn u hu] at hg
  rw [hg]
  congr 1
  ring

theorem amplitudeLatitude_exp_prod_integrable (hn : 1≤n) (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) {r : ℝ} (hr : |r|≤1) :
    Integrable (fun z : BankDisorder n μ × Vector n => Real.exp
      (β*amplitudeField μ x (latitudeFrameAt x) p₀ s z.1 (latitudeMap x (latitudeFrameAt x) r z.2)))
      ((bankLaw n μ).prod (sphereLaw n)) := by
  have hcont : Continuous (fun z : BankDisorder n μ × Vector n => Real.exp
      (β*amplitudeField μ x (latitudeFrameAt x) p₀ s z.1 (latitudeMap x (latitudeFrameAt x) r z.2))) := by
    unfold amplitudeField bankComponent SphericalAging.FiniteModel.tensorLinear
      SphericalAging.FiniteModel.tensorMonomial latitudeMap overlap
    fun_prop
  apply (integrable_prod_iff' hcont.measurable.aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun u => amplitudeLatitudePoint_exp_integrable μ β x p₀ s r u),?_⟩
  apply (integrable_const (Real.exp (β^2*((n+1 : ℕ) : ℝ)*amplitudeLatitudeCovariance μ p₀ s r 1/2))).congr
  filter_upwards [sphereLaw_support hn] with u hu
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (amplitudeLatitudePoint_exp_integral_on_sphere hn μ β x hx p₀ s hr u hu).symm

theorem amplitudeLatitude_expected_partition (hn : 1≤n) (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) {r : ℝ} (hr : |r|≤1) :
    (∫ D : BankDisorder n μ,partitionAgainst (latitudeLaw x (latitudeFrameAt x) r) β
      (amplitudeField μ x (latitudeFrameAt x) p₀ s D) ∂bankLaw n μ)=
      Real.exp (β^2*((n+1 : ℕ) : ℝ)*amplitudeLatitudeCovariance μ p₀ s r 1/2) := by
  simp_rw [amplitudeLatitudePartition_eq_sphereIntegral]
  rw [integral_integral_swap (amplitudeLatitude_exp_prod_integrable hn μ β x hx p₀ s hr)]
  have he : (fun u : Vector n => ∫ D : BankDisorder n μ,Real.exp
      (β*amplitudeField μ x (latitudeFrameAt x) p₀ s D (latitudeMap x (latitudeFrameAt x) r u)) ∂bankLaw n μ)=ᵐ[sphereLaw n]
      fun _ => Real.exp (β^2*((n+1 : ℕ) : ℝ)*amplitudeLatitudeCovariance μ p₀ s r 1/2) := by
    filter_upwards [sphereLaw_support hn] with u hu
    exact amplitudeLatitudePoint_exp_integral_on_sphere hn μ β x hx p₀ s hr u hu
  rw [integral_congr_ae he]
  simp

theorem amplitudeLatitudeQuenchedPressure_le_annealed (hn : 1≤n) (μ : FiniteMixture)
    {β : ℝ} (hβ : 0<β) (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) {r : ℝ} (hr : |r|≤1) :
    amplitudeLatitudeQuenchedPressure n μ β x (latitudeFrameAt x) p₀ s r≤
      β^2*amplitudeLatitudeCovariance μ p₀ s r 1/2 := by
  have hi : Integrable (fun D : BankDisorder n μ => partitionAgainst
      (latitudeLaw x (latitudeFrameAt x) r) β (amplitudeField μ x (latitudeFrameAt x) p₀ s D)) (bankLaw n μ) := by
    simpa only [amplitudeLatitudePartition_eq_sphereIntegral] using
      (amplitudeLatitude_exp_prod_integrable hn μ β x hx p₀ s hr).integral_prod_left
  have hl := amplitudeLatitudeLogPartition_integrable hn μ hβ x hx p₀ s hs hr
  have hp (D : BankDisorder n μ) := partitionAgainst_pos
    (latitudeLaw x (latitudeFrameAt x) r)
    ((latitudeLaw_support hn x hx (latitudeFrameAt x) (latitudeFrameAt_orthogonal x hx) hr).mono fun _ hv => hv.1)
    β (amplitudeField_contDiff μ x (latitudeFrameAt x) p₀ s D).continuous
  have h := integral_log_le_log_integral (bankLaw n μ) hi hl (.of_forall hp)
  rw [amplitudeLatitude_expected_partition hn μ β x hx p₀ s hr,Real.log_exp] at h
  unfold amplitudeLatitudeQuenchedPressure
  apply (div_le_iff₀ (by positivity : 0<((n+1 : ℕ) : ℝ))).mpr
  nlinarith

theorem amplitudeLatitudeCovariance_zero_zero (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) : amplitudeLatitudeCovariance μ p₀ s 0 0=0 := by
  unfold amplitudeLatitudeCovariance
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.2.val=0
  · have hp := i.1.property
    simp only [hi,Nat.sub_zero]
    rw [zero_pow (by omega : 2*i.1.val.val≠0)]
    ring
  · rw [zero_pow hi]
    ring

theorem amplitudeDiracTrial_zero_eq_annealed (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    amplitudeDiracTrial μ β p₀ s 0=β^2*amplitudeLatitudeCovariance μ p₀ s 0 1/2 := by
  unfold amplitudeDiracTrial
  simp only [amplitudeDiracAtom,abs_zero,add_zero,zero_div,sub_zero,Real.log_one,
    amplitudeLatitudeCovariance_zero_zero,add_zero]

/-- The actual annealed endpoint is within ε of the original Dirac trial
near zero, uniformly over the full source amplitude box. -/
theorem exists_amplitudeLatitude_annealed_near_zero (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ δ≤1 ∧ ∀ (s : Fin 2 → ℝ),(∀ j,|s j|≤2) →
      ∀ r : ℝ,|r|≤δ → β^2*amplitudeLatitudeCovariance μ p₀ s r 1/2≤
        amplitudeDiracTrial μ β p₀ s r+ε := by
  let K : Set ((Fin 2 → ℝ) × ℝ) :=
    (Icc (fun _ : Fin 2 => (-2 : ℝ)) (fun _ => (2 : ℝ))).prod (Icc (-1 : ℝ) 1)
  let f : ((Fin 2 → ℝ) × ℝ) → ℝ := fun z =>
    β^2*amplitudeLatitudeCovariance μ p₀ z.1 z.2 1/2-amplitudeDiracTrial μ β p₀ z.1 z.2
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hf : Continuous f := by
    have hcov : Continuous (fun z : (Fin 2 → ℝ) × ℝ => amplitudeLatitudeCovariance μ p₀ z.1 z.2 1) := by
      simpa only [Function.comp_def,id_eq] using (amplitudeLatitudeCovariance_joint_continuous μ p₀).comp
        ((continuous_id : Continuous (fun z : (Fin 2 → ℝ) × ℝ => z)).prodMk
          (continuous_const : Continuous (fun _ : (Fin 2 → ℝ) × ℝ => (1 : ℝ))))
    exact ((hcov.const_mul (β^2)).div_const 2).sub (amplitudeDiracTrial_joint_continuous μ β p₀)
  obtain ⟨η,hη,hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hf.continuousOn) ε hε
  let δ : ℝ := min (η/2) 1
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  refine ⟨δ,hδ,min_le_right _ _,?_⟩
  intro s hs r hr
  have hs' : s∈Icc (fun _ : Fin 2 => (-2 : ℝ)) (fun _ => (2 : ℝ)) :=
    ⟨fun j => (abs_le.mp (hs j)).1,fun j => (abs_le.mp (hs j)).2⟩
  have hr1 : |r|≤1 := hr.trans (min_le_right _ _)
  have hsr : (s,r)∈K := ⟨hs',abs_le.mp hr1⟩
  have hs0 : (s,(0 : ℝ))∈K := ⟨hs',by norm_num⟩
  have hd : dist (s,r) (s,(0 : ℝ))<η := by
    simp only [Prod.dist_eq,dist_self,Real.dist_eq,sub_zero,max_eq_right (abs_nonneg r)]
    have hh := min_le_left (η/2) (1 : ℝ)
    change abs r ≤ min (η/2) 1 at hr
    linarith
  have hh := hmod (s,r) hsr (s,0) hs0 hd
  have h0 : f (s,0)=0 := by
    dsimp [f]
    rw [amplitudeDiracTrial_zero_eq_annealed]
    ring
  rw [h0,Real.dist_eq,sub_zero] at hh
  dsimp [f] at hh
  linarith [le_abs_self (β^2*amplitudeLatitudeCovariance μ p₀ s r 1/2-amplitudeDiracTrial μ β p₀ s r)]


/-- Genuine fixed-atom mean upper across zero on every compact signed
latitude interval strictly inside the poles. -/
theorem amplitudeLatitudeQuenchedPressure_eventually_all_latitudes_dirac_upper
    (μ : FiniteMixture) {β : ℝ} (hβ : 0<β) (p₀ : Degree μ.maxDegree)
    {ρ ε : ℝ} (hρ0 : 0<ρ) (hρ1 : ρ<1) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ (s : Fin 2 → ℝ),(∀ j,|s j|≤2) →
      ∀ r : ℝ,|r|≤ρ → ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
        amplitudeLatitudeQuenchedPressure n μ β x (latitudeFrameAt x) p₀ s r≤
          amplitudeDiracTrial μ β p₀ s r+ε := by
  obtain ⟨δ₀,hδ₀,hδ₀1,hzero⟩ := exists_amplitudeLatitude_annealed_near_zero μ β p₀ hε
  let δ : ℝ := min δ₀ (ρ/2)
  have hδ : 0<δ := lt_min hδ₀ (by positivity)
  have hδρ : δ≤ρ := (min_le_right _ _).trans (by linarith)
  have hmean := amplitudeLatitudeQuenchedPressure_eventually_uniform_dirac_upper μ β p₀ hδ hδρ hρ1 hε
  filter_upwards [hmean,eventually_ge_atTop 1] with n hmean hn
  intro s hs r hr x hx
  rcases le_total |r| δ with hsmall | hlarge
  · exact (amplitudeLatitudeQuenchedPressure_le_annealed hn μ hβ x hx p₀ s hs (hr.trans hρ1.le)).trans
      (hzero s hs r (hsmall.trans (min_le_left _ _)))
  · exact hmean s hs r ⟨hlarge,hr⟩ x hx (latitudeFrameAt x) (latitudeFrameAt_orthogonal x hx)

/-- The actual bank probability that any latitude in [-ρ,ρ] exceeds its
fixed original Dirac trial by ε decays exponentially in the true dimension. -/
theorem amplitudeLatitudeSampledPressure_eventually_all_latitudes_dirac_upper
    (μ : FiniteMixture) {β : ℝ} (hβ : 0<β) (p₀ : Degree μ.maxDegree)
    {ρ ε : ℝ} (hρ0 : 0<ρ) (hρ1 : ρ<1) (hε : 0<ε) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (s : Fin 2 → ℝ),(∀ j,|s j|≤2) →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
        bankLaw n μ {D | ∃ r : ℝ,|r|≤ρ ∧
          amplitudeDiracTrial μ β p₀ s r+ε<amplitudeLatitudeSampledPressure μ β x p₀ s r D}≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  obtain ⟨γ,hγ,hconc⟩ := amplitudeLatitude_uniform_concentration_eventually μ hβ
    (show 0<ε/2 by positivity) p₀
  have hmean := amplitudeLatitudeQuenchedPressure_eventually_all_latitudes_dirac_upper μ hβ p₀
    hρ0 hρ1 (show 0<ε/2 by positivity)
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hconc,hmean] with n hconc hmean
  intro s hs x hx
  have hconc' := hconc s hs (-ρ) ρ (by linarith) hρ1.le (by linarith) x hx
  apply (measure_mono ?_).trans hconc'
  rintro D ⟨r,hr,hD⟩
  refine ⟨r,abs_le.mp hr,?_⟩
  have hN : 0<((n+1 : ℕ) : ℝ) := by positivity
  have hM := hmean s hs r hr x hx
  change (∫ E,amplitudeLatitudeLogPartition μ β x p₀ s r E ∂bankLaw n μ)/((n+1 : ℕ) : ℝ)≤
    amplitudeDiracTrial μ β p₀ s r+ε/2 at hM
  have hM' := (div_le_iff₀ hN).mp hM
  have hD' := (lt_div_iff₀ hN).mp hD
  have hcenter : (ε/2)*((n+1 : ℕ) : ℝ)≤amplitudeLatitudeCenteredLogPartition μ β x p₀ s r D := by
    unfold amplitudeLatitudeCenteredLogPartition
    nlinarith
  exact hcenter.trans (le_abs_self _)

/-- Exact sampled source direction upper, including zero and both signs,
uniformly over source perturbations and all reference axes before dimension. -/
theorem amplitudeLatitudeSampledPressure_at_eventually_all_latitudes_upper
    (μ : FiniteMixture) {β : ℝ} (hβ : 0<β) (p₀ : Degree μ.maxDegree)
    {ρ ε : ℝ} (hρ0 : 0<ρ) (hρ1 : ρ<1) (hε : 0<ε) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (k : Fin 2) (τ : ℝ),τ∈Icc (-1/2 : ℝ) (1/2) →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
        bankLaw n μ {D | ∃ r : ℝ,|r|≤ρ ∧
          latitudePressureTrial μ β |r|+τ*(2+τ)*amplitudeDiracShiftCoefficient μ β p₀ k r+ε<
            amplitudeLatitudeSampledPressure μ β x p₀ (amplitudeAt k τ) r D}≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  obtain ⟨γ,hγ,hupper⟩ := amplitudeLatitudeSampledPressure_eventually_all_latitudes_dirac_upper μ hβ p₀ hρ0 hρ1 hε
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hupper] with n hupper
  intro k τ hτ x hx
  have hs : ∀ j,|amplitudeAt k τ j|≤2 := by
    intro j
    unfold amplitudeAt
    split_ifs
    · exact abs_le.mpr ⟨by linarith [hτ.1],by linarith [hτ.2]⟩
    · norm_num
  apply (measure_mono ?_).trans (hupper (amplitudeAt k τ) hs x hx)
  rintro D ⟨r,hr,hD⟩
  refine ⟨r,hr,?_⟩
  rw [amplitudeDiracTrial_at,amplitudeDiracTrial_one μ β p₀ (hr.trans_lt hρ1)]
  exact hD

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
