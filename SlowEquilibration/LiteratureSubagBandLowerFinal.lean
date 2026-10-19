-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerComparison
public import SlowEquilibration.SourceLiteratureParisiTemperatureEven
public import SlowEquilibration.SphericalLatitudeRegularity
public import SlowEquilibration.SourcePureCapMixedLatitudeOverlap

/-!
# Fixed-parameter reductions for Subag's lower band approximation

Dropping constraints between independent replica groups makes the literal
replicated partition submultiplicative. Together with positive band volume
and monotonicity in the tolerances, this proves that the exact lower
approximation is equivalent to its fixed-parameter, fixed-positive-count
version. Neither a large-count threshold nor an existential choice of
smaller tolerances remains in that equivalent formulation.

The exact-latitude geometry records the transverse overlap normalization.
Gaussian sign symmetry also removes any restriction to positive temperature.
The mixed-latitude domain inclusion is uniform in the replica count, and
sequential integration proves the product of one-replica slab lower bounds
used at the start of Section 2.1.

The all-temperature zero-overlap replicated-pressure limit and the analytic
partition comparison with a thick latitude are not asserted in this file.
In the source proof the former uses Lemma 22's pressure lower tail at every
exponential rate to control nets of orthogonal frames. Ordinary Gaussian
concentration alone does not supply that step.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagBandLowerFinal

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagTheorem5Proof SourceLiteratureParisiTemperatureEven
open LiteratureSubagTheorem10Proof
open SphericalGaussianJet WholeFieldRegression
open scoped Topology BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem band_measurable {N k : ℕ} (q δ ρ : ℝ) (m : Vector N) :
    MeasurableSet (ReplicatedBand k q δ ρ m) := by
  simp only [ReplicatedBand, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    exact (isClosed_le (by unfold overlap; fun_prop) continuous_const).measurableSet
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

private theorem product_density_integrable {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    Integrable (fun σ : Fin k → Vector N => ∏ i, gibbsDensity N β H (σ i))
      (Measure.pi (fun _ : Fin k => sphereLaw N)) :=
  Integrable.fintype_prod (fun _ => gibbsDensity_integrable hN β hH)

private theorem product_gibbs_eq_withDensity {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    Measure.pi (fun _ : Fin k => gibbsLaw N β H) =
      (Measure.pi (fun _ : Fin k => sphereLaw N)).withDensity
        (fun σ => ENNReal.ofReal (∏ i, gibbsDensity N β H (σ i))) := by
  let := gibbsLaw_probability hN β hH
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      (product_density_integrable (k := k) hN β hH).restrict
      (.of_forall (fun σ => Finset.prod_nonneg (fun i _ =>
        (gibbsDensity_pos hN β hH (σ i)).le))), Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
      (gibbsDensity_pos hN β hH x).le))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gibbsLaw, withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal (gibbsDensity_integrable hN β hH).restrict
      (.of_forall (fun x => (gibbsDensity_pos hN β hH x).le))]

private theorem product_gibbs_real_eq_integral {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H)
    {B : Set (Fin k → Vector N)} (hB : MeasurableSet B) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β H)).real B =
      ∫ σ in B, ∏ i, gibbsDensity N β H (σ i)
        ∂Measure.pi (fun _ : Fin k => sphereLaw N) := by
  rw [product_gibbs_eq_withDensity hN β hH, Measure.real,
    withDensity_apply _ hB,
    ← ofReal_integral_eq_lintegral_ofReal
      (product_density_integrable (k := k) hN β hH).restrict
      (.of_forall (fun σ => Finset.prod_nonneg (fun i _ =>
        (gibbsDensity_pos hN β hH (σ i)).le))),
    ENNReal.toReal_ofReal (integral_nonneg (fun σ =>
      Finset.prod_nonneg (fun i _ => (gibbsDensity_pos hN β hH (σ i)).le)))]

private theorem product_density_formula {N k : ℕ} (β : ℝ)
    (H : Vector N → ℝ) (m : Vector N) (σ : Fin k → Vector N) :
    (∏ i, gibbsDensity N β H (σ i)) =
      (Real.exp ((k : ℝ) * β * H m) / partition N β H ^ k) *
        Real.exp (β * ∑ i : Fin k, (H (σ i) - H m)) := by
  simp only [gibbsDensity, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

private theorem product_gibbs_band_mass {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β (field (mixtureCoefficients μ) J))).real
        (ReplicatedBand k q δ ρ m) =
      (Real.exp ((k : ℝ) * β * field (mixtureCoefficients μ) J m) /
        mixturePartition μ β J ^ k) * replicatedBandPartition k μ β q δ ρ J m := by
  rw [product_gibbs_real_eq_integral hN β (field_contDiff _ J).continuous
    (band_measurable q δ ρ m)]
  simp_rw [product_density_formula β (field (mixtureCoefficients μ) J) m]
  rw [integral_const_mul]
  rfl


private theorem finite_logPartition_bound {V H : Type*} [MeasurableSpace V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H] (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) :
    |GaussianSpinInterpolation.logPartition ν L w| ≤
      |Real.log (ν.real univ)| + K * ‖w‖ := by
  have hi := GaussianSpinInterpolation.weight_integrable ν (fun _ => 1) L
    measurable_const hL
    (hb.mono (fun _ hv => ⟨by norm_num, hv⟩) : ∀ᵐ v ∂ν, |(1 : ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K) w
  have hmass := measureReal_univ_pos (μ := ν)
  have hz := GaussianSpinInterpolation.moment_one_pos ν L hL hb w
  have hlo : ν.real univ * Real.exp (-K * ‖w‖) ≤
      GaussianSpinInterpolation.moment ν (fun _ => 1) L w := by
    have h := integral_mono_ae (integrable_const (Real.exp (-K * ‖w‖))) hi
      (hb.mono (fun v hv => by
        simp only [GaussianSpinInterpolation.weight, one_mul]
        apply Real.exp_le_exp.mpr
        have hh := (L v).le_opNorm w |>.trans
          (mul_le_mul_of_nonneg_right hv (norm_nonneg w))
        rw [Real.norm_eq_abs] at hh
        linarith [neg_le_abs (L v w)]))
    simpa only [integral_const, smul_eq_mul, GaussianSpinInterpolation.moment] using h
  have hhi : GaussianSpinInterpolation.moment ν (fun _ => 1) L w ≤
      ν.real univ * Real.exp (K * ‖w‖) := by
    have h := integral_mono_ae hi (integrable_const (Real.exp (K * ‖w‖)))
      (hb.mono (fun v hv => by
        simp only [GaussianSpinInterpolation.weight, one_mul]
        apply Real.exp_le_exp.mpr
        have hh := (L v).le_opNorm w |>.trans
          (mul_le_mul_of_nonneg_right hv (norm_nonneg w))
        exact (le_abs_self _).trans hh))
    simpa only [integral_const, smul_eq_mul, GaussianSpinInterpolation.moment] using h
  have hl := Real.log_le_log (mul_pos hmass (Real.exp_pos _)) hlo
  have hu := Real.log_le_log hz hhi
  rw [Real.log_mul hmass.ne' (Real.exp_ne_zero _), Real.log_exp] at hl hu
  change Real.log (ν.real univ) + -K * ‖w‖ ≤
    GaussianSpinInterpolation.logPartition ν L w at hl
  change GaussianSpinInterpolation.logPartition ν L w ≤
    Real.log (ν.real univ) + K * ‖w‖ at hu
  exact abs_le.mpr ⟨by linarith [neg_le_abs (Real.log (ν.real univ))],
    by linarith [le_abs_self (Real.log (ν.real univ))]⟩

private theorem finite_logPartition_gaussian_integrable {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    Integrable (GaussianSpinInterpolation.logPartition ν L)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hc := (GaussianSpinInterpolation.logPartition_contDiff ν L hL hK hb).continuous
  apply ((integrable_const |Real.log (ν.real univ)|).add
    (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul K)).mono'
    hc.aestronglyMeasurable
  exact .of_forall fun w => by
    rw [Real.norm_eq_abs]
    exact finite_logPartition_bound ν L hL hb w

private theorem replicatedBand_integrand_integrable {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    Integrable (fun σ : Fin k → Vector N =>
      Real.exp (β * ∑ i : Fin k,
        (field (mixtureCoefficients μ) J (σ i) -
          field (mixtureCoefficients μ) J m)))
      (Measure.pi (fun _ : Fin k => sphereLaw N)) := by
  have hi : Integrable (fun x : Vector N =>
      Real.exp (β * (field (mixtureCoefficients μ) J x -
        field (mixtureCoefficients μ) J m))) (sphereLaw N) :=
    partitionAgainst_integrable (sphereLaw N) (sphereLaw_support hN) β
      ((field_contDiff _ J).continuous.sub continuous_const)
  have hp := Integrable.fintype_prod (fun _ : Fin k => hi)
  convert hp using 1
  ext σ
  rw [Finset.mul_sum, Real.exp_sum]

/-- Positive surface volume makes the replicated partition strictly positive
for every disorder realization. -/
private theorem replicatedBandPartition_pos {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ ρ m)) :
    0 < replicatedBandPartition k μ β q δ ρ J m := by
  let : NeZero ((Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ ρ m)) := ⟨hvol.ne'⟩
  exact integral_exp_pos
    (replicatedBand_integrand_integrable hN μ β J m).restrict

/-- The physical replicated-band pressure is integrable under the literal
disorder law whenever its deterministic surface volume is positive. -/
private theorem replicatedBandPressure_integrable {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (m : Vector N)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ ρ m)) :
    Integrable (fun J : Disorder N μ.maxDegree =>
      replicatedBandPressure k μ β q δ ρ J m) (disorderLaw N μ.maxDegree) := by
  let ν := (Measure.pi (fun _ : Fin k => sphereLaw N)).restrict
    (ReplicatedBand k q δ ρ m)
  let : NeZero ((Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ ρ m)) := ⟨hvol.ne'⟩
  have : NeZero ν := inferInstance
  let L : (Fin k → Vector N) → EuclideanDisorder N μ.maxDegree →L[ℝ] ℝ :=
    fun σ => β • ∑ i : Fin k,
      (sphereLinear (mixtureCoefficients μ) (σ i) - sphereLinear (mixtureCoefficients μ) m)
  let K : ℝ := |β| * (k : ℝ) *
    (Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1) +
      ‖sphereLinear (mixtureCoefficients μ) m‖)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : Measurable L := by
    have hs : Measurable (fun σ : Fin k → Vector N => ∑ i : Fin k,
        (sphereLinear (mixtureCoefficients μ) (σ i) -
          sphereLinear (mixtureCoefficients μ) m)) := by
      apply Finset.measurable_sum
      intro i _
      exact ((sphereLinear_measurable _).comp (measurable_pi_apply i)).sub measurable_const
    exact (measurable_const : Measurable (fun _ : Fin k → Vector N => β)).smul hs
  have ha : ∀ᵐ σ ∂Measure.pi (fun _ : Fin k => sphereLaw N), ∀ i : Fin k,
      ‖sphereLinear (mixtureCoefficients μ) (σ i)‖ ≤
        Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1) :=
    eventually_all.mpr (fun i =>
      (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin k => sphereLaw N) (i := i)).eventually
        (sphereLinear_bound hN _ (mixtureCoefficients_nonnegative μ)))
  have hb : ∀ᵐ σ ∂ν, ‖L σ‖ ≤ K := by
    filter_upwards [ha.filter_mono ae_restrict_le] with σ hσ
    dsimp [L, K]
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
    calc
      _ ≤ ∑ i : Fin k,
          ‖sphereLinear (mixtureCoefficients μ) (σ i) -
            sphereLinear (mixtureCoefficients μ) m‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin k,
          (Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1) +
            ‖sphereLinear (mixtureCoefficients μ) m‖) := by
        apply Finset.sum_le_sum
        intro i _
        exact (norm_sub_le _ _).trans (add_le_add (hσ i) (le_refl _))
      _ = _ := by simp; ring
  have hi := finite_logPartition_gaussian_integrable ν L hL hK hb
  have hic := (euclideanDisorder_hasLaw N μ.maxDegree).integrable_comp hi
  have he (J : Disorder N μ.maxDegree) :
      GaussianSpinInterpolation.logPartition ν L (euclideanDisorder J) =
        Real.log (replicatedBandPartition k μ β q δ ρ J m) := by
    unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
    congr 1
    apply integral_congr_ae
    exact .of_forall fun σ => by
      simp only [GaussianSpinInterpolation.weight, one_mul, L,
        _root_.smul_apply, _root_.sum_apply,
        _root_.sub_apply, smul_eq_mul, sphereLinear_apply,
        unpack_euclideanDisorder]
  have hilog : Integrable (fun J : Disorder N μ.maxDegree =>
      Real.log (replicatedBandPartition k μ β q δ ρ J m))
      (disorderLaw N μ.maxDegree) := by
    simpa only [Function.comp_def, he] using hic
  exact hilog.div_const _



private theorem bandPressure_mono {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ₁ δ₂ ρ₁ ρ₂ : ℝ) (m : Vector N)
    (hδ : δ₁ ≤ δ₂) (hρ : ρ₁ ≤ ρ₂)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ₁ ρ₁ m)) :
    expectedReplicatedBandPressure k μ β q δ₁ ρ₁ m ≤
      expectedReplicatedBandPressure k μ β q δ₂ ρ₂ m := by
  have hsub : ReplicatedBand k q δ₁ ρ₁ m ⊆ ReplicatedBand k q δ₂ ρ₂ m := by
    intro σ hσ
    refine ⟨fun i => (hσ.1 i).trans ?_, fun i j hij => (hσ.2 i j hij).trans_le hρ⟩
    exact mul_le_mul_of_nonneg_right hδ (Real.sqrt_nonneg q)
  have hvol₂ : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ₂ ρ₂ m) := hvol.trans_le (measure_mono hsub)
  unfold expectedReplicatedBandPressure
  apply integral_mono (replicatedBandPressure_integrable hN μ β q δ₁ ρ₁ m hvol)
    (replicatedBandPressure_integrable hN μ β q δ₂ ρ₂ m hvol₂)
  intro J
  have hpart : replicatedBandPartition k μ β q δ₁ ρ₁ J m ≤
      replicatedBandPartition k μ β q δ₂ ρ₂ J m := by
    unfold replicatedBandPartition
    exact setIntegral_mono_set (replicatedBand_integrand_integrable hN μ β J m).restrict
      (.of_forall fun _ => (Real.exp_pos _).le) (.of_forall fun _ h => hsub h)
  unfold replicatedBandPressure
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (replicatedBandPartition_pos hN μ β q δ₁ ρ₁ J m hvol) hpart)
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Removing the constraints between two groups bounds their complete-band
mass by the product of their separate-band masses. -/
private theorem band_mass_add_le_mul {N : ℕ} (ν : Measure (Vector N))
    [IsProbabilityMeasure ν] (n k : ℕ) (q δ ρ : ℝ) (m : Vector N) :
    (Measure.pi (fun _ : Fin (n + k) => ν)).real (ReplicatedBand (n + k) q δ ρ m) ≤
      (Measure.pi (fun _ : Fin n => ν)).real (ReplicatedBand n q δ ρ m) *
        (Measure.pi (fun _ : Fin k => ν)).real (ReplicatedBand k q δ ρ m) := by
  let e₁ := MeasurableEquiv.piCongrLeft
    (fun _ : Fin n ⊕ Fin k => Vector N) finSumFinEquiv.symm
  let e₂ := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => Vector N)
  let e := e₁.trans e₂
  have h₁ := measurePreserving_piCongrLeft
    (fun _ : Fin n ⊕ Fin k => ν) finSumFinEquiv.symm
  have h₂ := measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => ν)
  have h : MeasurePreserving e (Measure.pi (fun _ : Fin (n + k) => ν))
      ((Measure.pi (fun _ : Fin n => ν)).prod (Measure.pi (fun _ : Fin k => ν))) :=
    h₂.comp h₁
  have hm := h.hasLaw.measureReal_eq
    (p := fun x => x ∈ (ReplicatedBand n q δ ρ m) ×ˢ (ReplicatedBand k q δ ρ m))
    (by simpa only [Set.ofPred_mem_eq] using
      ((band_measurable (k := n) q δ ρ m).prod (band_measurable (k := k) q δ ρ m)))
  calc
    _ ≤ (Measure.pi (fun _ : Fin (n + k) => ν)).real
        {σ | e σ ∈ (ReplicatedBand n q δ ρ m) ×ˢ (ReplicatedBand k q δ ρ m)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro σ hσ
      constructor
      · constructor
        · intro i
          simpa [e, e₁, e₂, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
            MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi] using
            hσ.1 (Fin.castAdd k i)
        · intro i j hij
          have hd : Fin.castAdd k i ≠ Fin.castAdd k j :=
            fun he => hij (Fin.castAdd_inj.mp he)
          simpa [e, e₁, e₂, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
            MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi] using
            hσ.2 (Fin.castAdd k i) (Fin.castAdd k j) hd
      · constructor
        · intro i
          simpa [e, e₁, e₂, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
            MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi] using
            hσ.1 (Fin.natAdd n i)
        · intro i j hij
          have hd : Fin.natAdd n i ≠ Fin.natAdd n j :=
            fun he => hij (Fin.ext (Nat.add_left_cancel (congrArg Fin.val he)))
          simpa [e, e₁, e₂, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
            MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi] using
            hσ.2 (Fin.natAdd n i) (Fin.natAdd n j) hd
    _ = _ := by
      calc
        _ = ((Measure.pi (fun _ : Fin n => ν)).prod
            (Measure.pi (fun _ : Fin k => ν))).real
              ((ReplicatedBand n q δ ρ m) ×ˢ (ReplicatedBand k q δ ρ m)) := by
          simpa only [Set.ofPred_mem_eq] using hm
        _ = _ := by simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]

private theorem band_mass_mul_le_pow {N : ℕ} (ν : Measure (Vector N))
    [IsProbabilityMeasure ν] (n r : ℕ) (q δ ρ : ℝ) (m : Vector N) :
    (Measure.pi (fun _ : Fin (n * r) => ν)).real (ReplicatedBand (n * r) q δ ρ m) ≤
      (Measure.pi (fun _ : Fin n => ν)).real (ReplicatedBand n q δ ρ m) ^ r := by
  induction r with
  | zero =>
      simp only [Nat.mul_zero, pow_zero]
      exact measureReal_le_one
  | succ r ih =>
      rw [Nat.mul_succ, pow_succ]
      exact (band_mass_add_le_mul ν (n * r) n q δ ρ m).trans
        (mul_le_mul_of_nonneg_right ih measureReal_nonneg)

/-- Subag Section 2.1: deleting cross-group constraints is valid for the
literal centered partition, at every temperature and in every positive dimension. -/
theorem replicatedBandPartition_mul_le_pow {N : ℕ} (hN : 1 ≤ N) (n r : ℕ)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    replicatedBandPartition (n * r) μ β q δ ρ J m ≤
      replicatedBandPartition n μ β q δ ρ J m ^ r := by
  let ν := gibbsLaw N β (field (mixtureCoefficients μ) J)
  let := gibbsLaw_probability hN β (field_contDiff (mixtureCoefficients μ) J).continuous
  have h := band_mass_mul_le_pow ν n r q δ ρ m
  dsimp only [ν] at h
  rw [product_gibbs_band_mass hN, product_gibbs_band_mass hN] at h
  have hZ := mixturePartition_pos hN μ β J
  have hc :
      (Real.exp ((n : ℝ) * β * field (mixtureCoefficients μ) J m) /
        mixturePartition μ β J ^ n) ^ r =
      Real.exp (((n * r : ℕ) : ℝ) * β * field (mixtureCoefficients μ) J m) /
        mixturePartition μ β J ^ (n * r) := by
    rw [div_pow, ← Real.exp_nat_mul, ← pow_mul]
    congr 2
    push_cast
    ring
  rw [mul_pow, hc] at h
  exact (mul_le_mul_iff_right₀ (div_pos (Real.exp_pos _) (pow_pos hZ _))).mp h

/-- Normalizing by the count reverses this comparison: a fixed positive
count has at least the pressure of any positive multiple. -/
theorem expectedReplicatedBandPressure_mul_le {N n r : ℕ}
    (hN : n * r + 1 ≤ N) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (μ : FiniteMixture) (β : ℝ) {q δ ρ : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hδ : 0 < δ) (hρ : 0 < ρ)
    (m : Vector N) (hm : ‖m‖ ^ 2 = (N : ℝ) * q) :
    expectedReplicatedBandPressure (n * r) μ β q δ ρ m ≤
      expectedReplicatedBandPressure n μ β q δ ρ m := by
  have hnN : n + 1 ≤ N := by nlinarith
  have hN0 : 1 ≤ N := by omega
  have hnr : 1 ≤ n * r := by nlinarith
  have hv := SourcePureSection9SmallClosures.replicatedBand_volume_positive
    hN hnr hq hδ hρ m hm
  have hvn := SourcePureSection9SmallClosures.replicatedBand_volume_positive
    hnN hn hq hδ hρ m hm
  unfold expectedReplicatedBandPressure
  apply integral_mono (replicatedBandPressure_integrable hN0 μ β q δ ρ m hv)
    (replicatedBandPressure_integrable hN0 μ β q δ ρ m hvn)
  intro J
  have hlog := Real.log_le_log (replicatedBandPartition_pos hN0 μ β q δ ρ J m hv)
    (replicatedBandPartition_mul_le_pow hN0 n r μ β q δ ρ J m)
  rw [Real.log_pow] at hlog
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hrpos : 0 < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  unfold replicatedBandPressure
  apply (div_le_div_iff₀ (mul_pos hNpos (Nat.cast_pos.mpr (by omega)))
    (mul_pos hNpos hnpos)).mpr
  calc
    _ ≤ ((r : ℝ) * Real.log (replicatedBandPartition n μ β q δ ρ J m)) *
        ((N : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hlog (mul_pos hNpos hnpos).le
    _ = _ := by push_cast; ring

/-- An exact equivalent formulation of the requested lower estimate.
Every positive tolerance and every fixed positive replica count suffice;
all dimension thresholds may still depend on that count. -/
theorem expectedBandLowerApproximation_iff_fixedParameters
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) :
    ExpectedBandLowerApproximation D ↔
      ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → ∀ ε : ℝ, 0 < ε →
        ∀ δ ρ : ℝ, 0 < δ → 0 < ρ → ∀ k : ℕ, 1 ≤ k →
          ∀ᶠ N : ℕ in atTop,
            ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
              Real.log (1 - q) / 2 + D.residual q - ε ≤
                expectedReplicatedBandPressure k μ β q δ ρ m := by
  constructor
  · intro h q hq ε hε δ ρ hδ hρ k hk
    obtain ⟨δ', hδ', hδle, ρ', hρ', hρle, K, hl⟩ := h q hq ε hε δ ρ hδ hρ
    let r := K + 1
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hKr : K ≤ k * r := by dsimp [r]; nlinarith
    filter_upwards [hl (k * r) hKr, eventually_ge_atTop (k * r + 1)] with N hlow hN
    intro m hm
    have hv := SourcePureSection9SmallClosures.replicatedBand_volume_positive
      hN (show 1 ≤ k * r by nlinarith) hq hδ' hρ' m hm
    exact (hlow m hm).trans
      ((bandPressure_mono (by omega) μ β q δ' δ ρ' ρ m hδle hρle hv).trans
        (expectedReplicatedBandPressure_mul_le hN hk hr μ β hq hδ hρ m hm))
  · intro h q hq ε hε δ₀ ρ₀ hδ₀ hρ₀
    exact ⟨δ₀, hδ₀, le_rfl, ρ₀, hρ₀, le_rfl, 1,
      fun k hk => h q hq ε hε δ₀ ρ₀ hδ₀ hρ₀ k hk⟩

private theorem replicatedBandPartition_neg_beta {N : ℕ} (k : ℕ) (μ : FiniteMixture)
    (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    replicatedBandPartition k μ (-β) q δ ρ J m =
      replicatedBandPartition k μ β q δ ρ (-J) m := by
  unfold replicatedBandPartition
  congr 1
  funext σ
  congr 1
  simp only [field_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

/-- The actual expected replicated pressure is even in temperature.
This includes the zero-volume case and requires no limiting formula. -/
theorem expectedReplicatedBandPressure_neg {N : ℕ} (k : ℕ) (μ : FiniteMixture)
    (β q δ ρ : ℝ) (m : Vector N) :
    expectedReplicatedBandPressure k μ (-β) q δ ρ m =
      expectedReplicatedBandPressure k μ β q δ ρ m := by
  unfold expectedReplicatedBandPressure replicatedBandPressure
  simp_rw [replicatedBandPartition_neg_beta]
  exact (disorderLaw_neg_measurePreserving N μ.maxDegree).integral_comp'
    (fun J => Real.log (replicatedBandPartition k μ β q δ ρ J m) /
      ((N : ℝ) * (k : ℝ)))

/-- The lower problem at negative temperature is exactly the same problem
at positive temperature, for any actual thermodynamic data. -/
theorem expectedBandLowerApproximation_neg_iff {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (E : ThermodynamicData μ (-β)) :
    ExpectedBandLowerApproximation D ↔ ExpectedBandLowerApproximation E := by
  have hres (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) : D.residual q = E.residual q :=
    tendsto_nhds_unique (D.residual_limit q hq)
      (show Tendsto (fun N : ℕ => quenchedPressure N (physicalResidualMixture μ q hq) β)
        atTop (𝓝 (E.residual q)) from by
          simpa only [quenchedPressure_neg] using E.residual_limit q hq)
  constructor
  · intro h q hq
    simpa only [hres q hq, expectedReplicatedBandPressure_neg] using h q hq
  · intro h q hq
    simpa only [← hres q hq, expectedReplicatedBandPressure_neg] using h q hq

/-- On the central latitude, the replica overlap tolerance is exactly
`ρ / (1 - q)` in transverse coordinates, with no asymptotic error. -/
theorem replicatedBand_latitude_iff {n k : ℕ} (hn : 1 ≤ n)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) (he : ∀ y, inner ℝ (e y) u = 0)
    {q δ ρ : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hδ : 0 ≤ δ)
    (y : Fin k → Vector n) :
    (fun i => latitudeMap u e (Real.sqrt q) (y i)) ∈
        ReplicatedBand k q δ ρ (Real.sqrt q • u) ↔
      ∀ i j : Fin k, i ≠ j → |overlap (y i) (y j)| < ρ / (1 - q) := by
  have hs : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.1.le
  have ha : |Real.sqrt q| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg q)]
    exact (Real.sqrt_le_one).mpr hq.2.le
  have hcenter (i : Fin k) :
      overlap (latitudeMap u e (Real.sqrt q) (y i)) (Real.sqrt q • u) = q := by
    rw [overlap, real_inner_smul_right, mul_div_assoc,
      show inner ℝ (latitudeMap u e (Real.sqrt q) (y i)) u /
        ((n + 1 : ℕ) : ℝ) = Real.sqrt q from overlap_latitude_center u hu e he _ _]
    nlinarith [hs]
  have hpair (i j : Fin k) :
      |overlap (latitudeMap u e (Real.sqrt q) (y i))
        (latitudeMap u e (Real.sqrt q) (y j)) - q| =
          (1 - q) * |overlap (y i) (y j)| := by
    rw [overlap_latitude_pair hn u hu e he ha, hs,
      add_sub_cancel_left, abs_mul, abs_of_pos (sub_pos.mpr hq.2)]
  constructor
  · intro h i j hij
    exact (lt_div_iff₀ (sub_pos.mpr hq.2)).mpr
      (by simpa only [mul_comm] using (hpair i j) ▸ h.2 i j hij)
  · intro h
    constructor
    · intro i
      rw [hcenter i, sub_self, abs_zero]
      positivity
    · intro i j hij
      rw [hpair]
      simpa only [mul_comm] using (lt_div_iff₀ (sub_pos.mpr hq.2)).mp (h i j hij)

/-- The domain inclusion for Subag's latitude thickening. A transverse
block and independent latitude windows give a genuine replicated band;
the tolerance loss is independent of the number of replicas. -/
theorem variableLatitude_mem_replicatedBand {n k : ℕ} (hn : 1 ≤ n)
    {q δ ρ η θ : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hηδ : η ≤ δ) (hwidth : 2 * η + θ ≤ ρ)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) (he : ∀ x, inner ℝ (e x) u = 0)
    (r : Fin k → ℝ) (hr : ∀ i, |r i| ≤ 1)
    (hnear : ∀ i, |r i - Real.sqrt q| ≤ η) (y : Fin k → Vector n)
    (hpair : ∀ i j, i ≠ j → |overlap (y i) (y j)| < θ) :
    (fun i => latitudeMap u e (r i) (y i)) ∈
      ReplicatedBand k q δ ρ (Real.sqrt q • u) := by
  have hs0 := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq.2.le
  have hs : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.1.le
  constructor
  · intro i
    have hc : overlap (latitudeMap u e (r i) (y i)) (Real.sqrt q • u) =
        Real.sqrt q * r i := by
      calc
        _ = Real.sqrt q * overlap (latitudeMap u e (r i) (y i)) u := by
          unfold overlap
          rw [real_inner_smul_right]
          ring
        _ = _ := by rw [overlap_latitude_center u hu e he]
    rw [hc, show Real.sqrt q * r i - q =
      Real.sqrt q * (r i - Real.sqrt q) by nlinarith [hs],
      abs_mul, abs_of_nonneg hs0]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left ((hnear i).trans hηδ) hs0
  · intro i j hij
    have hprod : |r i * r j - q| ≤ 2 * η := by
      calc
        _ = |r i * (r j - Real.sqrt q) + Real.sqrt q * (r i - Real.sqrt q)| := by
          congr 1
          nlinarith [hs]
        _ ≤ |r i| * |r j - Real.sqrt q| + Real.sqrt q * |r i - Real.sqrt q| := by
          simpa only [abs_mul, abs_of_nonneg hs0] using
            abs_add_le (r i * (r j - Real.sqrt q)) (Real.sqrt q * (r i - Real.sqrt q))
        _ ≤ 1 * η + 1 * η := add_le_add
          (mul_le_mul (hr i) (hnear j) (abs_nonneg _) (by norm_num))
          (mul_le_mul hs1 (hnear i) (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    let c := Real.sqrt (1 - (r i) ^ 2) * Real.sqrt (1 - (r j) ^ 2)
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hc1 : c ≤ 1 := by
      have hi : Real.sqrt (1 - (r i) ^ 2) ≤ 1 :=
        Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (r i)])
      have hj : Real.sqrt (1 - (r j) ^ 2) ≤ 1 :=
        Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (r j)])
      exact (mul_le_mul_of_nonneg_right hi (Real.sqrt_nonneg _)).trans (by simpa using hj)
    rw [SourcePureCapMixedLatitudeOverlap.overlap_latitude_pair_mixed
      hn u hu e he (hr i) (hr j)]
    change |r i * r j + c * overlap (y i) (y j) - q| < ρ
    have hb : |r i * r j + c * overlap (y i) (y j) - q| ≤
        2 * η + |overlap (y i) (y j)| := by
      calc
        _ = |(r i * r j - q) + c * overlap (y i) (y j)| := by congr 1; ring
        _ ≤ |r i * r j - q| + |c * overlap (y i) (y j)| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul, abs_of_nonneg hc0]
          exact add_le_add hprod
            (by simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right hc1 (abs_nonneg (overlap (y i) (y j)))))
    linarith [hpair i j hij]

private theorem overlapBlock_measurable {N k : ℕ} (q ρ : ℝ) :
    MeasurableSet (overlapBlock (N := N) (k := k) q ρ) := by
  simp only [overlapBlock, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => ?_
  exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

private theorem overlapBlock_cons_iff {N k : ℕ} (ρ : ℝ)
    (y : Vector N) (σ : Fin k → Vector N) :
    Fin.cons y σ ∈ overlapBlock 0 ρ ↔
      σ ∈ overlapBlock 0 ρ ∧ ∀ i, |overlap y (σ i)| < ρ := by
  constructor
  · intro h
    constructor
    · intro i j hij
      simpa only [Fin.cons_succ] using
        h i.succ j.succ (by simpa only [ne_eq, Fin.succ_inj] using hij)
    · intro i
      simpa only [Fin.cons_zero, Fin.cons_succ, sub_zero] using
        h 0 i.succ (Fin.succ_ne_zero i).symm
  · rintro ⟨hσ, hy⟩ i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => simpa only [Fin.cons_zero, Fin.cons_succ, sub_zero] using hy j
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simpa only [Fin.cons_succ, Fin.cons_zero, sub_zero, overlap,
          real_inner_comm] using hy i
      | succ j =>
        have hij' : i ≠ j := fun he => hij (congrArg Fin.succ he)
        simpa only [Fin.cons_succ] using hσ i j hij'

private theorem overlapBlock_pi_succ_lower {N k : ℕ} (ν : Measure (Vector N))
    [IsProbabilityMeasure ν] (ρ : ℝ) (a : ℝ≥0∞)
    (hslab : ∀ᵐ (σ : Fin k → Vector N) ∂Measure.pi (fun _ : Fin k => ν),
      σ ∈ overlapBlock 0 ρ → a ≤ ν {y | ∀ i, |overlap y (σ i)| < ρ}) :
    a * (Measure.pi (fun _ : Fin k => ν)) (overlapBlock 0 ρ) ≤
      (Measure.pi (fun _ : Fin (k + 1) => ν)) (overlapBlock 0 ρ) := by
  let P := Measure.pi (fun _ : Fin k => ν)
  let f : Vector N × (Fin k → Vector N) → Fin (k + 1) → Vector N :=
    fun p => Fin.cons p.1 p.2
  have hf : Measurable f := GaussianReplicaKernel.appendHead_measurable k
  have hmap : (ν.prod P).map f = Measure.pi (fun _ : Fin (k + 1) => ν) := by
    have h := (measurePreserving_piFinSuccAbove
      (fun _ : Fin (k + 1) => ν) 0).symm.map_eq
    simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_zero, cast_eq, P, f] using h
  let A := f ⁻¹' overlapBlock (N := N) (k := k + 1) 0 ρ
  have hA : MeasurableSet A := hf (overlapBlock_measurable 0 ρ)
  have hm : (ν.prod P) A =
      (Measure.pi (fun _ : Fin (k + 1) => ν)) (overlapBlock 0 ρ) := by
    calc
      _ = ((ν.prod P).map f) (overlapBlock 0 ρ) :=
        (Measure.map_apply hf (overlapBlock_measurable 0 ρ)).symm
      _ = _ := by rw [hmap]
  calc
    _ = ∫⁻ σ, (overlapBlock (N := N) (k := k) 0 ρ).indicator
        (fun _ => a) σ ∂P :=
      (lintegral_indicator_const (μ := P) (overlapBlock_measurable 0 ρ) a).symm
    _ ≤ ∫⁻ σ, ν ((fun y => (y, σ)) ⁻¹' A) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hslab] with σ hσ
      by_cases hb : σ ∈ overlapBlock 0 ρ
      · rw [Set.indicator_of_mem hb]
        have hs : ((fun y => (y, σ)) ⁻¹' A) =
            {y | ∀ i, |overlap y (σ i)| < ρ} := by
          ext y
          simpa only [A, f, Set.mem_preimage, Set.mem_ofPred_eq, hb, true_and] using
            (overlapBlock_cons_iff ρ y σ)
        rw [hs]
        exact hσ hb
      · rw [Set.indicator_of_notMem hb]
        exact bot_le
    _ = (ν.prod P) A := (Measure.prod_apply_symm hA).symm
    _ = _ := hm

/-- Subag Section 2.1's sequential replica integration, for any probability
measure, including the actual Gibbs law at any temperature. Lower bounds
for each one-replica slab multiply to a lower bound for the whole block. -/
theorem overlapBlock_pi_lower_of_slab {N k : ℕ} (ν : Measure (Vector N))
    [IsProbabilityMeasure ν] (ρ : ℝ) (a : ℕ → ℝ≥0∞)
    (hslab : ∀ j : ℕ, j < k →
      ∀ᵐ (σ : Fin j → Vector N) ∂Measure.pi (fun _ : Fin j => ν),
        σ ∈ overlapBlock 0 ρ → a j ≤ ν {y | ∀ i, |overlap y (σ i)| < ρ}) :
    (∏ j ∈ Finset.range k, a j) ≤
      (Measure.pi (fun _ : Fin k => ν)) (overlapBlock 0 ρ) := by
  revert hslab
  induction k with
  | zero =>
      intro _
      have hB : overlapBlock (N := N) (k := 0) 0 ρ = Set.univ := by
        ext σ
        simp [overlapBlock]
      simp only [Finset.range_zero, Finset.prod_empty, hB, measure_univ, le_refl]
  | succ k ih =>
      intro hslab
      have hprev := ih (fun j hj => hslab j (Nat.lt_succ_of_lt hj))
      calc
        _ = a k * ∏ j ∈ Finset.range k, a j := by rw [Finset.prod_range_succ, mul_comm]
        _ ≤ a k * (Measure.pi (fun _ : Fin k => ν)) (overlapBlock 0 ρ) :=
          by gcongr
        _ ≤ _ := overlapBlock_pi_succ_lower ν ρ (a k) (hslab k (Nat.lt_succ_self k))

end SlowEquilibration.LiteratureSubagBandLowerFinal
