module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Lemmas.SmartPath.IndependentGaussianAffineIBP
public import Lemmas.SmartPath.IndependentEndpoint
public import Lemmas.Gaussian.CanonicalModel

@[expose] public section

/-!
Generic Gaussian free-energy calculus for the mixed physical branch.
The three elementary affine-growth helpers are adapted from the frozen
IndependentGaussianAffineIBP source (Apache-2.0); the covariance is arbitrary.
-/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass
open scoped BigOperators Topology NNReal ENNReal
namespace FourPapersCommon
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

variable {N : ℕ}
variable {E : Type*} [NormedAddCommGroup E]

theorem fderiv_gaussianFreeEnergy_firstVariation
    [NormedSpace ℝ E]
    (A : E →L[ℝ] EnergySpace N) (field v : EnergySpace N) (x y : E) :
    fderiv ℝ
        (fun z : E =>
          fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
            (A z + field) v) x y =
      (hessian_free_energy_fderiv (N := N) (A x + field)) (A y) v := by
  have hc : HasFDerivAt
      (fun z : E =>
        fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
          (A z + field))
      ((hessian_free_energy_fderiv (N := N) (A x + field)).comp A) x := by
    apply HasFDerivAt.comp x
    · have hcf : ContDiff ℝ 1
          (fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)) :=
        (contDiff_free_energy_density (N := N)).fderiv_right
          (m := (1 : WithTop ℕ∞)) (by
            change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
            exact WithTop.coe_le_coe.mpr le_top)
      exact (hcf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    · simpa using A.hasFDerivAt.add_const field
  have hv := hc.clm_apply (hasFDerivAt_const (x := x) (c := v))
  rw [hv.fderiv]
  simp

theorem abs_gaussianFreeEnergy_hessian_le
    (H u v : EnergySpace N) :
    |hessian_free_energy N H u v| ≤
      2 * (1 / (N : ℝ)) * ‖u‖ * ‖v‖ := by
  classical
  have hp_sum :
      ∑ σ : Config N, gibbs_pmf N H σ = 1 :=
    sum_gibbs_pmf N H
  have hfirst :
      |∑ σ : Config N, gibbs_pmf N H σ * u σ * v σ| ≤
        ‖u‖ * ‖v‖ := by
    calc
      |∑ σ : Config N, gibbs_pmf N H σ * u σ * v σ|
          ≤ ∑ σ : Config N,
              |gibbs_pmf N H σ * u σ * v σ| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : Config N,
            gibbs_pmf N H σ * (‖u‖ * ‖v‖) := by
        gcongr with σ
        rw [abs_mul, abs_mul,
          abs_of_nonneg (gibbs_pmf_nonneg N H σ)]
        have huv : |u σ| * |v σ| ≤ ‖u‖ * ‖v‖ :=
          mul_le_mul
            (abs_apply_le_norm N u σ)
            (abs_apply_le_norm N v σ)
            (abs_nonneg _) (norm_nonneg _)
        calc
          gibbs_pmf N H σ * |u σ| * |v σ| =
              gibbs_pmf N H σ * (|u σ| * |v σ|) := by
                ring
          _ ≤ gibbs_pmf N H σ * (‖u‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_left huv
              (gibbs_pmf_nonneg N H σ)
      _ = ‖u‖ * ‖v‖ := by
        rw [← Finset.sum_mul, hp_sum, one_mul]
  have hu :
      |∑ σ : Config N, gibbs_pmf N H σ * u σ| ≤ ‖u‖ := by
    calc
      |∑ σ : Config N, gibbs_pmf N H σ * u σ|
          ≤ ∑ σ : Config N,
              |gibbs_pmf N H σ * u σ| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : Config N,
            gibbs_pmf N H σ * ‖u‖ := by
        gcongr with σ
        rw [abs_mul,
          abs_of_nonneg (gibbs_pmf_nonneg N H σ)]
        exact mul_le_mul_of_nonneg_left
          (abs_apply_le_norm N u σ)
          (gibbs_pmf_nonneg N H σ)
      _ = ‖u‖ := by
        rw [← Finset.sum_mul, hp_sum, one_mul]
  have hv :
      |∑ σ : Config N, gibbs_pmf N H σ * v σ| ≤ ‖v‖ := by
    calc
      |∑ σ : Config N, gibbs_pmf N H σ * v σ|
          ≤ ∑ σ : Config N,
              |gibbs_pmf N H σ * v σ| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : Config N,
            gibbs_pmf N H σ * ‖v‖ := by
        gcongr with σ
        rw [abs_mul,
          abs_of_nonneg (gibbs_pmf_nonneg N H σ)]
        exact mul_le_mul_of_nonneg_left
          (abs_apply_le_norm N v σ)
          (gibbs_pmf_nonneg N H σ)
      _ = ‖v‖ := by
        rw [← Finset.sum_mul, hp_sum, one_mul]
  rw [hessian_free_energy, abs_mul]
  have hN0 : 0 ≤ (1 / (N : ℝ)) :=
    one_div_nonneg.mpr (Nat.cast_nonneg N)
  rw [abs_of_nonneg hN0]
  calc
    1 / (N : ℝ) *
        |(∑ σ : Config N,
            gibbs_pmf N H σ * u σ * v σ) -
          (∑ σ : Config N,
            gibbs_pmf N H σ * u σ) *
            ∑ τ : Config N,
              gibbs_pmf N H τ * v τ|
      ≤ 1 / (N : ℝ) *
          (|(∑ σ : Config N,
              gibbs_pmf N H σ * u σ * v σ)| +
            |(∑ σ : Config N,
              gibbs_pmf N H σ * u σ) *
              ∑ τ : Config N,
                gibbs_pmf N H τ * v τ|) := by
        gcongr
        exact abs_sub _ _
    _ ≤ 1 / (N : ℝ) *
        (‖u‖ * ‖v‖ + ‖u‖ * ‖v‖) := by
      gcongr
      rw [abs_mul]
      exact mul_le_mul hu hv (abs_nonneg _) (norm_nonneg _)
    _ = 2 * (1 / (N : ℝ)) * ‖u‖ * ‖v‖ := by
      ring

noncomputable def gaussianFreeEnergy_firstVariation_growth
    [NormedSpace ℝ E]
    (A : E →L[ℝ] EnergySpace N)
    (field v : EnergySpace N) :
    PhysLean.Probability.GaussianIBP.HasModerateGrowth
      (fun x : E =>
        fderiv ℝ
          (fun H : EnergySpace N =>
            free_energy_density (N := N) H)
          (A x + field) v) := by
  let C0 :=
    (SpinGlass.hasModerateGrowth_free_energy_density N).C
  let C1 := C0 * (1 + ‖field‖ + ‖A‖) * ‖v‖
  let C2 := 2 * (1 / (N : ℝ)) * ‖A‖ * ‖v‖
  let C := 1 + C1 + C2
  refine ⟨C, 1, ?_, ?_, ?_⟩
  · have hC0 : 0 < C0 :=
      (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos
    have hC1 : 0 ≤ C1 := by positivity
    have hC2 : 0 ≤ C2 := by positivity
    dsimp [C]
    positivity
  · intro x
    have hbase :=
      (SpinGlass.hasModerateGrowth_free_energy_density N).bound_dF_apply
        (A x + field) v
    have hm :
        (SpinGlass.hasModerateGrowth_free_energy_density N).m = 1 :=
      rfl
    rw [hm, pow_one] at hbase
    have hAx : ‖A x‖ ≤ ‖A‖ * ‖x‖ :=
      A.le_opNorm x
    have hsum :
        1 + ‖A x + field‖ ≤
          (1 + ‖field‖ + ‖A‖) * (1 + ‖x‖) := by
      have hadd := norm_add_le (A x) field
      nlinarith [norm_nonneg x, norm_nonneg field, norm_nonneg A]
    have hC0 : 0 ≤ C0 :=
      (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos.le
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
    have hmul :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum hC0) hv0
    have hC1 : 0 ≤ C1 := by positivity
    have hC2 : 0 ≤ C2 := by positivity
    have hx1 : 0 ≤ 1 + ‖x‖ := by positivity
    calc
      |fderiv ℝ
          (fun H : EnergySpace N =>
            free_energy_density (N := N) H)
          (A x + field) v| =
          ‖fderiv ℝ
            (fun H : EnergySpace N =>
              free_energy_density (N := N) H)
            (A x + field) v‖ := by
              rw [Real.norm_eq_abs]
      _ ≤ C0 * (1 + ‖A x + field‖) * ‖v‖ :=
        hbase
      _ ≤ C1 * (1 + ‖x‖) := by
        simpa [C1, mul_assoc, mul_comm, mul_left_comm]
          using hmul
      _ ≤ C * (1 + ‖x‖) := by
        apply mul_le_mul_of_nonneg_right _ hx1
        dsimp [C]
        linarith
      _ = C * (1 + ‖x‖) ^ 1 := by
        rw [pow_one]
  · intro x
    have hC2 : 0 ≤ C2 := by positivity
    have hop :
        ‖fderiv ℝ
          (fun z : E =>
            fderiv ℝ
              (fun H : EnergySpace N =>
                free_energy_density (N := N) H)
              (A z + field) v) x‖ ≤ C2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ hC2 ?_
      intro y
      rw [fderiv_gaussianFreeEnergy_firstVariation
        A field v x y,
        hessian_free_energy_fderiv_eq_hessian_free_energy]
      rw [Real.norm_eq_abs]
      have hh :=
        abs_gaussianFreeEnergy_hessian_le
          (N := N) (A x + field) (A y) v
      calc
        |hessian_free_energy N
            (A x + field) (A y) v|
            ≤ 2 * (1 / (N : ℝ)) * ‖A y‖ * ‖v‖ :=
          hh
        _ ≤ C2 * ‖y‖ := by
          have hAy := A.le_opNorm y
          have hfac : 0 ≤ 2 * (1 / (N : ℝ)) := by
            positivity
          have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
          have hmul :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hAy hfac) hv0
          simpa [C2, mul_assoc, mul_comm, mul_left_comm]
            using hmul
    have hC1 : 0 ≤ C1 := by
      have hC0 : 0 ≤ C0 :=
        (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos.le
      dsimp [C1]
      positivity
    have hx1 : 1 ≤ 1 + ‖x‖ := by
      linarith [norm_nonneg x]
    calc
      ‖fderiv ℝ
          (fun z : E =>
            fderiv ℝ
              (fun H : EnergySpace N =>
                free_energy_density (N := N) H)
              (A z + field) v) x‖
          ≤ C2 :=
        hop
      _ ≤ C * (1 + ‖x‖) := by
        have hC2C : C2 ≤ C := by
          dsimp [C]
          linarith
        exact hC2C.trans
          (le_mul_of_one_le_right
            (by dsimp [C]; positivity) hx1)
      _ = C * (1 + ‖x‖) ^ 1 := by
        rw [pow_one]


theorem gaussianFreeEnergy_ibp_linear
    [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (g : Ω → E)
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (A B : E →L[ℝ] EnergySpace N) (field : EnergySpace N) :
    (∫ ω, fderiv ℝ (free_energy_density (N := N))
        (A (g ω) + field) (B (g ω))) =
      ∫ ω, ∑ i : hg.ι, (hg.τ i : ℝ) * hessian_free_energy N
        (A (g ω) + field) (A (hg.w i)) (B (hg.w i)) := by
  have hd (i : hg.ι) : ContDiff ℝ 1
      (fun x : E => fderiv ℝ (free_energy_density (N := N))
        (A x + field) (B (hg.w i))) := by
    have hgrad : ContDiff ℝ 1 (fderiv ℝ (free_energy_density (N := N))) :=
      (contDiff_free_energy_density (N := N)).fderiv_right
        (m := (1 : WithTop ℕ∞)) (by
          change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top)
    exact (hgrad.comp (A.contDiff.add contDiff_const)).clm_apply contDiff_const
  rw [SpinGlass.GeneralizedLatala.gaussian_ibp_gradient_linear g hg A B field
    (free_energy_density (N := N)) hd
    (fun i => gaussianFreeEnergy_firstVariation_growth A field (B (hg.w i)))]
  apply integral_congr_ae
  filter_upwards with ω
  congr 1
  funext i
  rw [fderiv_gaussianFreeEnergy_firstVariation,
    hessian_free_energy_fderiv_eq_hessian_free_energy]

theorem gaussianLinearImage_secondMoment
    [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (g : Ω → E)
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (A B : E →L[ℝ] EnergySpace N) (σ τ : Config N) :
    (∫ ω, A (g ω) σ * B (g ω) τ) =
      ∑ i : hg.ι, (hg.τ i : ℝ) * A (hg.w i) σ * B (hg.w i) τ := by
  classical
  have hpoint (ω : Ω) : g ω = ∑ i, hg.c i ω • hg.w i := congrFun hg.repr ω
  have hc (i : hg.ι) : HasGaussianLaw (hg.c i) volume := HasLaw.hasGaussianLaw
    (HasLaw.mk (hg.c_meas i).aemeasurable (hg.c_gauss i))
  have hint (i j : hg.ι) : Integrable
      (fun ω => hg.c i ω * A (hg.w i) σ * (hg.c j ω * B (hg.w j) τ)) := by
    have hij := (hc i).memLp_two.integrable_mul (hc j).memLp_two
    convert hij.const_mul (A (hg.w i) σ * B (hg.w j) τ) using 1
    ext ω
    simp only [Pi.mul_apply]
    ring
  have hApoint (ω : Ω) : A (g ω) σ = ∑ i, hg.c i ω * A (hg.w i) σ := by
    rw [hpoint]
    simp
  have hBpoint (ω : Ω) : B (g ω) τ = ∑ i, hg.c i ω * B (hg.w i) τ := by
    rw [hpoint]
    simp
  simp_rw [hApoint, hBpoint]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j)]
  simp_rw [show ∀ i j, (fun ω => hg.c i ω * A (hg.w i) σ *
      (hg.c j ω * B (hg.w j) τ)) =
      fun ω => (A (hg.w i) σ * B (hg.w j) τ) * (hg.c i ω * hg.c j ω) by
    intro i j; funext ω; ring, integral_const_mul,
    SpinGlass.GeneralizedLatala.gaussianHilbert_coord_secondMoment g hg]
  simp
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem bilinear_spectral_contraction {ι : Type*} [Fintype ι]
    (T : EnergySpace N →L[ℝ] EnergySpace N →L[ℝ] ℝ)
    (a : ι → ℝ) (u v : ι → EnergySpace N) :
    (∑ i, a i * T (u i) (v i)) =
      ∑ σ : Config N, ∑ τ : Config N,
        (∑ i, a i * u i σ * v i τ) * T (std_basis N σ) (std_basis N τ) := by
  classical
  calc
    (∑ i, a i * T (u i) (v i)) =
        ∑ i, a i * ∑ σ : Config N, ∑ τ : Config N,
          u i σ * v i τ * T (std_basis N σ) (std_basis N τ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [SpinGlass.GeneralizedLatala.bilin_eq_sum_std N T]
    _ = _ := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem gaussianFreeEnergy_trace_covariance
    [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (g : Ω → E)
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (A B : E →L[ℝ] EnergySpace N) (H : EnergySpace N) :
    (∑ i : hg.ι, (hg.τ i : ℝ) * hessian_free_energy N H
        (A (hg.w i)) (B (hg.w i))) =
      ∑ σ : Config N, ∑ τ : Config N,
        (∫ ω, A (g ω) σ * B (g ω) τ) *
          hessian_free_energy N H (std_basis N σ) (std_basis N τ) := by
  classical
  simp_rw [gaussianLinearImage_secondMoment g hg A B,
    ← hessian_free_energy_fderiv_eq_hessian_free_energy]
  exact bilinear_spectral_contraction _ _ _ _

theorem abs_gaussianFreeEnergy_firstVariation_le (H v : EnergySpace N) :
    |fderiv ℝ (free_energy_density (N := N)) H v| ≤ (1 / (N : ℝ)) * ‖v‖ := by
  classical
  rw [fderiv_free_energy_density_apply, abs_mul, abs_neg,
    abs_of_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg N))]
  apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (Nat.cast_nonneg N))
  calc
    |∑ σ : Config N, gibbs_pmf N H σ * v σ| ≤
        ∑ σ : Config N, |gibbs_pmf N H σ * v σ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Config N, gibbs_pmf N H σ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg N H σ)]
      exact mul_le_mul_of_nonneg_left (abs_apply_le_norm N v σ) (gibbs_pmf_nonneg N H σ)
    _ = ‖v‖ := by rw [← Finset.sum_mul, sum_gibbs_pmf, one_mul]

theorem integrable_gaussianFreeEnergy_affine
    [NormedSpace ℝ E] {g : Ω → E} (hg : Integrable g)
    (A : E →L[ℝ] EnergySpace N) (field : EnergySpace N) :
    Integrable (fun ω => free_energy_density (N := N) (A (g ω) + field)) := by
  let C := (hasModerateGrowth_free_energy_density N).C
  have hC : 0 ≤ C := (hasModerateGrowth_free_energy_density N).Cpos.le
  have hint : Integrable (fun ω => C * (1 + (‖A‖ * ‖g ω‖ + ‖field‖))) :=
    ((integrable_const 1).add ((hg.norm.const_mul ‖A‖).add (integrable_const ‖field‖))).const_mul C
  apply hint.mono'
  · exact (contDiff_free_energy_density (N := N)).continuous.comp_aestronglyMeasurable
      ((A.continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable).add_const field)
  · filter_upwards with ω
    have hh := (hasModerateGrowth_free_energy_density N).F_bound (A (g ω) + field)
    change |free_energy_density (N := N) (A (g ω) + field)| ≤ C * (1 + ‖A (g ω) + field‖) ^ 1 at hh
    rw [pow_one] at hh
    rw [Real.norm_eq_abs]
    exact hh.trans (mul_le_mul_of_nonneg_left
      (by linarith [norm_add_le (A (g ω)) field, A.le_opNorm (g ω)]) hC)

def gaussianSpectralCovariance {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (u v : ι → EnergySpace N) (σ τ : Config N) : ℝ :=
  ∑ i, a i * u i σ * v i τ

theorem gaussianSpectralCovariance_linearCombination {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (u v : ι → EnergySpace N) (b c d e : ℝ) (σ τ : Config N) :
    gaussianSpectralCovariance a (fun i => b • u i + c • v i)
        (fun i => d • u i + e • v i) σ τ =
      b * d * gaussianSpectralCovariance a u u σ τ +
      b * e * gaussianSpectralCovariance a u v σ τ +
      c * d * gaussianSpectralCovariance a v u σ τ +
      c * e * gaussianSpectralCovariance a v v σ τ := by
  classical
  unfold gaussianSpectralCovariance
  calc
    (∑ i, a i * (b • u i + c • v i) σ * (d • u i + e • v i) τ) =
        ∑ i, (b * d * (a i * u i σ * u i τ) + b * e * (a i * u i σ * v i τ) +
          c * d * (a i * v i σ * u i τ) + c * e * (a i * v i σ * v i τ)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem gaussianFreeEnergy_hessian_offdiag (H : EnergySpace N) {σ τ : Config N}
    (hστ : σ ≠ τ) :
    hessian_free_energy N H (std_basis N σ) (std_basis N τ) =
      -(1 / (N : ℝ)) * gibbs_pmf N H σ * gibbs_pmf N H τ := by
  classical
  simp [hessian_free_energy, std_basis, hστ]
  ring

theorem gaussianFreeEnergy_covariance_contraction_nonpos (H : EnergySpace N)
    (C : Config N → Config N → ℝ) (hdiag : ∀ σ, C σ σ = 0)
    (hC : ∀ σ τ, 0 ≤ C σ τ) :
    (∑ σ : Config N, ∑ τ : Config N,
      C σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) ≤ 0 := by
  classical
  apply Finset.sum_nonpos
  intro σ _
  apply Finset.sum_nonpos
  intro τ _
  by_cases he : σ = τ
  · subst τ
    simp [hdiag]
  · rw [gaussianFreeEnergy_hessian_offdiag H he]
    have hh : -(1 / (N : ℝ)) * gibbs_pmf N H σ * gibbs_pmf N H τ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (gibbs_pmf_nonneg N H σ))
        (gibbs_pmf_nonneg N H τ)
    exact mul_nonpos_of_nonneg_of_nonpos (hC σ τ) hh

end FourPapersCommon
