module

public import SphericalAging.MultivariateItoFormula

public section

/-! The genuine C² Itô formula with the actual Hamiltonian sphere generator,
including identified full-filtration predictable stochastic integrands. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PhysicalC2Ito
open HardSphereDynamics LocalSDE VectorIto AnnealedSDECore
open MultivariateTaylor MultivariateItoFormula
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma derivative_coordinates (f : State N → ℝ) (x v : State N) :
    fderiv ℝ f x v=∑ i : Fin N,fderiv ℝ f x (basisVector i)*v i := by
  conv_lhs => rw [← state_sum_basis v]
  simp only [map_sum,map_smul,smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma noise_hessian_coordinates (H : State N →L[ℝ] State N →L[ℝ] ℝ) (x : State N) :
    (∑ j : Fin N,H (noiseColumn x j) (noiseColumn x j))=
      ∑ i : Fin N,∑ k : Fin N,H (basisVector i) (basisVector k)*
        (∑ j : Fin N,noiseColumn x j i*noiseColumn x j k) := by
  rw [show (∑ j : Fin N,H (noiseColumn x j) (noiseColumn x j))=
      ∑ j : Fin N,∑ i : Fin N,∑ k : Fin N,noiseColumn x j i*noiseColumn x j k*H (basisVector i) (basisVector k) from
        Finset.sum_congr rfl (fun j _ => SphereGenerator.bilinear_coordinates H _ _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma generator_coordinates (β : ℝ) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (x : State N) :
    SphereGenerator.coefficientGenerator β J f x=
      (∑ i : Fin N,fderiv ℝ f x (basisVector i)*hamiltonianDrift β J x i)+
      (1/2 : ℝ)*(∑ i : Fin N,∑ k : Fin N,Hessian f x (basisVector i) (basisVector k)*
        (∑ j : Fin N,noiseColumn x j i*noiseColumn x j k)) := by
  unfold SphereGenerator.coefficientGenerator
  rw [derivative_coordinates,noise_hessian_coordinates]

lemma generator_continuous (β : ℝ) (J : FiniteModel.Disorder N p)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (SphereGenerator.coefficientGenerator β J f) := by
  have hD := hf.continuous_fderiv (by norm_num)
  have hH := hessian_continuous hf
  unfold SphereGenerator.coefficientGenerator
  exact (hD.clm_apply (contDiff_hamiltonianDrift β J).continuous).add
    ((continuous_finsetSum Finset.univ (fun j _ =>
      (hH.clm_apply (contDiff_noiseColumn j).continuous).clm_apply (contDiff_noiseColumn j).continuous)).const_mul _)

/-- Actual time integration of the coordinate drift and covariance is
precisely the actual Frechet coefficient generator integral. -/
lemma generator_integral_coordinates (β : ℝ) (J : FiniteModel.Disorder N p)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (g : ℝ≥0 → State N)
    (hg : Continuous g) (T : ℝ≥0) :
    (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) T,fderiv ℝ f (g s) (basisVector i)*
      hamiltonianDrift β J (g s) i ∂nonnegativeLebesgueMeasure)+
    (1/2 : ℝ)*(∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
      Hessian f (g s) (basisVector i) (basisVector k)*
        (∑ j : Fin N,noiseColumn (g s) j i*noiseColumn (g s) j k) ∂nonnegativeLebesgueMeasure)=
    ∫ s in Ioc (0 : ℝ≥0) T,SphereGenerator.coefficientGenerator β J f (g s) ∂nonnegativeLebesgueMeasure := by
  let d (i : Fin N) (s : ℝ≥0) := fderiv ℝ f (g s) (basisVector i)*hamiltonianDrift β J (g s) i
  let q (i k : Fin N) (s : ℝ≥0) := Hessian f (g s) (basisVector i) (basisVector k)*
    (∑ j : Fin N,noiseColumn (g s) j i*noiseColumn (g s) j k)
  have hd (i : Fin N) : IntegrableOn (d i) (Ioc (0 : ℝ≥0) T) nonnegativeLebesgueMeasure := by
    have hc : Continuous (d i) := ((MultivariateItoWeights.derivative_basis_continuous hf i).comp hg).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp ((contDiff_hamiltonianDrift β J).continuous.comp hg))
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hq (i k : Fin N) : IntegrableOn (q i k) (Ioc (0 : ℝ≥0) T) nonnegativeLebesgueMeasure := by
    have hnoise (j a : Fin N) : Continuous (fun s => noiseColumn (g s) j a) :=
      (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) a).comp ((contDiff_noiseColumn j).continuous.comp hg)
    have hc : Continuous (q i k) := ((MultivariateItoSums.hessian_basis_continuous hf i k).comp hg).mul
      (continuous_finsetSum Finset.univ (fun j _ => (hnoise j i).mul (hnoise j k)))
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hds := integrable_finsetSum Finset.univ (fun i _ => hd i)
  have hqs := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun k _ => hq i k))
  change (∑ i,∫ s in Ioc (0 : ℝ≥0) T,d i s ∂nonnegativeLebesgueMeasure)+
    (1/2 : ℝ)*(∑ i,∑ k,∫ s in Ioc (0 : ℝ≥0) T,q i k s ∂nonnegativeLebesgueMeasure)=_
  calc
    _ = (∫ s in Ioc (0 : ℝ≥0) T,∑ i,d i s ∂nonnegativeLebesgueMeasure)+
      (1/2 : ℝ)*(∫ s in Ioc (0 : ℝ≥0) T,∑ i,∑ k,q i k s ∂nonnegativeLebesgueMeasure) := by
        rw [integral_finsetSum _ (fun i _ => hd i),
          integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hq i k))]
        congr 2
        exact Finset.sum_congr rfl (fun i _ => (integral_finsetSum _ (fun k _ => hq i k)).symm)
    _ = ∫ s in Ioc (0 : ℝ≥0) T,((∑ i,d i s)+(1/2 : ℝ)*(∑ i,∑ k,q i k s)) ∂nonnegativeLebesgueMeasure := by
      have he := integral_add hds (hqs.const_mul (1/2 : ℝ))
      rw [he,integral_const_mul]
    _ = _ := integral_congr_ae (.of_forall (fun s => (generator_coordinates β J f (g s)).symm))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Genuine general C² Itô formula for the actual sphere Hamiltonian SDE,
with the actual physical coefficient generator rather than an assumed PDE. -/
theorem physical_C2_ito_formula (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (T : ℝ≥0) (hX : IsRandomStrongSolutionOn D
      (fun _ i x => hamiltonianDrift β J x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    ∃ V : Fin N → Fin N → PredictableProcessL2 F P,
      (∀ i j,(V i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun s ω => fderiv ℝ f (X s ω) (basisVector i)*noiseColumn (X s ω) j i) T) ∧
      ∀ᵐ ω ∂P,f (X T ω)=f (Z0 ω)+
        (∫ s in Ioc (0 : ℝ≥0) T,SphereGenerator.coefficientGenerator β J f (X s ω) ∂nonnegativeLebesgueMeasure)+
        ∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) ω := by
  have hb : ∀ᵐ ω ∂P,∀ s,‖X s ω‖≤R := by
    filter_upwards [hXs] with ω hω
    intro s
    have hn : ‖X s ω‖^2=(N : ℝ) := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hω s
    nlinarith [norm_nonneg (X s ω)]
  obtain ⟨V,hV,he⟩ := strong_C2_ito_formula D T hX
    (fun _ i j => (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp (contDiff_noiseColumn j).continuous)
    R hR hb hf
  refine ⟨V,hV,?_⟩
  filter_upwards [he,hX.2.2.1] with ω heω hc
  have hg := generator_integral_coordinates β J hf (fun s => X s ω) hc T
  linarith

end SphericalAging.PhysicalC2Ito
