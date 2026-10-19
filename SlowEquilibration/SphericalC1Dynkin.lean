-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC1Dynamics
public import SlowEquilibration.SphericalReversibility

/-! The actual C² Itô and Dynkin identities for the C¹-gradient spherical
Picard process. Only the drift's C¹ regularity is used. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace ContDiff
namespace SlowEquilibration.SphericalC1Dynamics
open SphericalAging HardSphereDynamics LocalSDE SphericalModel SphericalDynamics
open VectorIto AnnealedSDECore PhysicalC2Ito MultivariateItoFormula MultivariateTaylor
open SphericalReversibility.Ito
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

namespace Ito
lemma generator_continuous (β : ℝ) (gfield : State N → State N)
    (hgfield : ContDiff ℝ 1 gfield) {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (coefficientGenerator β gfield f) := by
  have hD := hf.continuous_fderiv (by norm_num)
  have hH := hessian_continuous hf
  unfold coefficientGenerator
  exact (hD.clm_apply (SphericalC1Dynamics.contDiff_drift β gfield hgfield).continuous).add
    ((continuous_finsetSum Finset.univ (fun j _ =>
      (hH.clm_apply (contDiff_noiseColumn j).continuous).clm_apply
        (contDiff_noiseColumn j).continuous)).const_mul _)

lemma generator_integral_coordinates (β : ℝ) (gfield : State N → State N) (hgfield : ContDiff ℝ 1 gfield)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (g : ℝ≥0 → State N)
    (hg : Continuous g) (T : ℝ≥0) :
    (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) T,fderiv ℝ f (g s) (basisVector i)*
      drift β gfield (g s) i ∂nonnegativeLebesgueMeasure)+
    (1/2 : ℝ)*(∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
      Hessian f (g s) (basisVector i) (basisVector k)*
        (∑ j : Fin N,noiseColumn (g s) j i*noiseColumn (g s) j k) ∂nonnegativeLebesgueMeasure)=
    ∫ s in Ioc (0 : ℝ≥0) T,coefficientGenerator β gfield f (g s) ∂nonnegativeLebesgueMeasure := by
  let d (i : Fin N) (s : ℝ≥0) := fderiv ℝ f (g s) (basisVector i)*drift β gfield (g s) i
  let q (i k : Fin N) (s : ℝ≥0) := Hessian f (g s) (basisVector i) (basisVector k)*
    (∑ j : Fin N,noiseColumn (g s) j i*noiseColumn (g s) j k)
  have hd (i : Fin N) : IntegrableOn (d i) (Ioc (0 : ℝ≥0) T) nonnegativeLebesgueMeasure := by
    have hc : Continuous (d i) := ((MultivariateItoWeights.derivative_basis_continuous hf i).comp hg).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp ((SphericalC1Dynamics.contDiff_drift β gfield hgfield).continuous.comp hg))
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
    _ = _ := integral_congr_ae (.of_forall (fun s => (generator_coordinates β gfield f (g s)).symm))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Genuine general C² Itô formula for the actual sphere Hamiltonian SDE,
with the actual physical coefficient generator rather than an assumed PDE. -/
theorem physical_C2_ito_formula (D : BrownianDriver N P F)
    (β : ℝ) (gfield : State N → State N) (hgfield : ContDiff ℝ 1 gfield) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (T : ℝ≥0) (hX : IsRandomStrongSolutionOn D
      (fun _ i x => drift β gfield x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ omega ∂P,∀ s,OnSphere (X s omega)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    ∃ V : Fin N → Fin N → PredictableProcessL2 F P,
      (∀ i j,(V i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun s omega => fderiv ℝ f (X s omega) (basisVector i)*noiseColumn (X s omega) j i) T) ∧
      ∀ᵐ omega ∂P,f (X T omega)=f (Z0 omega)+
        (∫ s in Ioc (0 : ℝ≥0) T,coefficientGenerator β gfield f (X s omega) ∂nonnegativeLebesgueMeasure)+
        ∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) omega := by
  have hb : ∀ᵐ omega ∂P,∀ s,‖X s omega‖≤R := by
    filter_upwards [hXs] with omega homega
    intro s
    have hn : ‖X s omega‖^2=(N : ℝ) := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using homega s
    nlinarith [norm_nonneg (X s omega)]
  obtain ⟨V,hV,he⟩ := strong_C2_ito_formula D T hX
    (fun _ i j => (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp (contDiff_noiseColumn j).continuous)
    R hR hb hf
  refine ⟨V,hV,?_⟩
  filter_upwards [he,hX.2.2.1] with omega heomega hc
  have hg := generator_integral_coordinates β gfield hgfield hf (fun s => X s omega) hc T
  linarith


open ActualC2Dynkin SharpRadialMoment PredictableDriftTime

theorem physical_C2_expectation_eq (D : BrownianDriver N P F)
    (β : ℝ) (gfield : State N → State N) (hgfield : ContDiff ℝ 1 gfield) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (T : ℝ≥0) (hX : IsRandomStrongSolutionOn D
      (fun _ i x => drift β gfield x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ omega ∂P,∀ s,OnSphere (X s omega)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    (∫ omega,f (X T omega) ∂P)=(∫ omega,f (Z0 omega) ∂P)+
      ∫ s in (0 : ℝ)..(T : ℝ),∫ omega,coefficientGenerator β gfield f (X s.toNNReal omega) ∂P := by
  obtain ⟨V,hV,he⟩ := physical_C2_ito_formula D β gfield hgfield T hX hXs R hR hNR hf
  let G : ℝ≥0 → Ω → ℝ := fun s omega => coefficientGenerator β gfield f (X s omega)
  have hGa : StronglyAdapted F G := fun s => (generator_continuous β gfield hgfield hf).comp_stronglyMeasurable (hX.2.1 s)
  have hGc : ∀ᵐ omega ∂P,Continuous (fun s => G s omega) := hX.2.2.1.mono
    (fun _ hc => (generator_continuous β gfield hgfield hf).comp hc)
  obtain ⟨Kg,hKg⟩ := sphere_observable_bound _ (generator_continuous β gfield hgfield hf) R hR hNR X hXs
  obtain ⟨Kf,hKf⟩ := sphere_observable_bound f hf.continuous R hR hNR X hXs
  have hf0 : Integrable (fun omega => f (X 0 omega)) P := Integrable.of_bound
    (hf.continuous.comp_aestronglyMeasurable (((hX.2.1 0).mono (F.le 0)).aestronglyMeasurable)) Kf
    (hKf.mono (fun _ h => h 0))
  have hfZ : Integrable (fun omega => f (Z0 omega)) P := hf0.congr
    ((randomStrong_initial_ae D T hX).mono (fun _ h => congrArg f h))
  have hGI : Integrable (fun omega => ∫ s in Ioc (0 : ℝ≥0) T,G s omega ∂nonnegativeLebesgueMeasure) P := by
    have hi := (timeCut_integrable G hGa hGc Kg hKg T).integral_prod_right
    convert hi using 1
    funext omega
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      by_cases hs : s ∈ Ioc (0 : ℝ≥0) T <;> simp [Set.indicator,FourPapersCommon.continuousAdaptedTimeCut,hs])
  have hnoise := integrable_finsetSum Finset.univ
    (fun i _ => (Lp.memLp (vectorIto D (V i))).integrable (by norm_num))
  rw [integral_congr_ae he]
  have hsum := integral_add (hfZ.add hGI) hnoise
  have hfirst := integral_add hfZ hGI
  simp only [Pi.add_apply] at hsum hfirst
  rw [hsum,hfirst,integral_finsetSum _ (fun i _ => (Lp.memLp (vectorIto D (V i))).integrable (by norm_num))]
  simp only [vectorIto_expectation_zero,Finset.sum_const_zero,add_zero]
  congr 1
  exact expectation_time_integral G hGa hGc Kg hKg T

/-- True generator evolution for every C² observable on the actual
physical sphere process, with no backward PDE assumed. -/
theorem physical_C2_hasDerivAt (D : BrownianDriver N P F)
    (β : ℝ) (gfield : State N → State N) (hgfield : ContDiff ℝ 1 gfield) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D
      (fun _ i x => drift β gfield x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ omega ∂P,∀ s,OnSphere (X s omega)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => ∫ omega,f (X s.toNNReal omega) ∂P)
      (∫ omega,coefficientGenerator β gfield f (X t.toNNReal omega) ∂P) t := by
  obtain ⟨K,hK⟩ := sphere_observable_bound _ (generator_continuous β gfield hgfield hf) R hR hNR X hXs
  have hmean : Continuous (fun s : ℝ => ∫ omega,coefficientGenerator β gfield f (X s.toNNReal omega) ∂P) :=
    (firstMoment_continuous (P := P) (fun s omega => coefficientGenerator β gfield f (X s omega))
      (fun s => (generator_continuous β gfield hgfield hf).comp_stronglyMeasurable ((hX 0).2.1 s))
      ((hX 0).2.2.1.mono (fun _ hc => (generator_continuous β gfield hgfield hf).comp hc)) K hK).comp continuous_real_toNNReal
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hmean.intervalIntegrable (0 : ℝ) t) (hmean.stronglyMeasurableAtFilter volume (𝓝 t))
    hmean.continuousAt).const_add (∫ omega,f (Z0 omega) ∂P)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [physical_C2_expectation_eq D β gfield hgfield s.toNNReal (hX s.toNNReal) hXs R hR hNR hf,
    Real.coe_toNNReal _ hs.le]


theorem physical_C2_hasDerivWithinAt_zero (D : BrownianDriver N P F)
    (β : ℝ) (gfield : State N → State N) (hgfield : ContDiff ℝ 1 gfield) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D
      (fun _ i x => drift β gfield x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ omega ∂P,∀ s,OnSphere (X s omega)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt (fun s : ℝ => ∫ omega,f (X s.toNNReal omega) ∂P)
      (∫ omega,coefficientGenerator β gfield f (Z0 omega) ∂P) (Ici 0) 0 := by
  obtain ⟨K,hK⟩ := sphere_observable_bound _ (generator_continuous β gfield hgfield hf) R hR hNR X hXs
  have hmean : Continuous (fun s : ℝ => ∫ omega,coefficientGenerator β gfield f (X s.toNNReal omega) ∂P) :=
    (firstMoment_continuous (P := P) (fun s omega => coefficientGenerator β gfield f (X s omega))
      (fun s => (generator_continuous β gfield hgfield hf).comp_stronglyMeasurable ((hX 0).2.1 s))
      ((hX 0).2.2.1.mono (fun _ hc => (generator_continuous β gfield hgfield hf).comp hc)) K hK).comp continuous_real_toNNReal
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hmean.intervalIntegrable (0 : ℝ) 0) (hmean.stronglyMeasurableAtFilter volume (𝓝 0))
    hmean.continuousAt).const_add (∫ omega,f (Z0 omega) ∂P)
  have he : (∫ omega,coefficientGenerator β gfield f (X (Real.toNNReal 0) omega) ∂P)=
      ∫ omega,coefficientGenerator β gfield f (Z0 omega) ∂P := by
    rw [Real.toNNReal_zero]
    apply integral_congr_ae
    filter_upwards [randomStrong_initial_ae D 0 (hX 0)] with omega homega
    rw [homega]
  rw [he] at hd
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [physical_C2_expectation_eq D β gfield hgfield s.toNNReal (hX s.toNNReal) hXs R hR hNR hf,
      Real.coe_toNNReal _ hs]
  · rw [Real.toNNReal_zero,physical_C2_expectation_eq D β gfield hgfield 0 (hX 0) hXs R hR hNR hf]
    simp


end Ito

/-- The actual C¹-gradient process satisfies the random-initial interface
of the genuine multivariate Itô construction. -/
theorem process_randomStrongSolution (hN : N ≠ 0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    IsRandomStrongSolutionOn (FixedCoefficients.canonicalDriver N)
      (fun _ i z => drift β g z i) (fun _ i j z => noiseColumn z j i)
      (fun _ => x) (process β g hg x) T :=
  RandomSDEConversions.localStrongSolution_to_random
    (fun i => (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp
      (SphericalC1Dynamics.contDiff_drift β g hg).continuous)
    (process_physical hN β g hg x hx T)

/-- Literal Brownian expectation of the constructed process. -/
def expectation (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (t : ℝ≥0) (f : State N → ℝ) (x : State N) : ℝ :=
  ∫ omega,f (process β g hg x t omega) ∂VectorBrownian.law N

/-- Genuine Dynkin identity, for every C² observable. -/
theorem expectation_dynkin (hN : N ≠ 0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (hx : OnSphere x) {f : State N → ℝ}
    (hf : ContDiff ℝ 2 f) (T : ℝ≥0) :
    expectation β g hg T f x = f x +
      ∫ s in (0 : ℝ)..(T : ℝ),expectation β g hg s.toNNReal
        (coefficientGenerator β g f) x := by
  simpa only [expectation,integral_const,probReal_univ,one_smul] using
    Ito.physical_C2_expectation_eq (FixedCoefficients.canonicalDriver N) β g hg T
      (process_randomStrongSolution hN β g hg x hx T)
      (process_onSphere hN β g hg x hx) (cutoffRadius N) (cutoffRadius_pos N)
      (cutoffRadius_contains_sphere N) hf

/-- The right derivative at time zero is the literal physical generator. -/
theorem expectation_hasDerivWithinAt_zero (hN : N ≠ 0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (hx : OnSphere x) {f : State N → ℝ}
    (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt (fun s : ℝ => expectation β g hg s.toNNReal f x)
      (coefficientGenerator β g f x) (Ici 0) 0 := by
  simpa only [expectation,integral_const,probReal_univ,one_smul] using
    Ito.physical_C2_hasDerivWithinAt_zero (FixedCoefficients.canonicalDriver N) β g hg
      (fun T => process_randomStrongSolution hN β g hg x hx T)
      (process_onSphere hN β g hg x hx) (cutoffRadius N) (cutoffRadius_pos N)
      (cutoffRadius_contains_sphere N) hf

end SlowEquilibration.SphericalC1Dynamics
