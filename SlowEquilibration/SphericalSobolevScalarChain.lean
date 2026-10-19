-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalFormCore
public import SlowEquilibration.SphericalBoundedMultiplierConvergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Genuine bounded smooth scalar chain calculus on the completed
spherical Gibbs gradient graph. Closure is proved using smooth graph
approximants, an actual L² almost everywhere subsequence and dominated
bounded multiplier convergence. -/
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SlowEquilibration.SphericalForm
open SphericalModel SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts ConditionedEntrance.KilledOperator
open SphericalBoundedMultiplierConvergence
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem lieDerivative_scalar_comp (A : Operator N) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ 1 Φ) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) (x : Vector N) :
    lieDerivative A (Φ ∘ f) x=deriv Φ (f x)*lieDerivative A f x := by
  have hd := ((hΦ.differentiable (by norm_num) (f x)).hasDerivAt).comp_hasFDerivAt x
    (hf.differentiable (by norm_num) x).hasFDerivAt
  unfold lieDerivative
  rw [hd.fderiv]
  simp only [_root_.smul_apply,smul_eq_mul]

def scalarGradientMultiplier (_hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (_hH : Continuous H) (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (K : ℝ≥0) (hK : ∀ r,‖deriv Φ r‖ ≤ K)
    (U : Lp ℝ 2 (gibbsLaw N β H))
    (G : PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H))) :
    PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)) :=
  WithLp.toLp 2 (fun ij => multiplication (gibbsLaw N β H)
    (fun x => deriv Φ (U x)) ((hΦ.continuous_deriv_one).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable U)) K (.of_forall (fun x => hK (U x))) (G ij))

theorem normalizedRotationGradientL2_scalar_comp (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (K : ℝ≥0) (hK : ∀ r,‖deriv Φ r‖ ≤ K) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) :
    normalizedRotationGradientL2 hN β H hH (Φ ∘ f) (hΦ.comp hf)=
      scalarGradientMultiplier hN β H hH Φ hΦ K hK
        (gibbsToL2 hN β H hH f hf.continuous) (normalizedRotationGradientL2 hN β H hH f hf) := by
  apply PiLp.ext
  intro ij
  let U := gibbsToL2 hN β H hH f hf.continuous
  let A := coordinateRotation ij.1 ij.2
  let V := gibbsToL2 hN β H hH (lieDerivative A f) (lieDerivative_continuous A hf)
  let W := gibbsToL2 hN β H hH (lieDerivative A (Φ ∘ f)) (lieDerivative_continuous A (hΦ.comp hf))
  change gradientScale N • W=multiplication (gibbsLaw N β H)
    (fun x => deriv Φ (U x)) ((hΦ.continuous_deriv_one).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable U)) K (.of_forall (fun x => hK (U x))) (gradientScale N • V)
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (gradientScale N) W,Lp.coeFn_smul (gradientScale N) V,
    multiplication_ae (gibbsLaw N β H) (fun x => deriv Φ (U x))
      ((hΦ.continuous_deriv_one).comp_aestronglyMeasurable (Lp.aestronglyMeasurable U))
      K (.of_forall (fun x => hK (U x))) (gradientScale N • V),
    gibbsToL2_coe hN β H hH f hf.continuous,
    gibbsToL2_coe hN β H hH (lieDerivative A f) (lieDerivative_continuous A hf),
    gibbsToL2_coe hN β H hH (lieDerivative A (Φ ∘ f)) (lieDerivative_continuous A (hΦ.comp hf))]
      with x hw hv hm hu hdf hdΦf
  change U x=f x at hu
  change V x=lieDerivative A f x at hdf
  change W x=lieDerivative A (Φ ∘ f) x at hdΦf
  rw [hw,hm,hv,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,hu,hdf,hdΦf,
    lieDerivative_scalar_comp A Φ hΦ f hf x]
  ring

/-- Actual completed-domain scalar chain rule, with the literal multiplier
Φ′(u) and the original normalized rotation gradient. -/
theorem sphericalSobolevGraph_scalar_chain (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0=0) (K : ℝ≥0) (hK : ∀ r,‖deriv Φ r‖ ≤ K)
    (u : sphericalSobolevGraph hN β H hH) :
    let hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by simp)
    let hL := lipschitzWith_of_nnnorm_deriv_le (hΦ1.differentiable (by norm_num))
      (fun r => show ‖deriv Φ r‖₊ ≤ K from hK r)
    ∃ v : sphericalSobolevGraph hN β H hH,
      v.val.fst=hL.compLp hΦ0 u.val.fst ∧
      v.val.snd=scalarGradientMultiplier hN β H hH Φ hΦ1 K hK u.val.fst u.val.snd := by
  let hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by simp)
  let hL := lipschitzWith_of_nnnorm_deriv_le (hΦ1.differentiable (by norm_num))
    (fun r => show ‖deriv Φ r‖₊ ≤ K from hK r)
  have hm : u.val∈closure (Set.range (smoothGradientGraphLinear hN β H hH)) := u.property
  obtain ⟨q,hq,hqLim⟩ := mem_closure_iff_seq_limit.mp hm
  choose f hf using hq
  have hseq : (fun n => smoothGradientGraphLinear hN β H hH (f n))=q := funext hf
  rw [← hseq] at hqLim
  have hpair := ((WithLp.homeomorphProd 2 _ _).continuous.tendsto u.val).comp hqLim
  have hU := (continuous_fst.tendsto u.val.ofLp).comp hpair
  have hG := (continuous_snd.tendsto u.val.ofLp).comp hpair
  let U : ℕ → Lp ℝ 2 (gibbsLaw N β H) := fun n =>
    gibbsToL2 hN β H hH (f n) (smoothCore_contDiff (f n)).continuous
  let G : ℕ → PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)) := fun n =>
    normalizedRotationGradientL2 hN β H hH (f n) ((smoothCore_contDiff (f n)).of_le (by simp))
  change Tendsto U atTop (𝓝 u.val.fst) at hU
  change Tendsto G atTop (𝓝 u.val.snd) at hG
  obtain ⟨ns,hns,hnsAE⟩ := (tendstoInMeasure_of_tendsto_Lp hU).exists_seq_tendsto_ae
  let ψ : ℕ → smoothCore N := fun n => ⟨Φ ∘ (f (ns n)),hΦ.comp (smoothCore_contDiff (f (ns n)))⟩
  have hvalue (n : ℕ) : gibbsToL2 hN β H hH (ψ n) (smoothCore_contDiff (ψ n)).continuous=
      hL.compLp hΦ0 (U (ns n)) := by
    apply Lp.ext
    filter_upwards [gibbsToL2_coe hN β H hH (ψ n) (smoothCore_contDiff (ψ n)).continuous,
      hL.coeFn_compLp hΦ0 (U (ns n)),
      gibbsToL2_coe hN β H hH (f (ns n)) (smoothCore_contDiff (f (ns n))).continuous]
        with x hx hc hf
    change U (ns n) x=(f (ns n) : Vector N → ℝ) x at hf
    rw [hx,hc,Function.comp_apply,hf]
    rfl
  have hV : Tendsto (fun n => gibbsToL2 hN β H hH (ψ n) (smoothCore_contDiff (ψ n)).continuous)
      atTop (𝓝 (hL.compLp hΦ0 u.val.fst)) := by
    have ht := (hL.continuous_compLp hΦ0).continuousAt.tendsto.comp (hU.comp hns.tendsto_atTop)
    exact ht.congr' (.of_forall (fun n => (hvalue n).symm))
  have hgrad (n : ℕ) : normalizedRotationGradientL2 hN β H hH (ψ n)
      ((smoothCore_contDiff (ψ n)).of_le (by simp))=
      scalarGradientMultiplier hN β H hH Φ hΦ1 K hK (U (ns n)) (G (ns n)) :=
    normalizedRotationGradientL2_scalar_comp hN β H hH Φ hΦ1 K hK (f (ns n))
      ((smoothCore_contDiff (f (ns n))).of_le (by simp))
  have hDG : Tendsto (fun n => scalarGradientMultiplier hN β H hH Φ hΦ1 K hK
      (U (ns n)) (G (ns n))) atTop
      (𝓝 (scalarGradientMultiplier hN β H hH Φ hΦ1 K hK u.val.fst u.val.snd)) := by
    apply (PiLp.continuous_toLp (p := 2)
      (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H))).continuousAt.tendsto.comp
    apply tendsto_pi_nhds.mpr
    intro ij
    apply multiplication_tendsto
      (fun n x => deriv Φ (U (ns n) x)) (fun x => deriv Φ (u.val.fst x))
      (fun n => (hΦ1.continuous_deriv_one).comp_aestronglyMeasurable (Lp.aestronglyMeasurable (U (ns n))))
      ((hΦ1.continuous_deriv_one).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u.val.fst)) K
      (fun n => .of_forall (fun x => hK _)) (.of_forall (fun x => hK _))
    · filter_upwards [hnsAE] with x hx
      exact hΦ1.continuous_deriv_one.continuousAt.tendsto.comp hx
    · exact ((PiLp.continuous_apply 2 _ ij).continuousAt.tendsto.comp hG).comp hns.tendsto_atTop
  let z := WithLp.toLp 2 (hL.compLp hΦ0 u.val.fst,
    scalarGradientMultiplier hN β H hH Φ hΦ1 K hK u.val.fst u.val.snd)
  have hz : z∈closure (Set.range (smoothGradientGraphLinear hN β H hH)) := by
    apply mem_closure_of_tendsto
      ((WithLp.homeomorphProd 2 _ _).symm.continuous.continuousAt.tendsto.comp
        (hV.prodMk_nhds (hDG.congr' (.of_forall (fun n => (hgrad n).symm)))))
    exact .of_forall (fun n => ⟨ψ n,rfl⟩)
  exact ⟨⟨z,hz⟩,rfl,rfl⟩

end SlowEquilibration.SphericalForm
