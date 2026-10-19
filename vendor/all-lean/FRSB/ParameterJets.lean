module
public import Paper.QuadraticImplicit
public import Paper.BCFTranslation
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

/-! Local parameter regularity for the genuine translation derivative hierarchy. -/
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace FRSB

theorem iteratedFDeriv_comp_linear_at
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : G →L[ℝ] E) (f : E → F) (x : G) (n : ℕ)
    (hf : ContDiffAt ℝ n f (L x)) :
    iteratedFDeriv ℝ n (f ∘ L) x =
      (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨u, hu, hxu, hfu⟩ := hf.contDiffOn' le_rfl (by simp)
  simp only [insert_eq_of_mem (mem_univ _), univ_inter] at hfu
  have hpre : IsOpen (L ⁻¹' u) := hu.preimage L.continuous
  have hcomp : ContDiffAt ℝ n (f ∘ L) x := hf.comp_continuousLinearMap L
  have h := L.iteratedFDerivWithin_comp_right hfu hu.uniqueDiffOn
    hpre.uniqueDiffOn hxu (le_refl (n : ℕ∞ω))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn hcomp hxu,
    iteratedFDerivWithin_eq_iteratedFDeriv hu.uniqueDiffOn hf hxu] at h
  exact h

theorem iteratedDeriv_affine_line
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (a v : E) (n : ℕ) (hf : ContDiffAt ℝ n f a) :
    iteratedDeriv n (fun t : ℝ => f (a + t • v)) 0 =
      iteratedFDeriv ℝ n f a (fun _ => v) := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ v
  have ht : ContDiffAt ℝ n (fun y : E => f (a + y)) (L 0) := by
    have hfa : ContDiffAt ℝ n f (a + (0 : E)) := by simpa using hf
    simpa only [map_zero, Function.comp_def] using
      hfa.comp (0 : E) (contDiffAt_const.add contDiffAt_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have h := iteratedFDeriv_comp_linear_at L (fun y : E => f (a + y)) 0 n ht
  change iteratedFDeriv ℝ n ((fun y : E => f (a + y)) ∘ L) 0 (fun _ => (1 : ℝ)) = _
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left]
  simp only [map_zero, add_zero, L, ContinuousLinearMap.toSpanSingleton_apply, one_smul]

theorem continuous_parameter_line_jets
    {P X : Type*} [TopologicalSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : P → X →L[ℝ] X →L[ℝ] X)
    (g : ℝ → X) (v : P × ℝ → X)
    (hB : Continuous B) (hv : Continuous v)
    (hg : ContDiff ℝ ∞ g)
    (hfix : ∀ p t, v (p, t) = g t + B p (v (p, t)) (v (p, t)))
    (hinv : ∀ p, Paper.quadraticLinearizationIsInvertible (B p) (v (p, 0)))
    (n : ℕ) : Continuous (fun p => iteratedDeriv n (fun t => v (p, t)) 0) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let A := (X →L[ℝ] X →L[ℝ] X) × ℝ
  let a : A := (B p₀, 0)
  let BF : A → X →L[ℝ] X →L[ℝ] X := Prod.fst
  let GF : A → X := fun q => g q.2
  have hbase : v (p₀, 0) = GF a + BF a (v (p₀, 0)) (v (p₀, 0)) := hfix p₀ 0
  obtain ⟨ψ, hψa, hψ, hunique⟩ := Paper.quadratic_local_solution_of_invertible
    BF GF a (v (p₀, 0)) contDiffAt_fst (hg.contDiffAt.comp a contDiffAt_snd)
      hbase (hinv p₀)
  have hpar : Continuous (fun q : P × ℝ => ((B q.1, q.2), v q)) :=
    ((hB.comp continuous_fst).prodMk continuous_snd).prodMk hv
  have hevent : ∀ᶠ q : P × ℝ in 𝓝 (p₀, 0), ψ (B q.1, q.2) = v q := by
    have hh := (hpar.continuousAt (x := (p₀, 0))).tendsto.eventually hunique
    filter_upwards [hh] with q hq
    exact hq.mp (hfix q.1 q.2)
  rw [nhds_prod_eq, eventually_prod_iff] at hevent
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := hevent
  let e : A := (0, 1)
  let J : A → X := fun q => iteratedFDeriv ℝ n ψ q (fun _ => e)
  have hJ : ContinuousAt J a := by
    have h := hψ.continuousAt_iteratedFDeriv (k := n) (by simp)
    exact (continuous_eval_const (fun _ : Fin n => e)).continuousAt.comp h
  have hparam : ContinuousAt (fun p => (B p, (0 : ℝ))) p₀ :=
    hB.continuousAt.prodMk continuousAt_const
  have hreg : ∀ᶠ p in 𝓝 p₀, ContDiffAt ℝ n ψ (B p, (0 : ℝ)) :=
    hparam.tendsto.eventually ((hψ.of_le (by simp : (n : ℕ∞ω) ≤ ∞)).eventually (by simp))
  have heq : (fun p => iteratedDeriv n (fun t => v (p, t)) 0) =ᶠ[𝓝 p₀]
      (fun p => J (B p, 0)) := by
    filter_upwards [hpa, hreg] with p hp hregp
    have hcurve : (fun t : ℝ => v (p, t)) =ᶠ[𝓝 0]
        (fun t : ℝ => ψ (B p, t)) := by
      filter_upwards [hpb] with t ht
      exact (hab hp ht).symm
    rw [hcurve.iteratedDeriv_eq n]
    have hline := iteratedDeriv_affine_line ψ (B p, (0 : ℝ)) e n hregp
    have harg (t : ℝ) : (B p, (0 : ℝ)) + t • e = (B p, t) := by
      apply Prod.ext
      · change B p + t • (0 : X →L[ℝ] X →L[ℝ] X) = B p
        ext x y
        simp
      · change (0 : ℝ) + t • (1 : ℝ) = t
        simp
    simpa only [harg, J] using hline
  have hcom : ContinuousAt (fun p : P => J (B p, (0 : ℝ))) p₀ := by
    exact ContinuousAt.comp (f := fun p : P => (B p, (0 : ℝ))) hJ hparam
  exact hcom.congr_of_eventuallyEq heq

end FRSB
