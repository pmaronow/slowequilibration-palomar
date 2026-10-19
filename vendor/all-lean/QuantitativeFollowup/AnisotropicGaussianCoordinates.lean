module
public import QuantitativeFollowup.AnisotropicFiniteJointDensity
public import QuantitativePaper.VectorHistoryLinear
public import FourPapersCommon.FiniteGaussianBlockLaw
public import QuantitativePaper.VectorSharpMassBounds

@[expose] public section

/-! An honest independent Gaussian coordinate realization of every
anisotropic field increment and coupling, retaining the terminal spin. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
variable {n k : ℕ}

abbrev AnisotropicGaussianIndex (n k : ℕ) := AnisotropicCouplingIndex n⊕(Fin (k+2)×Fin n)
abbrev AnisotropicGaussianSpace (n k : ℕ) := EuclideanSpace ℝ (AnisotropicGaussianIndex n k)
abbrev AnisotropicGaussianCoordinates (n k : ℕ) := AnisotropicDisorder n×(Fin (k+2)→Field n)

def anisotropicGaussianCoordinateLaw (n k : ℕ) : Measure (AnisotropicGaussianCoordinates n k) :=
  (anisotropicDisorderLaw n).prod (Measure.pi (fun _ : Fin (k+2) => stdGaussian (Field n)))

instance anisotropicGaussianCoordinateLaw_probability (n k : ℕ) :
    IsProbabilityMeasure (anisotropicGaussianCoordinateLaw n k) := by
  unfold anisotropicGaussianCoordinateLaw
  infer_instance

def anisotropicCoordinateUpdate (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : ℕ)
    (P : AnisotropicParameter n) (z : Field n) : AnisotropicParameter n :=
  P+anisotropicSchemeInput D s (k+1-i) z

theorem measurable_anisotropicCoordinateUpdate (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) :
    Measurable (Function.uncurry (anisotropicCoordinateUpdate D s i)) := by
  unfold anisotropicCoordinateUpdate
  fun_prop

def anisotropicCoordinateHistory (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (p : AnisotropicGaussianCoordinates n k) : FiniteHistory (AnisotropicParameter n) (k+2) :=
  independentHistory (anisotropicCoordinateUpdate D s) (k+2) (anisotropicDisorderInjection n p.1,p.2)

theorem measurable_anisotropicCoordinateHistory (D : AnisotropicSpinModel n)
    (s : RSBScheme k) : Measurable (anisotropicCoordinateHistory D s) :=
  (measurable_independentHistory _ (measurable_anisotropicCoordinateUpdate D s) _).comp
    (((anisotropicDisorderInjection n).continuous.measurable.comp measurable_fst).prodMk measurable_snd)

theorem anisotropicCoordinateHistory_map (D : AnisotropicSpinModel n) (s : RSBScheme k) :
    (anisotropicGaussianCoordinateLaw n k).map (anisotropicCoordinateHistory D s) =
      anisotropicFiniteBaseHistoryLaw D s := by
  have hh := independentHistory_law (anisotropicFiniteBaseInitialLaw n) (stdGaussian (Field n))
    (anisotropicCoordinateUpdate D s) (measurable_anisotropicCoordinateUpdate D s)
    (anisotropicFiniteBaseTransition D s) (fun _ => inferInstance)
    (fun i P => finiteStateGaussianRawKernel_apply _ P) (k+2)
  have he : (anisotropicFiniteBaseInitialLaw n).prod (Measure.pi (fun _ : Fin (k+2) => stdGaussian (Field n))) =
      (anisotropicGaussianCoordinateLaw n k).map (fun p => (anisotropicDisorderInjection n p.1,p.2)) := by
    unfold anisotropicFiniteBaseInitialLaw anisotropicGaussianCoordinateLaw
    conv_lhs => rhs;rw [←Measure.map_id (μ := Measure.pi (fun _ : Fin (k+2) => stdGaussian (Field n)))]
    rw [Measure.map_prod_map _ _ (anisotropicDisorderInjection n).continuous.measurable measurable_id]
    rfl
  have hm : Measurable (fun p : AnisotropicGaussianCoordinates n k =>
      (anisotropicDisorderInjection n p.1,p.2)) := by fun_prop
  rw [he,Measure.map_map (measurable_independentHistory _ (measurable_anisotropicCoordinateUpdate D s) _) hm] at hh
  exact hh

def anisotropicRawGaussianCoordinates (n k : ℕ) (z : AnisotropicGaussianIndex n k→ℝ) :
    AnisotropicGaussianCoordinates n k :=
  (WithLp.toLp 2 (fun i => z (.inl i)),flatFieldCoordinates n k (fun i => z (.inr i)))

theorem measurable_anisotropicRawGaussianCoordinates (n k : ℕ) :
    Measurable (anisotropicRawGaussianCoordinates n k) :=
  ((PiLp.continuous_toLp 2 (fun _ : AnisotropicCouplingIndex n => ℝ)).measurable.comp
    (Measurable.of_eval fun i => measurable_pi_apply _)).prodMk
    ((measurable_flatFieldCoordinates n k).comp (Measurable.of_eval fun i => measurable_pi_apply _))

theorem anisotropicRawGaussianCoordinates_map (n k : ℕ) :
    (Measure.pi (fun _ : AnisotropicGaussianIndex n k => gaussianReal 0 1)).map
      (anisotropicRawGaussianCoordinates n k) = anisotropicGaussianCoordinateLaw n k := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : AnisotropicGaussianIndex n k => ℝ)
  have he := (measurePreserving_sumPiEquivProdPi
    (fun _ : AnisotropicGaussianIndex n k => gaussianReal 0 1)).map_eq
  have hf : anisotropicRawGaussianCoordinates n k =
      (Prod.map (WithLp.toLp 2) (flatFieldCoordinates n k)) ∘ e := rfl
  rw [hf,←Measure.map_map ((by fun_prop : Measurable (WithLp.toLp 2 :
    (AnisotropicCouplingIndex n→ℝ)→AnisotropicDisorder n)).prodMap
      (measurable_flatFieldCoordinates n k)) e.measurable,he,
    ←Measure.map_prod_map _ _ (by fun_prop) (measurable_flatFieldCoordinates n k),
    map_pi_eq_stdGaussian,flatFieldCoordinates_map,fieldGaussian_eq_stdGaussian]
  rfl

def anisotropicEuclideanCoordinates (n k : ℕ) (z : AnisotropicGaussianSpace n k) :
    AnisotropicGaussianCoordinates n k := anisotropicRawGaussianCoordinates n k (WithLp.ofLp z)

theorem measurable_anisotropicEuclideanCoordinates (n k : ℕ) :
    Measurable (anisotropicEuclideanCoordinates n k) :=
  (measurable_anisotropicRawGaussianCoordinates n k).comp (by fun_prop)

theorem anisotropicEuclideanCoordinates_map (n k : ℕ) :
    (stdGaussian (AnisotropicGaussianSpace n k)).map (anisotropicEuclideanCoordinates n k) =
      anisotropicGaussianCoordinateLaw n k := by
  rw [←map_pi_eq_stdGaussian,Measure.map_map (measurable_anisotropicEuclideanCoordinates n k) (by fun_prop)]
  exact anisotropicRawGaussianCoordinates_map n k

def anisotropicEuclideanJointMap (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (p : AnisotropicGaussianSpace n k×Configuration n) :
    FiniteHistory (AnisotropicParameter n) (k+2)×Configuration n :=
  (anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k p.1),p.2)

theorem measurable_anisotropicEuclideanJointMap (D : AnisotropicSpinModel n) (s : RSBScheme k) :
    Measurable (anisotropicEuclideanJointMap D s) :=
  ((measurable_anisotropicCoordinateHistory D s).comp (measurable_anisotropicEuclideanCoordinates n k)).prodMap measurable_id

def anisotropicEuclideanDensity (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (p : AnisotropicGaussianSpace n k×Configuration n) : ℝ≥0∞ :=
  anisotropicFiniteJointDensity D s a (anisotropicEuclideanJointMap D s p)

theorem measurable_anisotropicEuclideanDensity (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : Measurable (anisotropicEuclideanDensity D s a) :=
  (measurable_anisotropicFiniteJointDensity D s a).comp (measurable_anisotropicEuclideanJointMap D s)

def anisotropicEuclideanJointLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    Measure (AnisotropicGaussianSpace n k×Configuration n) :=
  ((stdGaussian (AnisotropicGaussianSpace n k)).prod (Measure.count : Measure (Configuration n))).withDensity
    (anisotropicEuclideanDensity D s a)

theorem anisotropicEuclideanJointLaw_map (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    (anisotropicEuclideanJointLaw D s a).map (anisotropicEuclideanJointMap D s) =
      anisotropicFiniteJointLaw D s a := by
  unfold anisotropicEuclideanJointLaw anisotropicEuclideanDensity
  rw [map_withDensity_pullback _ _
    (measurable_anisotropicEuclideanJointMap D s) _ (measurable_anisotropicFiniteJointDensity D s a)]
  change (((stdGaussian (AnisotropicGaussianSpace n k)).prod Measure.count).map
    (Prod.map (anisotropicCoordinateHistory D s ∘ anisotropicEuclideanCoordinates n k) id)).withDensity _ = _
  rw [←Measure.map_prod_map _ _ ((measurable_anisotropicCoordinateHistory D s).comp
      (measurable_anisotropicEuclideanCoordinates n k)) measurable_id,
    ←Measure.map_map (measurable_anisotropicCoordinateHistory D s) (measurable_anisotropicEuclideanCoordinates n k),
    anisotropicEuclideanCoordinates_map,anisotropicCoordinateHistory_map,Measure.map_id,
    anisotropicFiniteJointLaw_eq_withDensity]

instance anisotropicEuclideanJointLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : IsProbabilityMeasure (anisotropicEuclideanJointLaw D s a) := by
  constructor
  have hh := congrArg (fun P : Measure (FiniteHistory (AnisotropicParameter n) (k+2)×Configuration n) => P univ)
    (anisotropicEuclideanJointLaw_map D s a)
  rw [Measure.map_apply (measurable_anisotropicEuclideanJointMap D s) MeasurableSet.univ,preimage_univ] at hh
  exact hh.trans (measure_univ (μ := anisotropicFiniteJointLaw D s a))

end QuantitativeFollowup
