import ComputableAnalysis.ComplexAnalysis.Polygon

/-!
# Cauchy cancellation with an arbitrary effective first-order modulus

A mesh depth and evaluation precision are computed separately. On each
leaf triangle, the error is at most `epsilon * 2^(-depth)`. The first-order
error, perimeter, and number of cells scale respectively by `1/2`, `1/2`,
and `4`, so their product is independent of depth. Taking epsilon to zero
proves an exact contour identity. A Lipschitz derivative is not required.
-/
namespace ComputableAnalysis.ComplexAnalysis
open QComplex

/-- Local first-order models on every triangle of a finite refinement. -/
def Triangle.FirstOrderModels (t : Triangle) (f : QComplex → QComplex)
    (epsilon : Rat) : Nat → Prop
  | 0 => t.Model f epsilon
  | n+1 => ∀ i : Fin 4, (t.child i).FirstOrderModels f (epsilon/2) n

theorem Triangle.first_order_bound (t : Triangle) (f : QComplex → QComplex)
    (epsilon : Rat) (n : Nat) (h : t.FirstOrderModels f epsilon n) :
    normBound (t.sum f n) ≤ epsilon*t.perimeter := by
  induction n generalizing t epsilon with
  | zero => exact t.model_bound f epsilon h
  | succ n ih =>
    have h0 := ih (t.child 0) (epsilon/2) (h 0)
    have h1 := ih (t.child 1) (epsilon/2) (h 1)
    have h2 := ih (t.child 2) (epsilon/2) (h 2)
    have h3 := ih (t.child 3) (epsilon/2) (h 3)
    rw [Triangle.perimeter_child] at h0 h1 h2 h3
    rw [Triangle.subdivide]
    have ha := normBound_add_le ((t.child 2).sum f n) ((t.child 3).sum f n)
    have hb := normBound_add_le ((t.child 1).sum f n)
      (add ((t.child 2).sum f n) ((t.child 3).sum f n))
    have hc := normBound_add_le ((t.child 0).sum f n)
      (add ((t.child 1).sum f n) (add ((t.child 2).sum f n) ((t.child 3).sum f n)))
    grind only

/-- Executable analytic data: meshes may refine arbitrarily slowly or
quickly; the error schedule controls both function evaluation and the local
first-order remainder. No assertion about contour integrals is assumed. -/
structure CauchyData (t : Triangle) (F : QComplex → ComplexRaw) where
  depth : Nat → Nat
  precision : Nat → QComplex → Nat
  depth_refines : ∀ n, n ≤ depth n
  bound : Rat
  bound_nonneg : 0 ≤ bound
  values_valid : ∀ z, (F z).Valid
  sample_accuracy : ∀ n z,
    ((F z).compute (precision n z)).width ≤ CertifiedComplexApproximation.rate 1 n ∧
    ((F z).compute (precision n z)).height ≤ CertifiedComplexApproximation.rate 1 n
  models : ∀ n, t.FirstOrderModels (sample F precision n)
    (CertifiedComplexApproximation.rate bound n) (depth n)

def CauchyData.contour {t : Triangle} {F : QComplex → ComplexRaw}
    (c : CauchyData t F) : ComplexRaw :=
  CertifiedComplexApproximation.raw (fun n => t.sum (sample F c.precision n) (c.depth n))
    (c.bound*t.perimeter)

theorem CauchyData.sum_bound {t : Triangle} {F : QComplex → ComplexRaw}
    (c : CauchyData t F) (n : Nat) :
    normBound (t.sum (sample F c.precision n) (c.depth n)) ≤
      CertifiedComplexApproximation.rate (c.bound*t.perimeter) n := by
  have h := t.first_order_bound (sample F c.precision n) _ (c.depth n) (c.models n)
  unfold CertifiedComplexApproximation.rate at *
  grind only [Rat.div_def]

private theorem CauchyData.zero_enclosed {t : Triangle} {F : QComplex → ComplexRaw}
    (c : CauchyData t F) (n : Nat) :
    ((ComplexRaw.ofQComplex zero).compute n).NestedIn
      (QBox.expand (QBox.point (t.sum (sample F c.precision n) (c.depth n)))
        (CertifiedComplexApproximation.rate (c.bound*t.perimeter) n)) := by
  have h := ComplexExponentialApproximation.point_add_error_nested_expand
    (t.sum (sample F c.precision n) (c.depth n))
    (neg (t.sum (sample F c.precision n) (c.depth n)))
    (by rw [normBound_neg]; exact c.sum_bound n)
  rw [add_neg_self_cert] at h
  exact h

theorem CauchyData.contour_valid {t : Triangle} {F : QComplex → ComplexRaw}
    (c : CauchyData t F) : c.contour.Valid :=
  CertifiedComplexApproximation.valid (Rat.mul_nonneg c.bound_nonneg t.perimeter_nonneg)
    (ComplexRaw.ofQComplex_valid zero) c.zero_enclosed

/-- Exact Cauchy theorem for an effective uniform first-order modulus. -/
theorem CauchyData.cauchy {t : Triangle} {F : QComplex → ComplexRaw}
    (c : CauchyData t F) : c.contour.Equiv (ComplexRaw.ofQComplex zero) :=
  CertifiedComplexApproximation.equiv_anchor (Rat.mul_nonneg c.bound_nonneg t.perimeter_nonneg)
    (ComplexRaw.ofQComplex_valid zero) c.zero_enclosed

/-- A common represented value, independently of mesh and sample choices. -/
theorem CauchyData.independent {t : Triangle} {F G : QComplex → ComplexRaw}
    (c : CauchyData t F) (d : CauchyData t G) : c.contour.Equiv d.contour :=
  ComplexRaw.equiv_trans c.contour_valid (ComplexRaw.ofQComplex_valid zero)
    d.contour_valid c.cauchy (ComplexRaw.equiv_symm d.cauchy)

/-- Quantitative quadratic models instantiate the general first-order API. -/
theorem Triangle.models_first_order (t : Triangle) (f : QComplex → QComplex)
    (E : Rat) (n : Nat) (h : t.Models f E n) :
    t.FirstOrderModels f (E*((1:Rat)/2)^n) n := by
  induction n generalizing t E with
  | zero =>
    change t.Model f E at h
    change t.Model f (E * (1/2)^0)
    simpa only [Rat.pow_zero, Rat.mul_one] using h
  | succ n ih =>
    intro i
    have hc := ih (t.child i) (E/4) (h i)
    have he : E*(1/2)^(n+1)/2 = E/4*(1/2)^n := by rw [Rat.pow_succ]; grind only
    rw [he]
    exact hc

theorem Triangle.Model.mono {t : Triangle} {f : QComplex → QComplex} {a b : Rat}
    (h : t.Model f a) (hab : a ≤ b) : t.Model f b := by
  obtain ⟨u,v,model⟩ := h
  exact ⟨u,v,fun z hz => Rat.le_trans (model z hz) hab⟩

theorem Triangle.FirstOrderModels.mono {t : Triangle} {f : QComplex → QComplex} {a b : Rat}
    (n : Nat) (h : t.FirstOrderModels f a n) (hab : a ≤ b) : t.FirstOrderModels f b n := by
  induction n generalizing t a b with
  | zero => exact Triangle.Model.mono h hab
  | succ n ih =>
    intro i
    apply ih (h i)
    grind only

def Triangle.Certificate.toCauchyData {t : Triangle} {F : QComplex → ComplexRaw}
    (c : t.Certificate F) : CauchyData t F where
  depth := fun n => n
  precision := c.precision
  depth_refines := fun _ => Nat.le_refl _
  bound := c.error
  bound_nonneg := c.error_nonneg
  values_valid := c.values_valid
  sample_accuracy := c.sample_accuracy
  models := by
    intro n
    apply Triangle.FirstOrderModels.mono n (t.models_first_order _ _ n (c.local_models n))
    have h := Rat.mul_le_mul_of_nonneg_left (Series.half_pow_le_one_div_succ n) c.error_nonneg
    unfold CertifiedComplexApproximation.rate
    grind only [Rat.div_def]


/-- Oriented triangle chains describe polygonal regions, including regions
with holes. Opposite interior edges cancel by `edgeSum_reverse`; no model is
required in an omitted triangle or inside a hole. -/
def chainSum (triangles : List Triangle) (f : QComplex → QComplex) (n : Nat) : QComplex :=
  triangles.foldr (fun t rest => add (t.sum f n) rest) zero

def chainPerimeter (triangles : List Triangle) : Rat :=
  triangles.foldr (fun t rest => t.perimeter + rest) 0

theorem chainPerimeter_nonneg (triangles : List Triangle) : 0 ≤ chainPerimeter triangles := by
  induction triangles with
  | nil => exact Rat.le_refl
  | cons t ts ih => exact Rat.add_nonneg t.perimeter_nonneg ih

theorem chain_bound (triangles : List Triangle) (f : QComplex → QComplex)
    (epsilon : Rat) (n : Nat)
    (h : ∀ t ∈ triangles, t.FirstOrderModels f epsilon n) :
    normBound (chainSum triangles f n) ≤ epsilon * chainPerimeter triangles := by
  induction triangles with
  | nil => simp [chainSum,chainPerimeter,normBound_zero]
  | cons t ts ih =>
    have ht := t.first_order_bound f epsilon n (h t (by simp))
    have hr := ih (by intro u hu; exact h u (by simp [hu]))
    have ha := normBound_add_le (t.sum f n) (chainSum ts f n)
    simp only [chainSum,chainPerimeter,List.foldr_cons] at *
    grind only

structure ChainData (triangles : List Triangle) (F : QComplex → ComplexRaw) where
  depth : Nat → Nat
  depth_refines : ∀ n, n ≤ depth n
  precision : Nat → QComplex → Nat
  bound : Rat
  bound_nonneg : 0 ≤ bound
  values_valid : ∀ z, (F z).Valid
  sample_accuracy : ∀ n z,
    ((F z).compute (precision n z)).width ≤ CertifiedComplexApproximation.rate 1 n ∧
    ((F z).compute (precision n z)).height ≤ CertifiedComplexApproximation.rate 1 n
  models : ∀ n t, t ∈ triangles → t.FirstOrderModels (sample F precision n)
    (CertifiedComplexApproximation.rate bound n) (depth n)

def ChainData.contour {ts : List Triangle} {F : QComplex → ComplexRaw}
    (c : ChainData ts F) : ComplexRaw :=
  CertifiedComplexApproximation.raw (fun n => chainSum ts (sample F c.precision n) (c.depth n))
    (c.bound*chainPerimeter ts)

private theorem ChainData.encloses_zero {ts : List Triangle} {F : QComplex → ComplexRaw}
    (c : ChainData ts F) (n : Nat) :
    ((ComplexRaw.ofQComplex zero).compute n).NestedIn
      (QBox.expand (QBox.point (chainSum ts (sample F c.precision n) (c.depth n)))
        (CertifiedComplexApproximation.rate (c.bound*chainPerimeter ts) n)) := by
  have hb := chain_bound ts (sample F c.precision n) _ (c.depth n) (c.models n)
  have he : normBound (neg (chainSum ts (sample F c.precision n) (c.depth n))) ≤
      CertifiedComplexApproximation.rate (c.bound*chainPerimeter ts) n := by
    rw [normBound_neg]
    unfold CertifiedComplexApproximation.rate at *
    grind only [Rat.div_def]
  have h := ComplexExponentialApproximation.point_add_error_nested_expand
    (chainSum ts (sample F c.precision n) (c.depth n))
    (neg (chainSum ts (sample F c.precision n) (c.depth n))) he
  rw [add_neg_self_cert] at h
  exact h

theorem ChainData.contour_valid {ts : List Triangle} {F : QComplex → ComplexRaw}
    (c : ChainData ts F) : c.contour.Valid :=
  CertifiedComplexApproximation.valid (Rat.mul_nonneg c.bound_nonneg (chainPerimeter_nonneg ts))
    (ComplexRaw.ofQComplex_valid zero) c.encloses_zero

theorem ChainData.cauchy {ts : List Triangle} {F : QComplex → ComplexRaw}
    (c : ChainData ts F) : c.contour.Equiv (ComplexRaw.ofQComplex zero) :=
  CertifiedComplexApproximation.equiv_anchor (Rat.mul_nonneg c.bound_nonneg (chainPerimeter_nonneg ts))
    (ComplexRaw.ofQComplex_valid zero) c.encloses_zero

end ComputableAnalysis.ComplexAnalysis
