import ComputableAnalysis.ComplexPowerCalculus
import ComputableAnalysis.CertifiedComplexApproximation
import ComputableAnalysis.Series

/-!
# Polygonal quadrature and finite Cauchy cancellation

The contour evaluator reads actual midpoint samples. Four-way subdivision
cancels interior edges exactly. No contour integral or vanishing conclusion
is a field of the local analytic certificate.
-/
namespace ComputableAnalysis.ComplexAnalysis
open QComplex

/-- Rational midpoint, shared by the two orientations of an edge. -/
def midpoint (a b : QComplex) : QComplex := scaleRat (1/2) (add a b)

theorem midpoint_comm (a b : QComplex) : midpoint a b = midpoint b a := by
  simp only [midpoint, scaleRat, add, QComplex.mk.injEq]
  constructor <;> grind

/-- Oriented, dyadically refined midpoint quadrature along one segment. -/
def edgeSum (f : QComplex → QComplex) (a b : QComplex) : Nat → QComplex
  | 0 => mul (f (midpoint a b)) (sub b a)
  | n+1 => add (edgeSum f a (midpoint a b) n) (edgeSum f (midpoint a b) b n)

theorem edgeSum_reverse (f : QComplex → QComplex) (a b : QComplex) (n : Nat) :
    edgeSum f b a n = neg (edgeSum f a b n) := by
  induction n generalizing a b with
  | zero =>
    simp only [edgeSum, midpoint_comm b a, mul, sub, add, neg, QComplex.mk.injEq]
    constructor <;> grind
  | succ n ih =>
    simp only [edgeSum, midpoint_comm b a, ih (midpoint a b) b, ih a (midpoint a b),
      add, neg, QComplex.mk.injEq]
    constructor <;> grind

structure Triangle where
  a : QComplex
  b : QComplex
  c : QComplex
 deriving Repr

def Triangle.child (t : Triangle) : Fin 4 → Triangle
  | ⟨0, _⟩ => ⟨t.a, midpoint t.a t.b, midpoint t.c t.a⟩
  | ⟨1, _⟩ => ⟨midpoint t.a t.b, t.b, midpoint t.b t.c⟩
  | ⟨2, _⟩ => ⟨midpoint t.c t.a, midpoint t.b t.c, t.c⟩
  | ⟨3, _⟩ => ⟨midpoint t.a t.b, midpoint t.b t.c, midpoint t.c t.a⟩

def Triangle.sum (t : Triangle) (f : QComplex → QComplex) (n : Nat) : QComplex :=
  add (edgeSum f t.a t.b n) (add (edgeSum f t.b t.c n) (edgeSum f t.c t.a n))

/-- The finite Stokes identity: every internal edge occurs twice with
opposite orientation. This holds for every function, holomorphic or not. -/
theorem Triangle.subdivide (t : Triangle) (f : QComplex → QComplex) (n : Nat) :
    t.sum f (n+1) = add ((t.child 0).sum f n)
      (add ((t.child 1).sum f n) (add ((t.child 2).sum f n) ((t.child 3).sum f n))) := by
  simp only [Triangle.sum, Triangle.child, edgeSum]
  rw [edgeSum_reverse f (midpoint t.a t.b) (midpoint t.b t.c) n,
      edgeSum_reverse f (midpoint t.b t.c) (midpoint t.c t.a) n,
      edgeSum_reverse f (midpoint t.c t.a) (midpoint t.a t.b) n]
  simp only [add, neg, QComplex.mk.injEq]
  constructor <;> grind

def affine (u v z : QComplex) : QComplex := add u (mul v z)

/-- Midpoint quadrature integrates an affine holomorphic function exactly. -/
theorem Triangle.affine_zero (t : Triangle) (u v : QComplex) :
    t.sum (affine u v) 0 = zero := by
  simp only [Triangle.sum, edgeSum, affine, midpoint, scaleRat, mul, sub, add, neg,
    zero, QComplex.mk.injEq]
  constructor <;> grind

theorem Triangle.sum_sub (t : Triangle) (f g : QComplex → QComplex) :
    t.sum (fun z => sub (f z) (g z)) 0 = sub (t.sum f 0) (t.sum g 0) := by
  simp only [Triangle.sum, edgeSum, mul, sub, add, neg, QComplex.mk.injEq]
  constructor <;> grind

/-- Rational barycentric points of the filled triangle. -/
def Triangle.Contains (t : Triangle) (z : QComplex) : Prop :=
  ∃ u v : Rat, 0 ≤ u ∧ 0 ≤ v ∧ u+v ≤ 1 ∧
    z = add t.a (add (scaleRat u (sub t.b t.a)) (scaleRat v (sub t.c t.a)))

theorem Triangle.midpoints_inside (t : Triangle) :
    t.Contains (midpoint t.a t.b) ∧ t.Contains (midpoint t.b t.c) ∧
      t.Contains (midpoint t.c t.a) := by
  constructor
  · refine ⟨1/2,0,by grind,by grind,by grind,?_⟩
    simp only [midpoint,scaleRat,sub,add,neg,QComplex.mk.injEq]; constructor <;> grind
  constructor
  · refine ⟨1/2,1/2,by grind,by grind,by grind,?_⟩
    simp only [midpoint,scaleRat,sub,add,neg,QComplex.mk.injEq]; constructor <;> grind
  · refine ⟨0,1/2,by grind,by grind,by grind,?_⟩
    simp only [midpoint,scaleRat,sub,add,neg,QComplex.mk.injEq]; constructor <;> grind

/-- A local complex-affine approximation throughout the filled triangle,
not merely at quadrature nodes. The algorithm does not read its coefficients. -/
def Triangle.Model (t : Triangle) (f : QComplex → QComplex) (E : Rat) : Prop :=
  ∃ u v, ∀ z, t.Contains z → normBound (sub (f z) (affine u v z)) ≤ E

def Triangle.perimeter (t : Triangle) : Rat :=
  normBound (sub t.b t.a) + normBound (sub t.c t.b) + normBound (sub t.a t.c)

theorem Triangle.model_bound (t : Triangle) (f : QComplex → QComplex) (E : Rat)
    (h : t.Model f E) : normBound (t.sum f 0) ≤ E * t.perimeter := by
  obtain ⟨u,v,model⟩ := h
  have h1 := model _ t.midpoints_inside.1
  have h2 := model _ t.midpoints_inside.2.1
  have h3 := model _ t.midpoints_inside.2.2
  have he : t.sum f 0 = t.sum (fun z => sub (f z) (affine u v z)) 0 := by
    rw [Triangle.sum_sub, Triangle.affine_zero]
    cases hq : t.sum f 0
    simp only [sub, add, neg, zero, QComplex.mk.injEq]
    constructor <;> grind
  rw [he]
  have e1 := Rat.le_trans (normBound_mul_le _ _)
    (Rat.mul_le_mul_of_nonneg_right h1 (normBound_nonneg (sub t.b t.a)))
  have e2 := Rat.le_trans (normBound_mul_le _ _)
    (Rat.mul_le_mul_of_nonneg_right h2 (normBound_nonneg (sub t.c t.b)))
  have e3 := Rat.le_trans (normBound_mul_le _ _)
    (Rat.mul_le_mul_of_nonneg_right h3 (normBound_nonneg (sub t.a t.c)))
  have h23 := normBound_add_le
    (mul (sub (f (midpoint t.b t.c)) (affine u v (midpoint t.b t.c))) (sub t.c t.b))
    (mul (sub (f (midpoint t.c t.a)) (affine u v (midpoint t.c t.a))) (sub t.a t.c))
  have h123 := normBound_add_le
    (mul (sub (f (midpoint t.a t.b)) (affine u v (midpoint t.a t.b))) (sub t.b t.a))
    (add (mul (sub (f (midpoint t.b t.c)) (affine u v (midpoint t.b t.c))) (sub t.c t.b))
      (mul (sub (f (midpoint t.c t.a)) (affine u v (midpoint t.c t.a))) (sub t.a t.c)))
  change normBound (add _ (add _ _)) ≤ _
  simp only [edgeSum, Triangle.perimeter]
  grind only


private theorem mid_sub_left (a b : QComplex) :
    sub (midpoint a b) a = scaleRat (1/2) (sub b a) := by
  simp only [midpoint, sub, add, neg, scaleRat, QComplex.mk.injEq]
  constructor <;> grind

private theorem mid_sub_mid (a b c : QComplex) :
    sub (midpoint a b) (midpoint a c) = scaleRat (1/2) (sub b c) := by
  simp only [midpoint, sub, add, neg, scaleRat, QComplex.mk.injEq]
  constructor <;> grind

private theorem norm_sub_swap (a b : QComplex) : normBound (sub a b) = normBound (sub b a) := by
  have he : sub a b = neg (sub b a) := by
    simp only [sub, add, neg, QComplex.mk.injEq]
    constructor <;> grind
  rw [he, normBound_neg]

private theorem norm_mid_left (a b : QComplex) :
    normBound (sub (midpoint a b) a) = (1/2) * normBound (sub b a) := by
  rw [mid_sub_left, normBound_scaleRat, qabs_eq_self_of_nonneg (by grind : (0:Rat) ≤ 1/2)]

private theorem norm_mid_mid (a b c : QComplex) :
    normBound (sub (midpoint a b) (midpoint a c)) = (1/2) * normBound (sub b c) := by
  rw [mid_sub_mid, normBound_scaleRat, qabs_eq_self_of_nonneg (by grind : (0:Rat) ≤ 1/2)]

theorem Triangle.perimeter_child (t : Triangle) (i : Fin 4) :
    (t.child i).perimeter = t.perimeter / 2 := by
  obtain ⟨i,hi⟩ := i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases h with h|h|h|h <;> subst i <;>
    simp only [Triangle.child, Triangle.perimeter]
  · rw [norm_mid_left, midpoint_comm t.c t.a, norm_mid_mid,
      norm_sub_swap t.a (midpoint t.a t.c), norm_mid_left, norm_sub_swap t.c t.b,
      norm_sub_swap t.c t.a]
    grind
  · rw [norm_sub_swap t.b (midpoint t.a t.b), midpoint_comm t.a t.b, norm_mid_left,
      norm_mid_left, norm_sub_swap (midpoint t.b t.a) (midpoint t.b t.c), norm_mid_mid,
      norm_sub_swap t.a t.b, norm_sub_swap t.c t.a]
    grind
  · rw [midpoint_comm t.b t.c, norm_mid_mid, norm_sub_swap t.c (midpoint t.c t.b),
      norm_mid_left, norm_mid_left, norm_sub_swap t.b t.c, norm_sub_swap t.a t.c]
    grind
  · rw [midpoint_comm t.a t.b, norm_mid_mid, midpoint_comm t.b t.c,
      norm_mid_mid, midpoint_comm t.c t.a, midpoint_comm t.b t.a, norm_mid_mid,
      norm_sub_swap t.c t.a, norm_sub_swap t.a t.b, norm_sub_swap t.b t.c]
    grind

/-- Each refinement asks only for local affine remainders. The permitted
error decreases quadratically with the diameter. -/
def Triangle.Models (t : Triangle) (f : QComplex → QComplex) (E : Rat) : Nat → Prop
  | 0 => t.Model f E
  | n+1 => ∀ i : Fin 4, (t.child i).Models f (E/4) n

/-- Cauchy's estimate from finite subdivision, for any complex function
with the indicated local affine approximations. -/
theorem Triangle.cauchy_bound (t : Triangle) (f : QComplex → QComplex) (E : Rat)
    (n : Nat) (h : t.Models f E n) :
    normBound (t.sum f n) ≤ E * t.perimeter * ((1:Rat)/2)^n := by
  induction n generalizing t E with
  | zero => simpa using t.model_bound f E h
  | succ n ih =>
    have h0 := ih (t.child 0) (E/4) (h 0)
    have h1 := ih (t.child 1) (E/4) (h 1)
    have h2 := ih (t.child 2) (E/4) (h 2)
    have h3 := ih (t.child 3) (E/4) (h 3)
    rw [Triangle.perimeter_child] at h0 h1 h2 h3
    rw [Triangle.subdivide]
    have ha := normBound_add_le ((t.child 2).sum f n) ((t.child 3).sum f n)
    have hb := normBound_add_le ((t.child 1).sum f n)
      (add ((t.child 2).sum f n) ((t.child 3).sum f n))
    have hc := normBound_add_le ((t.child 0).sum f n)
      (add ((t.child 1).sum f n) (add ((t.child 2).sum f n) ((t.child 3).sum f n)))
    rw [Rat.pow_succ]
    grind only


theorem Triangle.perimeter_nonneg (t : Triangle) : 0 ≤ t.perimeter := by
  have h1 := normBound_nonneg (sub t.b t.a)
  have h2 := normBound_nonneg (sub t.c t.b)
  have h3 := normBound_nonneg (sub t.a t.c)
  unfold Triangle.perimeter
  grind only

/-- A computable contour samples a represented function at rational points.
The precision selector is executable data, not a choice extracted from Prop. -/
def sample (F : QComplex → ComplexRaw) (precision : Nat → QComplex → Nat)
    (n : Nat) (z : QComplex) : QComplex := ((F z).compute (precision n z)).center

def Triangle.contour (t : Triangle) (F : QComplex → ComplexRaw)
    (precision : Nat → QComplex → Nat) (E : Rat) : ComplexRaw :=
  CertifiedComplexApproximation.raw (fun n => t.sum (sample F precision n) n) (E*t.perimeter)

/-- The analytic hypothesis concerns local affine remainders of the actual
samples, not contour sums. Irrational function values are permitted. -/
structure Triangle.Certificate (t : Triangle) (F : QComplex → ComplexRaw) where
  precision : Nat → QComplex → Nat
  error : Rat
  error_nonneg : 0 ≤ error
  values_valid : ∀ z, (F z).Valid
  sample_accuracy : ∀ n z,
    ((F z).compute (precision n z)).width ≤ CertifiedComplexApproximation.rate 1 n ∧
    ((F z).compute (precision n z)).height ≤ CertifiedComplexApproximation.rate 1 n
  local_models : ∀ n, t.Models (sample F precision n) error n

private theorem Triangle.encloses_zero (t : Triangle) (F : QComplex → ComplexRaw)
    (c : t.Certificate F) (n : Nat) :
    ((ComplexRaw.ofQComplex zero).compute n).NestedIn
      (QBox.expand (QBox.point (t.sum (sample F c.precision n) n))
        (CertifiedComplexApproximation.rate (c.error*t.perimeter) n)) := by
  have hb := t.cauchy_bound (sample F c.precision n) c.error n (c.local_models n)
  have hE := Rat.mul_nonneg c.error_nonneg t.perimeter_nonneg
  have hd := Rat.mul_le_mul_of_nonneg_left (Series.half_pow_le_one_div_succ n) hE
  have hbound : normBound (neg (t.sum (sample F c.precision n) n)) ≤
      CertifiedComplexApproximation.rate (c.error*t.perimeter) n := by
    rw [normBound_neg]
    unfold CertifiedComplexApproximation.rate
    grind only [Rat.div_def]
  have h := ComplexExponentialApproximation.point_add_error_nested_expand
    (t.sum (sample F c.precision n) n) (neg (t.sum (sample F c.precision n) n)) hbound
  rw [add_neg_self_cert] at h
  exact h

theorem Triangle.contour_valid (t : Triangle) (F : QComplex → ComplexRaw)
    (c : t.Certificate F) : (t.contour F c.precision c.error).Valid :=
  CertifiedComplexApproximation.valid (Rat.mul_nonneg c.error_nonneg t.perimeter_nonneg)
    (ComplexRaw.ofQComplex_valid zero) (t.encloses_zero F c)

/-- Exact computed Cauchy theorem, derived from local analytic error data. -/
theorem Triangle.cauchy (t : Triangle) (F : QComplex → ComplexRaw)
    (c : t.Certificate F) :
    (t.contour F c.precision c.error).Equiv (ComplexRaw.ofQComplex zero) :=
  CertifiedComplexApproximation.equiv_anchor (Rat.mul_nonneg c.error_nonneg t.perimeter_nonneg)
    (ComplexRaw.ofQComplex_valid zero) (t.encloses_zero F c)

/-- Internal choices of evaluation precision and error majorants do not
change the represented contour value. -/
theorem Triangle.contour_independent (t : Triangle) (F G : QComplex → ComplexRaw)
    (c : t.Certificate F) (d : t.Certificate G) :
    (t.contour F c.precision c.error).Equiv (t.contour G d.precision d.error) :=
  ComplexRaw.equiv_trans (t.contour_valid F c) (ComplexRaw.ofQComplex_valid zero)
    (t.contour_valid G d) (t.cauchy F c) (ComplexRaw.equiv_symm (t.cauchy G d))

/-- A concrete check: conjugation does not satisfy the holomorphic contour
conclusion on the unit right triangle. -/
def unitTriangle : Triangle := ⟨zero, one, ⟨0,1⟩⟩

theorem conjugation_nonzero :
    unitTriangle.sum (fun z => ⟨z.re,-z.im⟩) 0 = ⟨0,1⟩ := by
  simp only [unitTriangle, Triangle.sum, edgeSum, midpoint, scaleRat, mul,
    sub, add, neg, zero, one, QComplex.mk.injEq]
  constructor <;> grind

end ComputableAnalysis.ComplexAnalysis
