import ComputableAnalysis.ComplexAnalysis.Polygon

/-! Concrete analytic certificates: the Cauchy theorem has nonconstant
clients and does not consume an assumed quadrature-vanishing certificate. -/
namespace ComputableAnalysis.ComplexAnalysis
open QComplex

theorem Triangle.midpoint_distances (t : Triangle) :
    normBound (sub (midpoint t.a t.b) t.a) ≤ t.perimeter ∧
    normBound (sub (midpoint t.b t.c) t.a) ≤ t.perimeter ∧
    normBound (sub (midpoint t.c t.a) t.a) ≤ t.perimeter := by
  have hn1 := normBound_nonneg (sub t.b t.a)
  have hn2 := normBound_nonneg (sub t.c t.b)
  have hn3 := normBound_nonneg (sub t.a t.c)
  have hswap : normBound (sub t.c t.a) = normBound (sub t.a t.c) := by
    have he : sub t.c t.a = neg (sub t.a t.c) := by
      simp only [sub, add, neg, QComplex.mk.injEq]; constructor <;> grind
    rw [he, normBound_neg]
  have he1 : sub (midpoint t.a t.b) t.a = scaleRat (1/2) (sub t.b t.a) := by
    simp only [midpoint, scaleRat, sub, add, neg, QComplex.mk.injEq]; constructor <;> grind
  have he2 : sub (midpoint t.b t.c) t.a =
      scaleRat (1/2) (add (sub t.b t.a) (sub t.c t.a)) := by
    simp only [midpoint, scaleRat, sub, add, neg, QComplex.mk.injEq]; constructor <;> grind
  have he3 : sub (midpoint t.c t.a) t.a = scaleRat (1/2) (sub t.c t.a) := by
    simp only [midpoint, scaleRat, sub, add, neg, QComplex.mk.injEq]; constructor <;> grind
  have hm := normBound_add_le (sub t.b t.a) (sub t.c t.a)
  rw [hswap] at hm
  rw [he1,he2,he3]
  simp only [normBound_scaleRat, qabs_eq_self_of_nonneg (by grind : (0:Rat) ≤ 1/2)]
  rw [hswap]
  unfold Triangle.perimeter
  constructor
  · grind only
  constructor <;> grind only

def squareFunction (z : QComplex) : QComplex := mul z z

theorem square_remainder (a z : QComplex) :
    sub (squareFunction z) (affine (neg (mul a a)) (scaleRat 2 a) z) =
      mul (sub z a) (sub z a) := by
  simp only [squareFunction, affine, scaleRat, sub, add, neg, mul, QComplex.mk.injEq]
  constructor <;> grind

theorem Triangle.point_distance (t : Triangle) (z : QComplex) (hz : t.Contains z) :
    normBound (sub z t.a) ≤ t.perimeter := by
  obtain ⟨u,v,hu,hv,huv,rfl⟩ := hz
  have he : sub (add t.a (add (scaleRat u (sub t.b t.a)) (scaleRat v (sub t.c t.a)))) t.a =
      add (scaleRat u (sub t.b t.a)) (scaleRat v (sub t.c t.a)) := by
    simp only [sub,add,neg,scaleRat,QComplex.mk.injEq]; constructor <;> grind
  rw [he]
  have ha := normBound_add_le (scaleRat u (sub t.b t.a)) (scaleRat v (sub t.c t.a))
  rw [normBound_scaleRat,normBound_scaleRat,qabs_eq_self_of_nonneg hu,qabs_eq_self_of_nonneg hv] at ha
  have hs : normBound (sub t.c t.a) = normBound (sub t.a t.c) := by
    have he : sub t.c t.a = neg (sub t.a t.c) := by
      simp only [sub,add,neg,QComplex.mk.injEq]; constructor <;> grind
    rw [he,normBound_neg]
  rw [hs] at ha
  have h1 := Rat.mul_le_mul_of_nonneg_right (show u ≤ 1 by grind) (normBound_nonneg (sub t.b t.a))
  have h2 := Rat.mul_le_mul_of_nonneg_right (show v ≤ 1 by grind) (normBound_nonneg (sub t.a t.c))
  have h3 := normBound_nonneg (sub t.c t.b)
  unfold Triangle.perimeter
  grind only

theorem Triangle.square_model (t : Triangle) : t.Model squareFunction (t.perimeter*t.perimeter) := by
  refine ⟨neg (mul t.a t.a), scaleRat 2 t.a, ?_⟩
  intro z hz
  rw [square_remainder]
  have hd := t.point_distance z hz
  apply Rat.le_trans (normBound_mul_le _ _)
  apply Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hd (normBound_nonneg _))
  exact Rat.mul_le_mul_of_nonneg_left hd t.perimeter_nonneg

theorem Triangle.square_models (t : Triangle) (n : Nat) :
    t.Models squareFunction (t.perimeter*t.perimeter) n := by
  induction n generalizing t with
  | zero => exact t.square_model
  | succ n ih =>
    intro i
    have h := ih (t.child i)
    rw [Triangle.perimeter_child] at h
    have he : t.perimeter / 2 * (t.perimeter / 2) = t.perimeter*t.perimeter/4 := by grind
    rw [he] at h
    exact h

def squareRaw (z : QComplex) : ComplexRaw := ComplexRaw.ofQComplex (squareFunction z)

def Triangle.squareCertificate (t : Triangle) : t.Certificate squareRaw where
  precision := fun n _ => n
  error := t.perimeter*t.perimeter
  error_nonneg := Rat.mul_nonneg t.perimeter_nonneg t.perimeter_nonneg
  values_valid := fun z => ComplexRaw.ofQComplex_valid _
  sample_accuracy := by
    intro n z
    have h := CertifiedComplexApproximation.rate_nonneg (by grind : (0:Rat) ≤ 1) n
    simp only [squareRaw, ComplexRaw.ofQComplex, QBox.width, QBox.height]
    constructor <;> grind only
  local_models := by
    intro n
    have he : sample squareRaw (fun n _ => n) n = squareFunction := by
      funext z
      change (QBox.point (squareFunction z)).center = squareFunction z
      cases squareFunction z
      simp only [QBox.point, QBox.center, QComplex.mk.injEq]
      constructor <;> grind
    rw [he]
    exact t.square_models n

theorem square_cauchy (t : Triangle) :
    (t.quadrature squareRaw t.squareCertificate.precision t.squareCertificate.error).Equiv
      (ComplexRaw.ofQComplex zero) := t.cauchy squareRaw t.squareCertificate

/-- Any valid represented constant, including an irrational complex value. -/
def Triangle.constantCertificate (t : Triangle) (c : ComplexRaw) (hc : c.Valid)
    (precision : Nat → Nat)
    (accuracy : ∀ n, (c.compute (precision n)).width ≤ CertifiedComplexApproximation.rate 1 n ∧
      (c.compute (precision n)).height ≤ CertifiedComplexApproximation.rate 1 n) :
    t.Certificate (fun _ => c) where
  precision := fun n _ => precision n
  error := 0
  error_nonneg := Rat.le_refl
  values_valid := fun _ => hc
  sample_accuracy := fun n _ => accuracy n
  local_models := by
    intro n
    suffices h : ∀ (k : Nat) (t : Triangle),
        t.Models (sample (fun _ => c) (fun n _ => precision n) n) 0 k from h n t
    intro k
    induction k with
    | zero =>
      intro t
      refine ⟨(c.compute (precision n)).center, zero, ?_⟩
      intro z _
      simp only [sample, affine, mul, add, sub, neg, zero, normBound, qabs]
      grind
    | succ k ih =>
      intro t i
      simpa only [Rat.div_def, Rat.zero_mul] using ih (t.child i)

end ComputableAnalysis.ComplexAnalysis
