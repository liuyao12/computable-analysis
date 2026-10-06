import ComputableAnalysis.ComplexInterval

/-!
# Polynomials over represented complex numbers

Coefficients and arguments are arbitrary valid raw representatives. Evaluation
is finite Horner arithmetic on their rational boxes. `Root` is exact raw-value
equality with zero, not an equality test or a supplied rational root.
-/
namespace ComputableAnalysis.RepresentedPolynomial

abbrev Coefficients := List ComplexCert

def zero : ComplexCert := ⟨ComplexRaw.ofQComplex QComplex.zero,
  ComplexRaw.ofQComplex_valid _⟩

def add (a b : ComplexCert) : ComplexCert :=
  ⟨ComplexRaw.add a.raw b.raw, ComplexRaw.add_valid a.valid b.valid⟩

def mul (a b : ComplexCert) : ComplexCert :=
  ⟨ComplexRaw.mul a.raw b.raw, ComplexRaw.mul_valid a.valid b.valid⟩

def eval : Coefficients → ComplexCert → ComplexCert
  | [], _ => zero
  | a :: p, z => add a (mul z (eval p z))

/-- Literal finite stage evaluation, allowing interval-valued coefficients. -/
def evalBox : List QBox → QBox → QBox
  | [], _ => QBox.zero
  | a :: p, z => QBox.add a (QBox.mul z (evalBox p z))

theorem eval_compute (p : Coefficients) (z : ComplexCert) (n : Nat) :
    (eval p z).raw.compute n = evalBox (p.map (fun a => a.raw.compute n)) (z.raw.compute n) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change QBox.add (a.raw.compute n) (QBox.mul (z.raw.compute n) ((eval p z).raw.compute n)) = _
      rw [ih]
      rfl

inductive Equivalent : Coefficients → Coefficients → Prop where
  | nil : Equivalent [] []
  | cons {a b : ComplexCert} {p q : Coefficients} :
      a.raw.Equiv b.raw → Equivalent p q → Equivalent (a :: p) (b :: q)

theorem eval_equiv {p q : Coefficients} (hpq : Equivalent p q)
    {z w : ComplexCert} (hzw : z.raw.Equiv w.raw) :
    (eval p z).raw.Equiv (eval q w).raw := by
  induction hpq with
  | nil => exact ComplexRaw.equiv_refl _ zero.valid
  | @cons a b p q hab _ ih =>
      exact ComplexRaw.add_equiv hab
        (ComplexRaw.mul_equiv z.valid w.valid (eval p z).valid (eval q w).valid hzw ih)

theorem equivalent_refl (p : Coefficients) : Equivalent p p := by
  induction p with
  | nil => exact .nil
  | cons a p ih => exact .cons (ComplexRaw.equiv_refl _ a.valid) ih

def Root (p : Coefficients) (z : ComplexCert) : Prop :=
  (eval p z).raw.Equiv zero.raw

theorem root_congr {p q : Coefficients} (hpq : Equivalent p q)
    {z w : ComplexCert} (hzw : z.raw.Equiv w.raw) (hz : Root p z) : Root q w :=
  ComplexRaw.equiv_trans (eval q w).valid (eval p z).valid zero.valid
    (ComplexRaw.equiv_symm (eval_equiv hpq hzw)) hz

/-- The exact root statement is equivalent to zero belonging to every
computed Horner enclosure. The enclosures are valid and shrink because all
coefficients and the argument are certified. -/
theorem root_iff_zero_in_boxes (p : Coefficients) (z : ComplexCert) :
    Root p z ↔ ∀ n, QBox.Overlaps
      (evalBox (p.map (fun a => a.raw.compute n)) (z.raw.compute n)) QBox.zero := by
  constructor
  · intro h n
    have hn := (ComplexRaw.compareAt_overlap_iff _ _ n n).1 (h n)
    change QBox.Overlaps ((eval p z).raw.compute n) QBox.zero at hn
    rwa [eval_compute] at hn
  · intro h n
    apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
    change QBox.Overlaps ((eval p z).raw.compute n) QBox.zero
    rw [eval_compute]
    exact h n

/-- A nested shrinking enclosure sequence whose polynomial images retain zero
represents an exact root. This is the limit bridge used after an existence
argument has produced the enclosures; it does not assume a pre-existing root. -/
theorem root_of_enclosures (p : Coefficients) (boxes : Nat → QBox)
    (hvalid : ComplexRaw.ValidCompute boxes)
    (hzero : ∀ n, QBox.Overlaps
      (evalBox (p.map (fun a => a.raw.compute n)) (boxes n)) QBox.zero) :
    Root p ⟨{ compute := boxes }, hvalid⟩ :=
  (root_iff_zero_in_boxes p _).2 hzero

/-- Rational-complex coefficients embed without changing the finite Horner
algorithm. -/
def ofRational (p : CPoly.Coeffs) : Coefficients :=
  p.map (fun a => ⟨ComplexRaw.ofQComplex a, ComplexRaw.ofQComplex_valid a⟩)

theorem eval_ofRational_compute (p : CPoly.Coeffs) (z : ComplexCert) (n : Nat) :
    (eval (ofRational p) z).raw.compute n = QBox.evalPoly p (z.raw.compute n) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change QBox.add (QBox.point a) (QBox.mul (z.raw.compute n)
        ((eval (ofRational p) z).raw.compute n)) = _
      rw [ih]
      rfl

/-- Real coefficients are a specialization, with no computability restriction
on the supplied representatives. -/
def ofReal (p : List Real) : Coefficients :=
  p.map fun (a : Real) =>
    { raw := ComplexRaw.ofRealRaw a.preferred
      valid := ComplexRaw.ofRealRaw_valid a.preferred a.valid }

end ComputableAnalysis.RepresentedPolynomial
