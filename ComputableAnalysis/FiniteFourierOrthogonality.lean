import ComputableAnalysis.FiniteFourierFoundation

/-!
# Certified finite Fourier orthogonality

The finite Fourier transform is driven by rational-complex arithmetic.  This
file isolates the one algebraic fact that an arbitrary finite transform needs:
the inner products of its certified mode vectors.  Root-of-unity identities
are supplied as finite certificates, so no completed `Real`, topology, or
classical infinite sum is hidden in the interface.
-/

namespace ComputableAnalysis

def finiteFourierModeVector (root : QComplex) (mode length : Nat) : List QComplex :=
  (List.range length).map (fun k =>
    QComplex.natPow root (mode * k))

def finiteFourierModeInnerProduct
    (root : QComplex) (length mode₁ mode₂ : Nat) : QComplex :=
  qcomplexListSum ((List.range length).map (fun k =>
    QComplex.mul
      (QComplex.conj (QComplex.natPow root (mode₁ * k)))
      (QComplex.natPow root (mode₂ * k))))

def finiteFourierSampleInnerProduct
    (root : QComplex) (length mode : Nat)
    (sample : Nat → QComplex) : QComplex :=
  qcomplexListSum ((List.range length).map (fun k =>
    QComplex.mul
      (QComplex.conj (QComplex.natPow root (mode * k)))
      (sample k)))

def finiteFourierSynthesisAt
    (root : QComplex) (k : Nat) (modes : List Nat)
    (coefficient : Nat → QComplex) : QComplex :=
  qcomplexListSum (modes.map (fun mode =>
    QComplex.mul (coefficient mode)
      (QComplex.natPow root (mode * k))))

private theorem qcomplexListSum_map_congr
    {α : Type} (xs : List α) (f g : α → QComplex)
    (h : ∀ x, x ∈ xs → f x = g x) :
    qcomplexListSum (xs.map f) = qcomplexListSum (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, qcomplexListSum]
      rw [h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

private theorem qcomplex_zero_add (z : QComplex) :
    QComplex.add QComplex.zero z = z := by
  cases z
  simp [QComplex.add, QComplex.zero]
  constructor <;> grind

private theorem qcomplexListSum_map_zero
    {α : Type} (xs : List α) (f : α → QComplex)
    (h : ∀ x, x ∈ xs → f x = QComplex.zero) :
    qcomplexListSum (xs.map f) = QComplex.zero := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, qcomplexListSum]
      rw [h x (by simp), ih (by
        intro y hy
        exact h y (by simp [hy]))]
      exact qcomplex_zero_add _

private theorem qcomplex_zero_mul (z : QComplex) :
    QComplex.mul QComplex.zero z = QComplex.zero := by
  cases z
  simp [QComplex.mul, QComplex.zero]
  constructor <;> grind

private theorem qcomplex_add_four_rearrange_local
    (a b c d : QComplex) :
    QComplex.add (QComplex.add a b) (QComplex.add c d) =
      QComplex.add (QComplex.add a c) (QComplex.add b d) := by
  cases a
  cases b
  cases c
  cases d
  simp [QComplex.add]
  constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem qcomplexListSum_map_add
    {α : Type} (xs : List α) (f g : α → QComplex) :
    qcomplexListSum (xs.map (fun x => QComplex.add (f x) (g x))) =
      QComplex.add (qcomplexListSum (xs.map f))
        (qcomplexListSum (xs.map g)) := by
  induction xs with
  | nil =>
      simp only [List.map_nil, qcomplexListSum]
      exact (qcomplex_zero_add QComplex.zero).symm
  | cons x xs ih =>
      simp only [List.map_cons, qcomplexListSum]
      rw [ih]
      exact qcomplex_add_four_rearrange_local (f x) (g x)
        (qcomplexListSum (xs.map f)) (qcomplexListSum (xs.map g))

private theorem qcomplex_scale_add_local (r : Rat) (x y : QComplex) :
    QComplex.scaleRat r (QComplex.add x y) =
      QComplex.add (QComplex.scaleRat r x) (QComplex.scaleRat r y) := by
  cases x
  cases y
  simp [QComplex.scaleRat, QComplex.add]
  constructor <;> grind [Rat.mul_add]

private theorem qcomplex_scale_zero_local (r : Rat) :
    QComplex.scaleRat r QComplex.zero = QComplex.zero := by
  simp [QComplex.scaleRat, QComplex.zero]

private theorem qcomplexListSum_map_scale
    {α : Type} (r : Rat) (xs : List α) (f : α → QComplex) :
    qcomplexListSum (xs.map (fun x => QComplex.scaleRat r (f x))) =
      QComplex.scaleRat r (qcomplexListSum (xs.map f)) := by
  induction xs with
  | nil =>
      simp only [List.map_nil, qcomplexListSum]
      exact (qcomplex_scale_zero_local r).symm
  | cons x xs ih =>
      simp only [List.map_cons, qcomplexListSum]
      rw [ih, qcomplex_scale_add_local]

/-! Synthesis is a finite operation: coefficients outside the advertised
mode list are irrelevant.  This is the elementary uniqueness principle used
when a finite Fourier certificate is extended with additional bookkeeping. -/
theorem finiteFourierSynthesisAt_congr
    (root : QComplex) (k : Nat) (modes : List Nat)
    (coefficient₁ coefficient₂ : Nat → QComplex)
    (hcoeff : ∀ mode, mode ∈ modes → coefficient₁ mode = coefficient₂ mode) :
    finiteFourierSynthesisAt root k modes coefficient₁ =
      finiteFourierSynthesisAt root k modes coefficient₂ := by
  induction modes with
  | nil => rfl
  | cons mode modes ih =>
      simp only [finiteFourierSynthesisAt, List.map_cons, qcomplexListSum]
      rw [hcoeff mode (by simp)]
      exact congrArg (QComplex.add
        (QComplex.mul (coefficient₂ mode)
          (QComplex.natPow root (mode * k))))
        (qcomplexListSum_map_congr modes _ _ (by
          intro mode' hmode'
          rw [hcoeff mode' (by simp [hmode']) ]))

theorem finiteFourierSynthesisAt_zero_coefficients
    (root : QComplex) (k : Nat) (modes : List Nat) :
    finiteFourierSynthesisAt root k modes (fun _ => QComplex.zero) =
      QComplex.zero := by
  induction modes with
  | nil => rfl
  | cons mode modes ih =>
      simp only [finiteFourierSynthesisAt, List.map_cons, qcomplexListSum]
      rw [qcomplexListSum_map_zero modes _ (by
        intro mode' hmode'
        exact qcomplex_zero_mul _)]
      rw [qcomplex_zero_mul]
      exact qcomplex_zero_add _

/-! Finite synthesis is linear in its coefficient table.  This is the
dual algebraic statement to linearity of the sampled coefficient map. -/
theorem finiteFourierSynthesisAt_add
    (root : QComplex) (k : Nat) (modes : List Nat)
    (coefficient₁ coefficient₂ coefficient : Nat → QComplex)
    (hcoefficient : ∀ mode, mode ∈ modes →
      coefficient mode = QComplex.add (coefficient₁ mode) (coefficient₂ mode)) :
    finiteFourierSynthesisAt root k modes coefficient =
      QComplex.add
        (finiteFourierSynthesisAt root k modes coefficient₁)
        (finiteFourierSynthesisAt root k modes coefficient₂) := by
  unfold finiteFourierSynthesisAt
  rw [qcomplexListSum_map_congr]
  · exact qcomplexListSum_map_add modes _ _
  · intro mode hmode
    rw [hcoefficient mode hmode, QComplex.add_mul_cert]

private theorem qcomplex_scale_mul_left_local
    (r : Rat) (x y : QComplex) :
    QComplex.mul (QComplex.scaleRat r x) y =
      QComplex.scaleRat r (QComplex.mul x y) := by
  cases x
  cases y
  simp [QComplex.scaleRat, QComplex.mul]
  constructor <;> grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
    Rat.add_mul]

theorem finiteFourierSynthesisAt_scale
    (root : QComplex) (k : Nat) (modes : List Nat)
    (r : Rat) (coefficient₀ coefficient : Nat → QComplex)
    (hcoefficient : ∀ mode, mode ∈ modes →
      coefficient mode = QComplex.scaleRat r (coefficient₀ mode)) :
    finiteFourierSynthesisAt root k modes coefficient =
      QComplex.scaleRat r
        (finiteFourierSynthesisAt root k modes coefficient₀) := by
  unfold finiteFourierSynthesisAt
  rw [qcomplexListSum_map_congr]
  · rw [qcomplexListSum_map_scale]
  · intro mode hmode
    rw [hcoefficient mode hmode, qcomplex_scale_mul_left_local]

/-! The finite sample inner product is linear in the sampled values.  This is
the algebraic step needed to transport Fourier coefficients through addition;
it is stated entirely over rational-complex stage data. -/
theorem finiteFourierSampleInnerProduct_add
    (root : QComplex) (length mode : Nat)
    (sample₁ sample₂ sample : Nat → QComplex)
    (hsample : ∀ k, sample k = QComplex.add (sample₁ k) (sample₂ k)) :
    finiteFourierSampleInnerProduct root length mode sample =
      QComplex.add
        (finiteFourierSampleInnerProduct root length mode sample₁)
        (finiteFourierSampleInnerProduct root length mode sample₂) := by
  unfold finiteFourierSampleInnerProduct
  rw [qcomplexListSum_map_congr]
  · exact qcomplexListSum_map_add (List.range length) _ _
  · intro k hk
    rw [hsample k, QComplex.mul_add_cert]

private theorem qcomplex_mul_scale_local
    (x y : QComplex) (r : Rat) :
    QComplex.mul x (QComplex.scaleRat r y) =
      QComplex.scaleRat r (QComplex.mul x y) := by
  cases x
  cases y
  simp [QComplex.mul, QComplex.scaleRat]
  constructor <;> grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
    Rat.add_mul]

private theorem qcomplex_conj_conj_local (z : QComplex) :
    QComplex.conj (QComplex.conj z) = z := by
  cases z
  simp [QComplex.conj]

private theorem qcomplexListSum_conj
    (xs : List QComplex) :
    QComplex.conj (qcomplexListSum xs) =
      qcomplexListSum (xs.map QComplex.conj) := by
  induction xs with
  | nil =>
      simp [qcomplexListSum, QComplex.conj, QComplex.zero]
  | cons x xs ih =>
      simp only [qcomplexListSum, List.map_cons, QComplex.conj_add]
      rw [ih]

/-! Scalar multiplication is the second half of the finite coefficient
linearity law. -/
theorem finiteFourierSampleInnerProduct_scale
    (root : QComplex) (length mode : Nat)
    (r : Rat) (sample₀ sample : Nat → QComplex)
    (hsample : ∀ k, sample k = QComplex.scaleRat r (sample₀ k)) :
    finiteFourierSampleInnerProduct root length mode sample =
      QComplex.scaleRat r
        (finiteFourierSampleInnerProduct root length mode sample₀) := by
  unfold finiteFourierSampleInnerProduct
  rw [qcomplexListSum_map_congr]
  · rw [qcomplexListSum_map_scale]
  · intro k hk
    rw [hsample k, qcomplex_mul_scale_local]

/-! Conjugating both the root and the sampled values conjugates the finite
Fourier coefficient.  This is the stage-level symmetry used for real-valued
signals. -/
theorem finiteFourierSampleInnerProduct_conj
    (root : QComplex) (length mode : Nat)
    (sample₀ sample : Nat → QComplex)
    (hsample : ∀ k, sample k = QComplex.conj (sample₀ k)) :
    finiteFourierSampleInnerProduct (QComplex.conj root) length mode sample =
      QComplex.conj
        (finiteFourierSampleInnerProduct root length mode sample₀) := by
  unfold finiteFourierSampleInnerProduct
  rw [qcomplexListSum_conj]
  rw [List.map_map]
  apply qcomplexListSum_map_congr (List.range length)
    (fun k => QComplex.mul
      (QComplex.conj (QComplex.natPow (QComplex.conj root) (mode * k)))
      (sample k))
    (fun k => QComplex.conj (QComplex.mul
      (QComplex.conj (QComplex.natPow root (mode * k)))
      (sample₀ k)))
  intro k hk
  rw [hsample k, QComplex.conj_mul, QComplex.conj_natPow,
    qcomplex_conj_conj_local]
  simp only [qcomplex_conj_conj_local]

structure FiniteFourierOrthogonalityCertificate where
  root : QComplex
  length : Nat
  positive_length : 0 < length
  modes : List Nat
  mode_bounded : ∀ mode, mode ∈ modes → mode < length
  inner_product : ∀ mode₁ mode₂,
    mode₁ ∈ modes → mode₂ ∈ modes →
      finiteFourierModeInnerProduct root length mode₁ mode₂ =
        if mode₁ = mode₂ then
          QComplex.ofRat (length : Rat)
        else QComplex.zero

/-! A reconstruction certificate is the finite, executable form of DFT
inversion.  It keeps the sample function and the coefficient formula visible;
the final reconstruction equality is an obligation over finitely many sample
indices. -/
structure FiniteFourierReconstructionCertificate where
  orthogonality : FiniteFourierOrthogonalityCertificate
  sample : Nat → QComplex
  coefficient : Nat → QComplex
  coefficient_formula : ∀ mode, mode ∈ orthogonality.modes →
    coefficient mode =
      QComplex.scaleRat
        (1 / (orthogonality.length : Rat))
        (finiteFourierSampleInnerProduct
          orthogonality.root orthogonality.length mode sample)
  reconstruction : ∀ k, k < orthogonality.length →
    finiteFourierSynthesisAt orthogonality.root k orthogonality.modes coefficient =
      sample k

theorem FiniteFourierReconstructionCertificate.coefficient_formula_at
    (certificate : FiniteFourierReconstructionCertificate)
    {mode : Nat} (hmode : mode ∈ certificate.orthogonality.modes) :
    certificate.coefficient mode =
      QComplex.scaleRat
        (1 / (certificate.orthogonality.length : Rat))
        (finiteFourierSampleInnerProduct
          certificate.orthogonality.root certificate.orthogonality.length
          mode certificate.sample) := by
  exact certificate.coefficient_formula mode hmode

theorem FiniteFourierReconstructionCertificate.reconstructs
    (certificate : FiniteFourierReconstructionCertificate)
    {k : Nat} (hk : k < certificate.orthogonality.length) :
    finiteFourierSynthesisAt certificate.orthogonality.root k
        certificate.orthogonality.modes certificate.coefficient =
      certificate.sample k := by
  exact certificate.reconstruction k hk

/-! Reconstruction is invariant under replacing coefficients by an extension
that agrees on the certified mode list.  This is the bridge between a
canonical finite Fourier table and an independently computed implementation
of the same coefficients. -/
theorem FiniteFourierReconstructionCertificate.reconstructs_of_coefficient_congr
    (certificate : FiniteFourierReconstructionCertificate)
    (coefficient' : Nat → QComplex)
    (hcoeff : ∀ mode, mode ∈ certificate.orthogonality.modes →
      coefficient' mode = certificate.coefficient mode)
    {k : Nat} (hk : k < certificate.orthogonality.length) :
    finiteFourierSynthesisAt certificate.orthogonality.root k
        certificate.orthogonality.modes coefficient' =
      certificate.sample k := by
  rw [finiteFourierSynthesisAt_congr
    certificate.orthogonality.root k certificate.orthogonality.modes
    coefficient' certificate.coefficient hcoeff]
  exact certificate.reconstruction k hk

/-! The four-point transform is the first concrete instance of the general
interface.  Its orthogonality claims are checked by finite reduction of the
rational-complex arithmetic, rather than imported from a theorem about
completed complex numbers. -/
def quarterTurnFourierOrthogonalityCertificate :
    FiniteFourierOrthogonalityCertificate where
  root := RotationSeries.imaginaryUnit
  length := 4
  positive_length := by omega
  modes := [0, 1, 2, 3]
  mode_bounded := by
    intro mode hmode
    simp at hmode
    rcases hmode with rfl | rfl | rfl | rfl <;> omega
  inner_product := by
    intro mode₁ mode₂ h₁ h₂
    simp at h₁ h₂
    rcases h₁ with rfl | rfl | rfl | rfl <;>
      rcases h₂ with rfl | rfl | rfl | rfl <;>
        native_decide

theorem FiniteFourierOrthogonalityCertificate.mode_vector_length
    (certificate : FiniteFourierOrthogonalityCertificate)
    (mode : Nat) :
    (finiteFourierModeVector certificate.root mode certificate.length).length =
      certificate.length := by
  simp [finiteFourierModeVector]

theorem FiniteFourierOrthogonalityCertificate.diagonal_inner_product
    (certificate : FiniteFourierOrthogonalityCertificate)
    {mode : Nat} (hmode : mode ∈ certificate.modes) :
    finiteFourierModeInnerProduct certificate.root certificate.length mode mode =
      QComplex.ofRat (certificate.length : Rat) := by
  simpa using certificate.inner_product mode mode hmode hmode

theorem FiniteFourierOrthogonalityCertificate.off_diagonal_inner_product
    (certificate : FiniteFourierOrthogonalityCertificate)
    {mode₁ mode₂ : Nat}
    (h₁ : mode₁ ∈ certificate.modes)
    (h₂ : mode₂ ∈ certificate.modes)
    (hne : mode₁ ≠ mode₂) :
    finiteFourierModeInnerProduct certificate.root certificate.length mode₁ mode₂ =
      QComplex.zero := by
  simpa [hne] using certificate.inner_product mode₁ mode₂ h₁ h₂

theorem FiniteFourierOrthogonalityCertificate.modes_bounded
    (certificate : FiniteFourierOrthogonalityCertificate)
    {mode : Nat} (hmode : mode ∈ certificate.modes) :
    mode < certificate.length := by
  exact certificate.mode_bounded mode hmode

/-! The certificate is also an executable finite check: every asserted inner
product is a sum over `List.range length`, hence can be instantiated by a
finite rational-complex computation. -/
theorem finiteFourierModeVector_eq_range_map
    (root : QComplex) (mode length : Nat) :
    finiteFourierModeVector root mode length =
      (List.range length).map (fun k =>
        QComplex.natPow root (mode * k)) := by
  rfl

end ComputableAnalysis
