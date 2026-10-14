import ComputableAnalysis.ModularForms.ExponentialDerivative
import ComputableAnalysis.RiemannHilbert.DomainAffineFunction
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums
import ComputableAnalysis.RiemannHilbert.EntireConstantODEUniqueness
import ComputableAnalysis.RiemannHilbert.ExponentialScalarParameters
import ComputableAnalysis.ComplexAffine

/-! Actual entire sine/cosine solution computations. One calculation pairs
two scalar exponential series; the other evaluates the rotation matrix's
recursive Taylor coefficients. Their derivative laws are proved separately.
This module does not import elementary sine agreement theorems. -/
namespace ComputableAnalysis.ElementarySineODE
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 2000000

def zeroScalar : Scalar := ⟨zero,ofQComplex_valid _⟩
def iScalar : Scalar := ⟨ofQComplex ⟨0,1⟩,ofQComplex_valid _⟩
def sineFactor : Scalar := ⟨ofQComplex ⟨0,-(1/2)⟩,ofQComplex_valid _⟩
def halfScalar : Scalar := ⟨ofQComplex ⟨1/2,0⟩,ofQComplex_valid _⟩

def exponentialAt (a : Scalar) : DomainFunctions.Map where
  domain _ := True
  eval z _ := ModularForms.entireExponentialValue (scalarProduct a z)
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ h := ModularForms.entireExponentialValue_congr _ _
    (mul_equiv a.property a.property z.property w.property (equiv_refl _ a.property) h)

def exponentialAt_holomorphic (a : Scalar) : DomainFunctions.Holomorphic (exponentialAt a) :=
  (ModularForms.entireExponential_holomorphic.compose (affine_holomorphic zeroScalar a)).transfer
    (exponentialAt a) (fun _ _ => ⟨trivial,trivial⟩)
    ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩
    (fun z _ => ModularForms.entireExponentialValue_congr _ _
      (zero_add_equiv (mul a.val z.val) (mul_valid a.property z.property)))

theorem exponentialAt_derivative (a z : Scalar) :
    ((exponentialAt_holomorphic a).derivative z trivial).val.Equiv
      (mul ((exponentialAt a).eval z trivial).val a.val) := by
  let w := (DomainFunctions.affine zeroScalar a).eval z trivial
  have he : (ModularForms.entireExponentialValue w).val.Equiv
      ((exponentialAt a).eval z trivial).val :=
    ModularForms.entireExponentialValue_congr _ _
      (zero_add_equiv (mul a.val z.val) (mul_valid a.property z.property))
  exact mul_equiv
    (ModularForms.entireExponential_holomorphic.derivative w trivial).property
    ((exponentialAt a).eval z trivial).property a.property a.property
    (equiv_trans
      (ModularForms.entireExponential_holomorphic.derivative w trivial).property
      (ModularForms.entireExponentialValue w).property ((exponentialAt a).eval z trivial).property
      (ModularForms.entireExponential_derivative_value w) he)
    (equiv_refl _ a.property)

def positiveFrequency (a : Scalar) : Scalar := scalarProduct iScalar a
def negativeFrequency (a : Scalar) : Scalar := scalarNeg (positiveFrequency a)

def exponentialDifference (a : Scalar) : DomainFunctions.Map :=
  sumOn (exponentialAt (positiveFrequency a)) (negate (exponentialAt (negativeFrequency a)))
    (fun _ _ => trivial)
def exponentialSum (a : Scalar) : DomainFunctions.Map :=
  sumOn (exponentialAt (positiveFrequency a)) (exponentialAt (negativeFrequency a))
    (fun _ _ => trivial)

def sine (a : Scalar) : DomainFunctions.Map :=
  productOn (constantOn (fun _ : Scalar => True) ScalarTopology.wholeData.invariant sineFactor)
    (exponentialDifference a) (fun _ _ => trivial)
def cosine (a : Scalar) : DomainFunctions.Map :=
  productOn (constantOn (fun _ : Scalar => True) ScalarTopology.wholeData.invariant halfScalar)
    (exponentialSum a) (fun _ _ => trivial)

def sine_holomorphic (a : Scalar) : DomainFunctions.Holomorphic (sine a) :=
  (constantOn_holomorphic ScalarTopology.wholeData sineFactor).productOn
    ((exponentialAt_holomorphic (positiveFrequency a)).sumOn
      (exponentialAt_holomorphic (negativeFrequency a)).negate (fun _ _ => trivial))
    (fun _ _ => trivial)
def cosine_holomorphic (a : Scalar) : DomainFunctions.Holomorphic (cosine a) :=
  (constantOn_holomorphic ScalarTopology.wholeData halfScalar).productOn
    ((exponentialAt_holomorphic (positiveFrequency a)).sumOn
      (exponentialAt_holomorphic (negativeFrequency a)) (fun _ _ => trivial))
    (fun _ _ => trivial)

private theorem rationalProduct (p q : QComplex) :
    (mul (ofQComplex p) (ofQComplex q)).Equiv (ofQComplex (QComplex.mul p q)) :=
  equiv_trans (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))
    (qcomplexLeftMul_valid p (ofQComplex_valid q)) (ofQComplex_valid _)
    (equiv_symm (qcomplexLeftMul_equiv_mul_ofQComplex p (ofQComplex_valid q)))
    (qcomplexLeftMul_ofQComplex p q)

private theorem sineFactor_i :
    (mul sineFactor.val iScalar.val).Equiv halfScalar.val := by
  simpa only [sineFactor,iScalar,halfScalar,
    show QComplex.mul ⟨0,-(1/2)⟩ ⟨0,1⟩ = ⟨1/2,0⟩ by decide +kernel] using
    rationalProduct ⟨0,-(1/2)⟩ ⟨0,1⟩

private theorem halfScalar_i :
    (mul halfScalar.val iScalar.val).Equiv (neg sineFactor.val) := by
  have h := rationalProduct ⟨1/2,0⟩ ⟨0,1⟩
  have he : QComplex.mul ⟨1/2,0⟩ ⟨0,1⟩ = ⟨0,1/2⟩ := by decide +kernel
  rw [he] at h
  apply equiv_trans (mul_valid halfScalar.property iScalar.property) (ofQComplex_valid _)
    (neg_valid sineFactor.property) h
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  change ((0:Rat)≤ -0 ∧ (1/2:Rat)≤ -(-(1/2))) ∧
    (-0≤ (0:Rat) ∧ -(-(1/2))≤ (1/2:Rat))
  decide +kernel

private theorem exponentialAt_derivative_quotient (a z : Scalar) :
    ComplexRawQuotient.ofRaw ((exponentialAt_holomorphic a).derivative z trivial).val
      ((exponentialAt_holomorphic a).derivative z trivial).property =
    ComplexRawQuotient.ofRaw ((exponentialAt a).eval z trivial).val
      ((exponentialAt a).eval z trivial).property * ComplexRawQuotient.ofRaw a.val a.property :=
  ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((exponentialAt_holomorphic a).derivative z trivial).property)
    (hright := mul_valid ((exponentialAt a).eval z trivial).property a.property)
    (exponentialAt_derivative a z)

theorem sine_derivative (a z : Scalar) :
    ((sine_holomorphic a).derivative z trivial).val.Equiv
      (mul a.val ((cosine a).eval z trivial).val) := by
  have hp := exponentialAt_derivative_quotient (positiveFrequency a) z
  have hm := exponentialAt_derivative_quotient (negativeFrequency a) z
  have hji := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid sineFactor.property iScalar.property) (hright := halfScalar.property) sineFactor_i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((sine_holomorphic a).derivative z trivial).property)
    (hright := mul_valid a.property ((cosine a).eval z trivial).property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let I := ComplexRawQuotient.ofRaw iScalar.val iScalar.property
  let J := ComplexRawQuotient.ofRaw sineFactor.val sineFactor.property
  let H := ComplexRawQuotient.ofRaw halfScalar.val halfScalar.property
  let P := ComplexRawQuotient.ofRaw ((exponentialAt (positiveFrequency a)).eval z trivial).val
    ((exponentialAt (positiveFrequency a)).eval z trivial).property
  let M := ComplexRawQuotient.ofRaw ((exponentialAt (negativeFrequency a)).eval z trivial).val
    ((exponentialAt (negativeFrequency a)).eval z trivial).property
  let DP := ComplexRawQuotient.ofRaw ((exponentialAt_holomorphic (positiveFrequency a)).derivative z trivial).val
    ((exponentialAt_holomorphic (positiveFrequency a)).derivative z trivial).property
  let DM := ComplexRawQuotient.ofRaw ((exponentialAt_holomorphic (negativeFrequency a)).derivative z trivial).val
    ((exponentialAt_holomorphic (negativeFrequency a)).derivative z trivial).property
  change DP=P*(I*A) at hp
  change DM=M*(-(I*A)) at hm
  change J*I=H at hji
  change 0*(P + -M)+J*(DP + -DM)=A*(H*(P+M))
  grind only

theorem cosine_derivative (a z : Scalar) :
    ((cosine_holomorphic a).derivative z trivial).val.Equiv
      (neg (mul a.val ((sine a).eval z trivial).val)) := by
  have hp := exponentialAt_derivative_quotient (positiveFrequency a) z
  have hm := exponentialAt_derivative_quotient (negativeFrequency a) z
  have hhi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid halfScalar.property iScalar.property) (hright := neg_valid sineFactor.property) halfScalar_i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((cosine_holomorphic a).derivative z trivial).property)
    (hright := neg_valid (mul_valid a.property ((sine a).eval z trivial).property))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let I := ComplexRawQuotient.ofRaw iScalar.val iScalar.property
  let J := ComplexRawQuotient.ofRaw sineFactor.val sineFactor.property
  let H := ComplexRawQuotient.ofRaw halfScalar.val halfScalar.property
  let P := ComplexRawQuotient.ofRaw ((exponentialAt (positiveFrequency a)).eval z trivial).val
    ((exponentialAt (positiveFrequency a)).eval z trivial).property
  let M := ComplexRawQuotient.ofRaw ((exponentialAt (negativeFrequency a)).eval z trivial).val
    ((exponentialAt (negativeFrequency a)).eval z trivial).property
  let DP := ComplexRawQuotient.ofRaw ((exponentialAt_holomorphic (positiveFrequency a)).derivative z trivial).val
    ((exponentialAt_holomorphic (positiveFrequency a)).derivative z trivial).property
  let DM := ComplexRawQuotient.ofRaw ((exponentialAt_holomorphic (negativeFrequency a)).derivative z trivial).val
    ((exponentialAt_holomorphic (negativeFrequency a)).derivative z trivial).property
  change DP=P*(I*A) at hp
  change DM=M*(-(I*A)) at hm
  change H*I= -J at hhi
  change 0*(P+M)+H*(DP+DM)= -(A*(J*(P + -M)))
  grind only

def pair (s c : Scalar) : Fiber 2 :=
  ⟨fun i => if i=0 then s.val else c.val,
    fun i => by dsimp; split <;> first | exact s.property | exact c.property⟩

def rotation (a : Scalar) : ValueMap (Fiber 2) (Fiber 2) where
  eval x := pair (scalarProduct a (Fiber.coordinate x 1))
    (scalarNeg (scalarProduct a (Fiber.coordinate x 0)))
  congr := by
    intro x y h i
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl | rfl
    · exact mul_equiv a.property a.property (x.property 1) (y.property 1) (equiv_refl _ a.property) (h 1)
    · exact neg_equiv (mul_equiv a.property a.property (x.property 0) (y.property 0) (equiv_refl _ a.property) (h 0))

theorem rotation_linear (a : Scalar) : IsLinear (rotation a) := by
  constructor
  · intro x y i
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl | rfl
    · exact mul_add_equiv a.val (x.val 1) (y.val 1) a.property (x.property 1) (y.property 1)
    · apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((rotation a).eval (Fiber.add x y)).property 1)
        (hright := (Fiber.add ((rotation a).eval x) ((rotation a).eval y)).property 1)
      let A := ComplexRawQuotient.ofRaw a.val a.property
      let X := ComplexRawQuotient.ofRaw (x.val 0) (x.property 0)
      let Y := ComplexRawQuotient.ofRaw (y.val 0) (y.property 0)
      change -(A*(X+Y))= -(A*X)+ -(A*Y)
      grind only
  · intro b x i
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl | rfl
    · apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((rotation a).eval (Fiber.scale b x)).property 0)
        (hright := (Fiber.scale b ((rotation a).eval x)).property 0)
      let A := ComplexRawQuotient.ofRaw a.val a.property
      let B := ComplexRawQuotient.ofRaw b.val b.property
      let X := ComplexRawQuotient.ofRaw (x.val 1) (x.property 1)
      change A*(B*X)=B*(A*X)
      grind only
    · apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((rotation a).eval (Fiber.scale b x)).property 1)
        (hright := (Fiber.scale b ((rotation a).eval x)).property 1)
      let A := ComplexRawQuotient.ofRaw a.val a.property
      let B := ComplexRawQuotient.ofRaw b.val b.property
      let X := ComplexRawQuotient.ofRaw (x.val 0) (x.property 0)
      change -(A*(B*X))=B*(-(A*X))
      grind only

def exponentialVector (a : Scalar) : DomainVectorFunctions.Map 2 where
  domain _ := True
  eval z _ := pair ((sine a).eval z trivial) ((cosine a).eval z trivial)
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ h i := by
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl | rfl
    · exact (sine a).eval_congr z w trivial trivial h
    · exact (cosine a).eval_congr z w trivial trivial h

def exponentialVector_holomorphic (a : Scalar) : DomainVectorFunctions.Holomorphic (exponentialVector a) where
  openDomain := ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩
  coordinates i := by
    by_cases hi : i=0
    · subst i
      exact (sine_holomorphic a).transfer _ (fun _ _ => trivial)
        ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩
        (fun z _ => equiv_refl _ ((sine a).eval z trivial).property)
    · have hi1 : i=1 := by omega
      subst i
      exact (cosine_holomorphic a).transfer _ (fun _ _ => trivial)
        ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩
        (fun z _ => equiv_refl _ ((cosine a).eval z trivial).property)

theorem exponentialVector_ode (a : Scalar) :
    CoordinateConnection.Horizontal (exponentialVector a) (exponentialVector_holomorphic a)
      (fun _ _ => rotation a) := by
  intro z _ i
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl | rfl
  · exact sine_derivative a z
  · exact cosine_derivative a z

theorem exponentialAt_zero (a : Scalar) :
    ((exponentialAt a).eval zeroScalar trivial).val.Equiv one :=
  equiv_trans ((exponentialAt a).eval zeroScalar trivial).property
    (ModularForms.entireExponentialValue zeroScalar).property (ofQComplex_valid _)
    (ModularForms.entireExponentialValue_congr _ _ (mul_zero_equiv a.val a.property))
    ModularForms.entireExponential_zero

private theorem two_halves : (add halfScalar.val halfScalar.val).Equiv one := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  change ((1/2:Rat)+(1/2)≤1 ∧ (0:Rat)+0≤0) ∧ (1≤(1/2:Rat)+(1/2) ∧ 0≤(0:Rat)+0)
  decide +kernel

def initial : Fiber 2 := pair zeroScalar oneScalar

theorem exponentialVector_initial (a : Scalar) :
    (exponentialVector a).eval zeroScalar trivial ≈ initial := by
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((exponentialAt (positiveFrequency a)).eval zeroScalar trivial).property)
    (hright := ofQComplex_valid _) (exponentialAt_zero (positiveFrequency a))
  have hm := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((exponentialAt (negativeFrequency a)).eval zeroScalar trivial).property)
    (hright := ofQComplex_valid _) (exponentialAt_zero (negativeFrequency a))
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid halfScalar.property halfScalar.property) (hright := ofQComplex_valid _) two_halves
  let P := ComplexRawQuotient.ofRaw ((exponentialAt (positiveFrequency a)).eval zeroScalar trivial).val
    ((exponentialAt (positiveFrequency a)).eval zeroScalar trivial).property
  let M := ComplexRawQuotient.ofRaw ((exponentialAt (negativeFrequency a)).eval zeroScalar trivial).val
    ((exponentialAt (negativeFrequency a)).eval zeroScalar trivial).property
  change P=1 at hp
  change M=1 at hm
  intro i
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl | rfl
  · apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((exponentialVector a).eval zeroScalar trivial).property 0)
      (hright := initial.property 0)
    let J := ComplexRawQuotient.ofRaw sineFactor.val sineFactor.property
    change J*(P + -M)=0
    rw [hp,hm]
    grind only
  · apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((exponentialVector a).eval zeroScalar trivial).property 1)
      (hright := initial.property 1)
    let H := ComplexRawQuotient.ofRaw halfScalar.val halfScalar.property
    change H+H=1 at hh
    change H*(P+M)=1
    rw [hp,hm]
    grind only

/-- The second computation is the actual executable matrix Taylor sum, with
coefficients determined by the rotation generator and initial vector. -/
def seriesVector (a : Scalar) : DomainVectorFunctions.Map 2 :=
  MatrixExponential.vector (rotation a) (rotation_linear a) initial
def seriesVector_holomorphic (a : Scalar) : DomainVectorFunctions.Holomorphic (seriesVector a) :=
  MatrixExponential.vector_holomorphic (rotation a) (rotation_linear a) initial

theorem seriesVector_ode (a : Scalar) :
    CoordinateConnection.Horizontal (seriesVector a) (seriesVector_holomorphic a)
      (fun _ _ => rotation a) :=
  fun z _ => MatrixExponential.vector_derivative_ode (rotation a) (rotation_linear a) initial z

theorem seriesVector_initial (a : Scalar) :
    (seriesVector a).eval zeroScalar trivial ≈ initial :=
  MatrixExponential.value_initial (rotation a) (rotation_linear a) initial

/-- Both independently justified solution calculations agree on the whole
represented complex plane. The proof uses ODE uniqueness, not a sine identity
or coefficient comparison between the two calculations. -/
theorem computations_agree_global (a z : Scalar) :
    (exponentialVector a).eval z trivial ≈ (seriesVector a).eval z trivial :=
  MatrixExponential.constant_ode_entire_unique (rotation a) (rotation_linear a)
    (exponentialVector a) (seriesVector a) (exponentialVector_holomorphic a) (seriesVector_holomorphic a)
    (fun _ => trivial) (fun _ => trivial) (exponentialVector_ode a) (seriesVector_ode a)
    zeroScalar (Setoid.trans (exponentialVector_initial a) (Setoid.symm (seriesVector_initial a))) z

theorem rotation_scaled (a : Scalar) :
    (rotation a).Equiv (OperatorPower.scaled (rotation oneScalar) a) := by
  intro x i
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl | rfl
  · exact equiv_symm (mul_equiv a.property a.property
      (mul_valid oneScalar.property (x.property 1)) (x.property 1)
      (equiv_refl _ a.property) (one_mul_equiv (x.val 1) (x.property 1)))
  · apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((rotation a).eval x).property 1)
      (hright := ((OperatorPower.scaled (rotation oneScalar) a).eval x).property 1)
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let X := ComplexRawQuotient.ofRaw (x.val 0) (x.property 0)
    change -(A*X)=A*(-(1*X))
    grind only

/-- Scaling the frequency is exactly a coordinate pullback, including
arbitrary represented irrational coefficients. -/
theorem seriesVector_reparametrization (a z : Scalar) :
    (seriesVector a).eval z trivial ≈ (seriesVector oneScalar).eval (scalarProduct a z) trivial :=
  Setoid.trans
    (MatrixExponential.value_congr (rotation a) (OperatorPower.scaled (rotation oneScalar) a)
      (rotation_linear a) (OperatorPower.scaled_linear (rotation oneScalar) (rotation_linear oneScalar) a)
      (rotation_scaled a) z z (equiv_refl _ z.property) initial initial (Setoid.refl initial))
    (MatrixExponential.value_scaled_operator (rotation oneScalar) (rotation_linear oneScalar) a z initial)

theorem scaled_sine_agrees_global (a z : Scalar) :
    ((sine a).eval z trivial).val.Equiv
      (((seriesVector oneScalar).eval (scalarProduct a z) trivial).val 0) :=
  Setoid.trans (computations_agree_global a z) (seriesVector_reparametrization a z) 0

end ComputableAnalysis.ElementarySineODE
