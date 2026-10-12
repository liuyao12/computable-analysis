import ComputableAnalysis.ModularForms.RationalModularCM
open ComputableAnalysis ComputableAnalysis.ModularForms ComputableAnalysis.RiemannHilbert

#check rationalNomeChart_valid
#check sampledNomeChart_rational_agreement
#check sampledNome.eval_congr
#check sampledNome_holomorphic
#check RationalEisenstein.rationalEisensteinTwo
#check RationalEisenstein.rationalEisensteinFour
#check RationalEisenstein.rationalEisensteinSix
#check (RationalEisenstein.derivedMap .four).eval_congr
#check RationalEisenstein.derivedMap_holomorphic
#check RationalEisenstein.sampledEisensteinTwo_original_agreement
#check RationalEisenstein.sampledEisensteinFour_original_agreement
#check RationalEisenstein.sampledEisensteinSix_original_agreement

#print axioms rationalNomeChart_valid
#print axioms sampledNomeChartValue_agrees
#print axioms sampledNomeChart_rational_agreement
#print axioms sampledNomeValue_agrees
#print axioms sampledNome_holomorphic
#print axioms RationalLambert.denominator_nonzero
#print axioms RationalLambert.prefix_agrees
#print axioms RationalLambert.difference_bound
#print axioms RationalLambert.rationalValue_valid
#print axioms RationalLambert.rationalValue_agrees
#print axioms RationalLambert.sample_inside
#print axioms RationalLambert.input_error
#print axioms RationalLambert.comparison_close
#print axioms RationalLambert.value_valid
#print axioms RationalLambert.value_agrees
#print axioms RationalEisenstein.rationalRaw_valid
#print axioms RationalEisenstein.derivedValue_agrees
#print axioms RationalEisenstein.derived_rational_agreement
#print axioms RationalEisenstein.derivedMap_holomorphic
#print axioms sampledNome_cm163_exact
#print axioms sampledNome_cm43_exact
#print axioms sampledCMEisenstein163_agrees
#print axioms sampledCMEisenstein43_agrees
#print axioms sampledCM163_normalized_fourier_product

-- A two-term check of each exact rational Lambert prefix, using a closed
-- rational formula independently of the recursive evaluator.
def lambertPrefixCheck (k : Nat) : Bool :=
  let q : QComplex := ⟨1/128,0⟩
  let expected : QComplex := ⟨1/127+(2:Rat)^k/16383,0⟩
  decide (RationalLambert.finitePrefix q k 2 = expected)
#eval lambertPrefixCheck 1
#eval lambertPrefixCheck 3
#eval lambertPrefixCheck 5

-- The generic derived sampler, not only its rational comparison, executes.
def derivedLambertZeroCheck : Bool :=
  let q : RiemannHilbert.Scalar := ⟨ComplexRaw.zero,ComplexRaw.ofQComplex_valid _⟩
  let hq : wideLambertFifthDomain q := ⟨0,by decide +kernel,by decide +kernel,FunctionTheory.Small.zero (by decide +kernel)⟩
  let b := (RationalLambert.sampledPrefix q hq 5 4).compute 0
  decide (b.lo = QComplex.zero ∧ b.hi = QComplex.zero)
#eval derivedLambertZeroCheck

example : (sampledNomeValue cmScalar43 cmPoint43_upper).val.Equiv
    (ComplexRaw.neg (sampledNomeChartValue cmDecayExponent43).val) := sampledNome_cm43_exact
example : (sampledJValue cmScalar163 cmPoint163_upper).val.Equiv
    (ComplexRaw.ofQComplex ⟨-640320^3,0⟩) := sampledJ_cm163_exact
