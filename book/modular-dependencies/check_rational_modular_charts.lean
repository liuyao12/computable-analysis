import ComputableAnalysis.ModularForms.UnitDiskEisensteinCM
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

open ComputableAnalysis ComputableAnalysis.ModularForms ComputableAnalysis.RiemannHilbert

#print axioms DiskLambert.denominator_nonzero
#print axioms DiskLambert.term_bound
#print axioms DiskLambert.majorant_step
#print axioms DiskLambert.prefix_tail
#print axioms DiskLambert.tail_shrinks
#print axioms DiskLambert.prefix_difference
#print axioms EisensteinUnitDisk.rational_mem_iff
#print axioms EisensteinUnitDisk.invariant
#print axioms DiskLambert.rationalValue_valid
#print axioms DiskLambert.radius_independent
#print axioms DiskLambert.rational_lipschitz
#print axioms DiskLambert.value_valid
#print axioms DiskLambert.value_congr
#print axioms DiskLambert.value_rational_agreement
#print axioms DiskLambert.value_legacy_agreement
#print axioms RationalEisenstein.unitDiskRationalRaw_valid
#print axioms RationalEisenstein.unitDiskDerived_rational_agreement
#print axioms RationalEisenstein.unitDiskRational_smallChart_agreement
#print axioms RationalEisenstein.unitDiskDerived_smallChart_agreement
#print axioms RationalEisenstein.sampledEisensteinTwo_original_agreement
#print axioms RationalEisenstein.sampledEisensteinFour_original_agreement
#print axioms RationalEisenstein.sampledEisensteinSix_original_agreement
#print axioms unitDiskCMEisenstein163_agrees
#print axioms unitDiskCMEisenstein43_agrees
#print axioms unitDiskCM163_normalized_fourier_product
#print axioms sampledJ_cm163_exact
#print axioms sampledJ_cm43_exact

-- A genuinely Euclidean point: its coordinate sum is greater than one.
example : RationalEisenstein.unitDiskRationalDomain ⟨3/5,3/5⟩ := by decide +kernel
example : (1:Rat)<QComplex.normBound ⟨3/5,3/5⟩ := by decide +kernel
-- Points arbitrarily close to the circle are accepted, but the circle is excluded.
example : RationalEisenstein.unitDiskRationalDomain ⟨999/1000,0⟩ := by decide +kernel
example : ¬RationalEisenstein.unitDiskRationalDomain ⟨1,0⟩ := by decide +kernel
example : ¬RationalEisenstein.unitDiskRationalDomain ⟨3/5,4/5⟩ := by decide +kernel

#check RationalEisenstein.rationalEisensteinTwo
#check RationalEisenstein.sampledEisensteinFour.eval_congr
#check DiskLambert.sample_inside

-- Independent one-term formula at a point outside the old chart.
def fullDiskFiniteCheck : Bool :=
  decide (RationalLambert.finitePrefix ⟨1/2,0⟩ 5 2=⟨1+(2:Rat)^5/3,0⟩)
#eval fullDiskFiniteCheck

-- Execute the full rational evaluator away from the former radius 1/64.
def fullDiskRationalCheck : Bool :=
  let B := (DiskLambert.rationalValue ⟨1/2,0⟩ 1).compute 1
  decide (B.lo.re≤B.hi.re ∧ B.lo.im≤0 ∧ 0≤B.hi.im)
#eval fullDiskRationalCheck

-- Execute the derived construction, rather than only its fixed-input comparison.
def fullDiskDerivedCheck : Bool :=
  let q := RationalLambert.point ⟨1/2,0⟩
  let hq := EisensteinUnitDisk.rational_mem ⟨1/2,0⟩ (by decide +kernel)
  let B := (DiskLambert.value q hq 1).compute 1
  decide (B.lo.re≤B.hi.re ∧ B.lo.im≤0 ∧ 0≤B.hi.im)
#eval fullDiskDerivedCheck
