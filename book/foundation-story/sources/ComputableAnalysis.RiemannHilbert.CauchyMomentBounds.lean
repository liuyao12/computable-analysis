import ComputableAnalysis.CauchyTaylorCoefficients
import ComputableAnalysis.RiemannHilbert.BoxApproximation
import ComputableAnalysis.RiemannHilbert.GeneralSeries
import ComputableAnalysis.RiemannHilbert.RationalReciprocal

/-! Fixed represented Cauchy moments inherit a uniform coefficient bound
from the mass of their rational quadrature rules. -/
namespace ComputableAnalysis.RiemannHilbert.CauchyMoments
open ComplexRaw FunctionTheory LocalODE CauchyTaylor
set_option autoImplicit false

theorem direction_power_bound (p : Node) (k : Nat) :
    QComplex.normBound (QComplex.natPow p.direction k) ≤ 2 := by
  have hu : QComplex.normSq (QComplex.natPow p.direction k)=1 := by
    induction k with
    | zero => change QComplex.normSq QComplex.one=1; decide +kernel
    | succ k ih => rw [QComplex.natPow,QComplex.normSq_mul,ih,p.unit]; decide +kernel
  have hb := disk_coordinates (z := QComplex.natPow p.direction k)
    (r := 1) (by decide) (by change QComplex.normSq (QComplex.natPow p.direction k) ≤ 1*1; rw [hu]; decide +kernel)
  unfold QComplex.normBound qabs
  split <;> split <;> grind only

theorem sample_bound (ps : Rule) (k : Nat) :
    QComplex.normBound (coefficientSample ps k) ≤ 2*mass ps := by
  induction ps with
  | nil => change QComplex.normBound QComplex.zero ≤ 2*0; decide +kernel
  | cons p ps ih =>
    have ha := l1_add (QComplex.mul p.weight (QComplex.natPow p.direction k)) (coefficientSample ps k)
    have hm := l1_mul p.weight (QComplex.natPow p.direction k)
    have hb := Rat.mul_le_mul_of_nonneg_left (direction_power_bound p k) (l1_nonneg p.weight)
    change QComplex.normBound (QComplex.add (QComplex.mul p.weight (QComplex.natPow p.direction k))
      (coefficientSample ps k)) ≤ 2*(QComplex.normBound p.weight+mass ps)
    grind only

theorem coefficient_bound {rules : Nat → Rule} (m : Moments rules) (B : Rat)
    (hm : ∀ n, mass (rules n) ≤ B) (k : Nat) : Small (m.coefficient k) (2*B) := by
  have hb (n : Nat) := l1_coordinates (Rat.le_trans (sample_bound (rules n) k)
    (Rat.mul_le_mul_of_nonneg_left (hm n) (by decide : (0 : Rat) ≤ 2)))
  refine ⟨?_,?_,?_,?_⟩
  · intro n j
    have h := (m.coefficient_contains_sample k j).2.1
    change -(2*B) ≤ ((m.coefficient k).compute j).hi.re
    change (coefficientSample (rules j) k).re ≤ ((m.coefficient k).compute j).hi.re at h
    grind only [hb j]
  · intro j n
    have h := (m.coefficient_contains_sample k j).1.1
    change ((m.coefficient k).compute j).lo.re ≤ 2*B
    change ((m.coefficient k).compute j).lo.re ≤ (coefficientSample (rules j) k).re at h
    grind only [hb j]
  · intro n j
    have h := (m.coefficient_contains_sample k j).2.2
    change -(2*B) ≤ ((m.coefficient k).compute j).hi.im
    change (coefficientSample (rules j) k).im ≤ ((m.coefficient k).compute j).hi.im at h
    grind only [hb j]
  · intro j n
    have h := (m.coefficient_contains_sample k j).1.2
    change ((m.coefficient k).compute j).lo.im ≤ 2*B
    change ((m.coefficient k).compute j).lo.im ≤ (coefficientSample (rules j) k).im at h
    grind only [hb j]

theorem one_power (k : Nat) : (1 : Rat)^k=1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Rat.pow_succ,ih,Rat.one_mul]

theorem certificate_bound {F : QComplex → ComplexRaw} (c : SeriesCertificate F) (k : Nat) :
    Small (c.coefficient k) ((2*c.cauchy.massBound)*(1 : Rat)^k) := by
  rw [one_power,Rat.mul_one]
  exact coefficient_bound c.moments c.cauchy.massBound c.cauchy.mass_le k

theorem rational_power (q : QComplex) (k : Nat) :
    (power (ofQComplex q) k).Equiv (ofQComplex (QComplex.natPow q k)) := by
  induction k with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ k ih =>
    exact equiv_trans (power_valid _ (ofQComplex_valid _) (k+1))
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
      (mul_equiv (power_valid _ (ofQComplex_valid _) k) (ofQComplex_valid _)
        (ofQComplex_valid _) (ofQComplex_valid _) ih (equiv_refl _ (ofQComplex_valid _)))
      (RationalReciprocal.raw_mul_constants _ _)

theorem rational_prefix {rules : Nat → Rule} (m : Moments rules) (q : QComplex) (N : Nat) :
    (BoundedSeries.valueBlock m.coefficient (ofQComplex q) 0 N).Equiv (m.partialSum q N) := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    rw [BoundedSeries.valueBlock.eq_2,Moments.partialSum.eq_2,Nat.zero_add]
    change (add (BoundedSeries.valueBlock m.coefficient (ofQComplex q) 0 N)
      (mul (m.coefficient N) (power (ofQComplex q) N))).Equiv
      (add (m.partialSum q N) (mul (m.coefficient N) (ofQComplex (QComplex.natPow q N))))
    exact add_equiv ih (mul_equiv (m.coefficient_valid N) (m.coefficient_valid N)
      (power_valid _ (ofQComplex_valid _) N) (ofQComplex_valid _)
      (equiv_refl _ (m.coefficient_valid N)) (rational_power q N))

end ComputableAnalysis.RiemannHilbert.CauchyMoments
