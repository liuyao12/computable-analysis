import ComputableAnalysis.DyadicCosineIntegral
import ComputableAnalysis.CosinePrimitiveData

/-!
# Dyadic radicals evaluate the SAME arctangent trigonometry

The ordinary argument is x with C(x)=cos(pi*x). A dyadic quarter-turn grid
has x=j/(2*2^d), not j/2^d. Its endpoint is 1/2. The product below uses
geometric pi, independently of the radical sampler. The integral's executable
samples use radicals only; the identification theorem has proof dependencies
on arctangent which are not part of its numerical instructions.
-/
namespace ComputableAnalysis.DyadicCosinePrimitive
open CosinePrimitive ClosedArctanInverse SinPiIntegral IntervalSelections

/-- Rational input in the original normalization. -/
def gridPoint (d j : Nat) : Rat := DyadicTrigonometry.gridAngle d j / 2

theorem gridPoint_domain (d j : Nat) (hj : j ≤ 2^d) : Domain (gridPoint d j) := by
  have h := DyadicTrigonometry.gridAngle_unit d j hj
  unfold Domain GeometricSineDerivative.OnHalf gridPoint
  have h0 := h.1; have h1 := h.2
  simp only [Rat.div_def]
  constructor <;> grind

/-- All dyadic values agree with the original closed S and C.
No value supplied by a cosine integral identity is used in this bridge. -/
theorem dyadic_values (d j : Nat) (hj : j ≤ 2^d) :
    (DyadicTrigonometry.powerCosine d j).Equiv (C (gridPoint d j)) ∧
    (DyadicTrigonometry.powerSine d j).Equiv (S (gridPoint d j)) := by
  have hx := gridPoint_domain d j hj
  have he : 2 * gridPoint d j = DyadicTrigonometry.gridAngle d j := by
    unfold gridPoint
    simp only [Rat.div_def]
    grind
  simp only [C, S, CosineFTC.cosine, CosineFTC.sine, dif_pos hx]
  change (DyadicTrigonometry.powerCosine d j).Equiv
      (ClockTrigonometry.cosine (2 * gridPoint d j)) ∧
    (DyadicTrigonometry.powerSine d j).Equiv
      (ClockTrigonometry.sine (2 * gridPoint d j))
  rw [he]
  exact DyadicTrigonometry.powers_equiv d j hj

/-- The product combines two independently defined numerical programs. -/
def product : RealRaw := RealRaw.mul CosinePrimitive.pi DyadicCosineIntegral.integral

def Statement : Prop := product.Equiv RealRaw.one

theorem product_valid : product.Valid :=
  RealRaw.mul_valid pi_valid DyadicCosineIntegral.integral_valid

private theorem pi_reciprocal_one :
    (RealRaw.mul CosinePrimitive.pi reciprocalPiRaw).Equiv RealRaw.one := by
  intro n
  let P := CosinePrimitive.pi.compute n
  have hb := CauchyPi.piCircleArea_valid.2.1 0 n (Nat.zero_le n)
  have hz : piCircleArea.compute 0 = ({lo := 2, hi := 4} : QInterval) := by decide +kernel
  rw [hz, ← pi_compute] at hb
  change 2 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ 4 at hb
  have hp : 0 < P.lo := by grind
  have hr : reciprocalPiRaw.compute n = {lo := 1/P.hi, hi := 1/P.lo} := by
    simp only [reciprocalPiRaw]
    rw [← pi_compute]
    change QInterval.inv P = _
    simp only [QInterval.inv, if_pos hp]
  have hpos : 0 < P.hi := by grind
  have hinv := PositiveIntervalInverse.one_div_antitone hp hb.2.1
  have hs : InBox (1/P.lo) (reciprocalPiRaw.compute n) := by
    rw [hr]
    exact ⟨hinv,Rat.le_refl⟩
  have hm := mul_mem (X := CosinePrimitive.pi)
    (Y := reciprocalPiRaw) (n := n)
    (show InBox P.lo (CosinePrimitive.pi.compute n) from ⟨Rat.le_refl,hb.2.1⟩) hs
  have he : P.lo*(1/P.lo)=1 := by
    simp only [Rat.div_def,Rat.one_mul]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hp)
  rw [he] at hm
  exact (RealRaw.compareAt_overlap_iff _ _ n n).2 ⟨hm.1,hm.2⟩

/-- Geometric pi times the radical-only cosine quadrature is one.
The integration interval is [0,1/2] in the existing C normalization. -/
theorem product_eq_one : Statement := by
  have h := RealRaw.mul_equiv pi_valid pi_valid
    DyadicCosineIntegral.integral_valid reciprocalPiRaw_valid
    (RealRaw.equiv_refl _ pi_valid) DyadicCosineIntegral.integral_equiv_reciprocalPi
  exact RealRaw.equiv_trans product_valid
    (RealRaw.mul_valid pi_valid reciprocalPiRaw_valid) (RealRaw.ofRat_valid 1)
    h pi_reciprocal_one

end ComputableAnalysis.DyadicCosinePrimitive
