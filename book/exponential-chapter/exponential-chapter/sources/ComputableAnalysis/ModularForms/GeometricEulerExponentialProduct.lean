import ComputableAnalysis.ModularForms.GeometricEulerExponentialFactor
import ComputableAnalysis.ModularForms.GeometricRotationEulerMesh
import ComputableAnalysis.ModularForms.ExponentialAddition

/-! Exact finite exponential products for the geometric mesh angular sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def geometricMeshAngle (N : Nat) : Nat → Rat
  | 0 => 0
  | k+1 => geometricMeshStep N*(2/(1+((k:Rat)*geometricMeshStep N)*((k:Rat)*geometricMeshStep N)))+
      geometricMeshAngle N k

def geometricMeshAngleScalar (N k : Nat) : Scalar :=
  ⟨ofQComplex ⟨0,geometricMeshAngle N k⟩,ofQComplex_valid _⟩

def geometricExponentialProduct (N : Nat) : Nat → ComplexRaw
  | 0 => ofQComplex QComplex.one
  | k+1 => mul (entireExponentialValue
      (geometricAngularIncrement ((k:Rat)*geometricMeshStep N) (geometricMeshStep N))).val
      (geometricExponentialProduct N k)

theorem geometricExponentialProduct_valid (N k : Nat) : (geometricExponentialProduct N k).Valid := by
  induction k with
  | zero => exact ofQComplex_valid _
  | succ k ih => exact mul_valid (entireExponentialValue _).property ih

theorem geometricMeshAngleScalar_succ (N k : Nat) :
    (add (geometricAngularIncrement ((k:Rat)*geometricMeshStep N) (geometricMeshStep N)).val
      (geometricMeshAngleScalar N k).val).Equiv (geometricMeshAngleScalar N (k+1)).val := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  simp only [geometricAngularIncrement,geometricMeshAngleScalar,geometricMeshAngle,add,ofQComplex,
    QBox.add,QBox.point,QComplex.add,QBox.Overlaps,QComplex.le_def]
  constructor <;> constructor <;> grind

theorem geometricExponentialProduct_angle (N k : Nat) :
    (geometricExponentialProduct N k).Equiv (entireExponentialValue (geometricMeshAngleScalar N k)).val := by
  induction k with
  | zero => exact equiv_symm entireExponential_zero
  | succ k ih =>
    let x := geometricAngularIncrement ((k:Rat)*geometricMeshStep N) (geometricMeshStep N)
    let a := geometricMeshAngleScalar N k
    let b : Scalar := ⟨add x.val a.val,add_valid x.property a.property⟩
    have hm := mul_equiv (entireExponentialValue x).property (entireExponentialValue x).property
      (geometricExponentialProduct_valid N k) (entireExponentialValue a).property
      (equiv_refl _ (entireExponentialValue x).property) ih
    exact equiv_trans (geometricExponentialProduct_valid N (k+1))
      (mul_valid (entireExponentialValue x).property (entireExponentialValue a).property)
      (entireExponentialValue (geometricMeshAngleScalar N (k+1))).property hm
      (equiv_trans (mul_valid (entireExponentialValue x).property (entireExponentialValue a).property)
        (entireExponentialValue b).property (entireExponentialValue (geometricMeshAngleScalar N (k+1))).property
        (entireExponential_addition x a)
        (entireExponentialValue_congr b (geometricMeshAngleScalar N (k+1)) (geometricMeshAngleScalar_succ N k)))

theorem geometricRotationSpeed_nonnegative (t : Rat) : 0 ≤ 2/(1+t*t) := by
  have ht : 0 ≤ t*t := by
    by_cases h : 0 ≤ t
    · exact Rat.mul_nonneg h h
    · have hn : 0 ≤ -t := by grind
      have hp := Rat.mul_nonneg hn hn
      grind only
  have hd : 0 < 1+t*t := by grind
  exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hd))

theorem geometricMeshAngle_bounds (N k : Nat) :
    0 ≤ geometricMeshAngle N k ∧
    geometricMeshAngle N k ≤ 2*(k:Rat)*geometricMeshStep N := by
  induction k with
  | zero => simp [geometricMeshAngle]
  | succ k ih =>
    have hh := Rat.le_of_lt (geometricMeshStep_positive N)
    have hn := geometricRotationSpeed_nonnegative ((k:Rat)*geometricMeshStep N)
    have hu := Rat.le_trans (self_le_qabs (2/(1+((k:Rat)*geometricMeshStep N)*
      ((k:Rat)*geometricMeshStep N))))
      (geometricRotationSpeed_bound ((k:Rat)*geometricMeshStep N))
    have hpn := Rat.mul_nonneg hh hn
    have hpu := Rat.mul_le_mul_of_nonneg_left hu hh
    simp only [geometricMeshAngle, Rat.natCast_add] at *
    have hone : ((1:Nat):Rat)=1 := by decide
    rw [hone]
    constructor <;> grind only

theorem geometricMeshAngle_endpoint_bounds (N : Nat) :
    0 ≤ geometricMeshAngle N (N+1) ∧ geometricMeshAngle N (N+1) ≤ 2 := by
  have hb := geometricMeshAngle_bounds N (N+1)
  have hi := geometricMeshStep_identity N
  constructor
  · exact hb.1
  · have he : 2*((N+1:Nat):Rat)*geometricMeshStep N=2 := by grind only
    rw [he] at hb
    exact hb.2

end ComputableAnalysis.ModularForms
