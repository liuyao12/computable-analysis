import ComputableAnalysis.RiemannHilbert.ExponentialMajorant
import ComputableAnalysis.RiemannHilbert.LocalCoefficientFunction

/-! A represented matrix exponential on the whole complex plane. Every finite
disc gets a constructed geometric rate and prefactor; comparisons prove that
neither these bounds nor the names of the operator and argument affect values. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}

def rate (R : Rat) : Rat := 1/(16*(R+1))

theorem rate_pos (R : Rat) (hR : 0 ≤ R) : 0 < rate R := by
  unfold rate
  rw [Rat.div_def, Rat.one_mul]
  exact (Rat.inv_pos).2 (Rat.mul_pos (by decide) (by grind))

theorem rate_small (R : Rat) (hR : 0 ≤ R) : 8*rate R*R ≤ (1 : Rat)/2 := by
  have hd : 0 < 16*(R+1) := Rat.mul_pos (by decide) (by grind)
  have he : rate R*(16*(R+1)) = 1 := by
    exact Rat.div_mul_cancel (Rat.ne_of_gt hd)
  apply Rat.le_of_mul_le_mul_right (c := 16*(R+1))
  · calc
      _ = 8*R := by calc
        _ = 8*R*(rate R*(16*(R+1))) := by grind
        _ = _ := by rw [he, Rat.mul_one]
      _ ≤ _ := by grind
  · exact hd

def discBudget (A : ValueMap (Fiber n) (Fiber n)) (R : Rat) : Rat :=
  geometricBudget (ValueMap.linearBound A) (rate R)

theorem discBudget_nonneg (A : ValueMap (Fiber n) (Fiber n)) (R : Rat) : 0 ≤ discBudget A R :=
  geometricBudget_nonneg _ _

theorem disc_majorant (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : Rat) (hR : 0 ≤ R) : OperatorMajorant (coefficientMap A) (discBudget A R) (rate R) :=
  coefficientMap_majorant A hA (rate R) (rate_pos R hR)

def onDisc (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (R : QPos)
    (z : Scalar) (hz : interior R.val z) : ValueMap (Fiber n) (Fiber n) :=
  operatorValue (coefficientMap A) z (discBudget A R.val) (rate R.val) R.val
    (discBudget_nonneg A R.val) (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))
    (Rat.le_of_lt R.property) (disc_majorant A hA R.val (Rat.le_of_lt R.property))
    (interior_bound R.val z hz)
    (by have := rate_small R.val (Rat.le_of_lt R.property)
        have := Rat.mul_nonneg (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))
          (Rat.le_of_lt R.property)
        grind)

theorem onDisc_linear (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (z : Scalar) (hz : interior R.val z) : IsLinear (onDisc A hA R z hz) :=
  operatorValue_linear (coefficientMap A) (coefficientMap_linear A hA) z
    (discBudget A R.val) (rate R.val) R.val
    (discBudget_nonneg A R.val) (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))
    (Rat.le_of_lt R.property) (disc_majorant A hA R.val (Rat.le_of_lt R.property))
    (interior_bound R.val z hz)
    (by have := rate_small R.val (Rat.le_of_lt R.property)
        have := Rat.mul_nonneg (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))
          (Rat.le_of_lt R.property)
        grind)

theorem onDisc_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : A.Equiv B) (R S : QPos) (z w : Scalar)
    (hz : interior R.val z) (hw : interior S.val w) (hzw : z.val.Equiv w.val)
    (x y : Fiber n) (hxy : x ≈ y) :
    (onDisc A hA R z hz).eval x ≈ (onDisc B hB S w hw).eval y :=
  VectorSeries.value_congr _ _ z w (coefficient_congr A B hAB x y hxy) hzw
    (2*discBudget A R.val*LocalSystem.initialBound x) (rate R.val) R.val
    (2*discBudget B S.val*LocalSystem.initialBound y) (rate S.val) S.val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (discBudget_nonneg A R.val)) (LocalSystem.initialBound_nonneg x))
    (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property))) (Rat.le_of_lt R.property)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (discBudget_nonneg B S.val)) (LocalSystem.initialBound_nonneg y))
    (Rat.le_of_lt (rate_pos S.val (Rat.le_of_lt S.property))) (Rat.le_of_lt S.property)
    (operatorCoefficient_bound (coefficientMap A) _ _ _ (LocalSystem.initialBound_nonneg x)
      (disc_majorant A hA R.val (Rat.le_of_lt R.property)) x (LocalSystem.initialBound_valid x))
    (operatorCoefficient_bound (coefficientMap B) _ _ _ (LocalSystem.initialBound_nonneg y)
      (disc_majorant B hB S.val (Rat.le_of_lt S.property)) y (LocalSystem.initialBound_valid y))
    (interior_bound R.val z hz) (interior_bound S.val w hw)
    (by have := rate_small R.val (Rat.le_of_lt R.property)
        have := Rat.mul_nonneg (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))
          (Rat.le_of_lt R.property)
        grind)
    (by have := rate_small S.val (Rat.le_of_lt S.property)
        have := Rat.mul_nonneg (Rat.le_of_lt (rate_pos S.val (Rat.le_of_lt S.property)))
          (Rat.le_of_lt S.property)
        grind)

def pointRadius (z : Scalar) : QPos :=
  ⟨LocalODE.initialBound z.val+1, by have := LocalODE.initialBound_nonneg z.val; grind⟩

theorem pointRadius_inside (z : Scalar) : interior (pointRadius z).val z :=
  ⟨LocalODE.initialBound z.val, LocalODE.initialBound_nonneg z.val, by grind [pointRadius],
    LocalODE.initialBound_valid z.val z.property⟩

/-- An executable evaluator for arbitrary valid represented arguments. All
precision schedules and disc bounds are chosen internally. -/
def value (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (z : Scalar) :
    ValueMap (Fiber n) (Fiber n) := onDisc A hA (pointRadius z) z (pointRadius_inside z)

theorem value_linear (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (z : Scalar) :
    IsLinear (value A hA z) := onDisc_linear A hA _ _ _

theorem value_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : A.Equiv B) (z w : Scalar) (hzw : z.val.Equiv w.val)
    (x y : Fiber n) (hxy : x ≈ y) : (value A hA z).eval x ≈ (value B hB w).eval y :=
  onDisc_congr A B hA hB hAB _ _ z w _ _ hzw x y hxy

theorem value_onDisc (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (z : Scalar) (hz : interior R.val z) (x : Fiber n) :
    (value A hA z).eval x ≈ (onDisc A hA R z hz).eval x :=
  onDisc_congr A A hA hA (fun _ => Setoid.refl _) _ R z z _ hz
    (equiv_refl _ z.property) x x (Setoid.refl _)

theorem onDisc_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (z : Scalar) (hz : interior R.val z) (E : Rat) (hE : 0 ≤ E)
    (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((onDisc A hA R z hz).eval x) (8*discBudget A R.val*E) :=
  operatorValue_bound (coefficientMap A) z _ _ _ E (discBudget_nonneg A R.val)
    (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property))) (Rat.le_of_lt R.property) hE
    (disc_majorant A hA R.val (Rat.le_of_lt R.property)) (interior_bound R.val z hz)
    (by have := rate_small R.val (Rat.le_of_lt R.property)
        have := Rat.mul_nonneg (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))
          (Rat.le_of_lt R.property)
        grind) x hx

theorem value_disc_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (z : Scalar) (hz : interior R.val z) (E : Rat) (hE : 0 ≤ E)
    (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((value A hA z).eval x) (8*discBudget A R.val*E) :=
  bound_congr (Setoid.symm (value_onDisc A hA R z hz x)) (onDisc_bound A hA R z hz E hE x hx)

def finitePrefix (A : ValueMap (Fiber n) (Fiber n)) (z : Scalar) (N : Nat) : ValueMap (Fiber n) (Fiber n) :=
  operatorPrefixMap (coefficientMap A) z N

theorem prefix_linear (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (z : Scalar) (N : Nat) :
    IsLinear (finitePrefix A z N) := operatorPrefixMap_linear _ (coefficientMap_linear A hA) z N

theorem value_prefix_close (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (z : Scalar) (hz : interior R.val z) (E : Rat) (hE : 0 ≤ E)
    (x : Fiber n) (hx : CoordinateBound x E) (N : Nat) :
    CoordinateBound (Fiber.sub ((value A hA z).eval x) ((finitePrefix A z N).eval x))
      (8*discBudget A R.val*E*(2*rate R.val*R.val)^N) := by
  have hs := operatorValue_close (coefficientMap A) z (discBudget A R.val) (rate R.val) R.val E
    (discBudget_nonneg A R.val) (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))
    (Rat.le_of_lt R.property) hE (disc_majorant A hA R.val (Rat.le_of_lt R.property))
    (interior_bound R.val z hz)
    (by have := rate_small R.val (Rat.le_of_lt R.property)
        have := Rat.mul_nonneg (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))
          (Rat.le_of_lt R.property)
        grind) x hx N
  exact bound_congr (Fiber.sub_congr (Setoid.symm (value_onDisc A hA R z hz x)) (Setoid.refl _)) hs

theorem prefix_error_shrinks (A : ValueMap (Fiber n) (Fiber n)) (R : QPos)
    (E : Rat) (hE : 0 ≤ E) :
    ShrinksToZero (fun N => 8*discBudget A R.val*E*(2*rate R.val*R.val)^N) :=
  operatorError_shrinks (discBudget A R.val) E (rate R.val) R.val
    (discBudget_nonneg A R.val) hE (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))
    (Rat.le_of_lt R.property)
    (by have := rate_small R.val (Rat.le_of_lt R.property)
        have := Rat.mul_nonneg (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))
          (Rat.le_of_lt R.property)
        grind)

end ComputableAnalysis.RiemannHilbert.MatrixExponential
