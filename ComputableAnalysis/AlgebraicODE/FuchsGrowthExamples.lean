import ComputableAnalysis.AlgebraicODE.FuchsGrowth
import ComputableAnalysis.DifferentialReciprocal

namespace ComputableAnalysis.AlgebraicODE.Fuchs.Growth
open LinearODE DiscreteLinearSystem FinitePolynomial

/-- The reciprocal solution of `z²y''+2zy'=0`, with its scaled jet. -/
def reciprocalJet (t : Rat) : RatVector 4 :=
  jetVector (QComplex.ofRat (1/t)) (QComplex.ofRat (-1/t))

def reciprocalRadius (a _b : Rat) (eps : QPos) : QPos :=
  if ha : 0 < a then
    ⟨eps.val/(2*(positiveReciprocalErrorCoefficient a+1)), by
      have hC := positiveReciprocalErrorCoefficient_nonneg ha
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind))⟩
  else ⟨1, by decide⟩

theorem reciprocal_residual {R : Rat} :
    ∀ a b (eps : QPos) x h,
      0 < a → a ≤ x → x ≤ b → a ≤ x+h → x+h ≤ b → b ≤ R →
      h ≠ 0 → qabs h ≤ (reciprocalRadius a b eps).val →
      vectorAbsSum (fun i => reciprocalJet (x+h) i-reciprocalJet x i-
        h*matrixApply (rayMatrix [QComplex.ofRat 2] [] QComplex.one x)
          (reciprocalJet x) i) ≤ eps.val*qabs h := by
  intro a b eps x h ha hax hxb haxh hxhb _ hh hdelta
  let C := positiveReciprocalErrorCoefficient a
  have hC : 0 ≤ C := positiveReciprocalErrorCoefficient_nonneg ha
  have hsec := (positiveReciprocalCenteredSecantBound a b ha (by grind)).error_bound
    x h hh
    (by apply qabs_le_of_neg_le_le <;> grind)
    (by apply qabs_le_of_neg_le_le <;> grind)
  change qabs ((1/(x+h)-1/x)/h- -(1/x^2)) ≤ qabs h*C at hsec
  have hr : 1/(x+h)-1/x+h*(1/x^2) =
      h*((1/(x+h)-1/x)/h- -(1/x^2)) := by
    have hc := FormalPowerSeries.mul_div_cancel_left (a := h) (b := 1/(x+h)-1/x) hh
    grind
  have hrb := Rat.mul_le_mul_of_nonneg_left hsec (qabs_nonneg h)
  rw [← qabs_mul, ← hr] at hrb
  have hid : (fun i => reciprocalJet (x+h) i-reciprocalJet x i-
      h*matrixApply (rayMatrix [QComplex.ofRat 2] [] QComplex.one x)
        (reciprocalJet x) i) =
      (fun i : Fin 4 => if i.val = 0 then 1/(x+h)-1/x+h*(1/x^2)
        else if i.val = 2 then -(1/(x+h)-1/x+h*(1/x^2)) else 0) := by
    funext i
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
      have := i.isLt
      omega
    rcases hi with hi | hi | hi | hi <;>
      simp [reciprocalJet, rayMatrix, companion, jetVector, matrixApply,
        matrixScale, finiteSum, CPoly.eval, QComplex.add, QComplex.mul,
        QComplex.zero, QComplex.ofRat, Rat.div_def, Rat.pow_succ,
        Rat.inv_mul_rev, hi] <;> grind
  rw [hid]
  change qabs (1/(x+h)-1/x+h*(1/x^2)) +
    (qabs 0 + (qabs (-(1/(x+h)-1/x+h*(1/x^2))) + (qabs 0+0))) ≤ _
  rw [qabs_neg, show qabs (0 : Rat) = 0 by decide +kernel]
  have hd : qabs h ≤ eps.val/(2*(C+1)) := by
    simpa [reciprocalRadius, ha, C] using hdelta
  have hK : 0 < 2*(C+1) := by grind
  have hcancel : 2*(C+1)*(eps.val/(2*(C+1))) = eps.val :=
    FormalPowerSeries.mul_div_cancel_left (Rat.ne_of_gt hK)
  have hmul := Rat.mul_le_mul_of_nonneg_left hd (Rat.le_of_lt hK)
  have hsq := Rat.mul_nonneg (qabs_nonneg h) (qabs_nonneg h)
  have hfinal := Rat.mul_le_mul_of_nonneg_right hmul (qabs_nonneg h)
  rw [hcancel] at hfinal
  have htwice := Rat.mul_le_mul_of_nonneg_left hrb (show (0 : Rat) ≤ 2 by decide)
  clear hsec hr hid hd hcancel hmul hdelta
  dsimp only [C] at *
  grind only

def reciprocalSolution (R : Rat) : RaySolution [QComplex.ofRat 2] [] QComplex.one R :=
  LinearSolution.ofExact reciprocalJet reciprocalRadius reciprocal_residual

/-- An actual pole-bearing solution satisfies the theorem; growth is not a
field supplied when constructing the solution. -/
theorem reciprocal_moderate {a : Rat} (ha : 0 < a) (ha1 : a ≤ 1) :
    NormBound ((reciprocalSolution 1).value a) (4/a^4) := by
  have hg := fuchs_ray_moderate [QComplex.ofRat 2] [] QComplex.one
    (reciprocalSolution 1) ha ha1 (Rat.le_refl (a := 1))
  have he : exponent [QComplex.ofRat 2] [] QComplex.one 1 = 4 := by decide +kernel
  have hn : normCeiling ((reciprocalSolution 1).value 1) 0 = 4 := by decide +kernel
  simpa [he, hn, Rat.pow_succ] using hg

end ComputableAnalysis.AlgebraicODE.Fuchs.Growth
