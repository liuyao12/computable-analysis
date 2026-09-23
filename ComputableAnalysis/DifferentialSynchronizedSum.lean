import ComputableAnalysis.FiniteDerivativeLimit

/-!
# Addition of independently scheduled represented derivatives

Nestedness permits evaluator schedules to be refined, at a threefold error
cost. This makes derivative addition automatic even when the two original
certificates use different step and runtime precision schedules.
-/

namespace ComputableAnalysis
namespace QInterval

private theorem differenceQuotient_contains_of_contains
    {A B A' B' : QInterval} (hA : A.ContainsInterval A')
    (hB : B.ContainsInterval B') (h : Rat) :
    (differenceQuotient B A h).ContainsInterval (differenceQuotient B' A' h) := by
  have hleft : B.lo - A.hi <= B'.lo - A'.hi := by
    rcases hA with ⟨_, ha⟩; rcases hB with ⟨hb, _⟩; grind
  have hright : B'.hi - A'.lo <= B.hi - A.lo := by
    rcases hA with ⟨ha, _⟩; rcases hB with ⟨_, hb⟩; grind
  unfold differenceQuotient divRat scaleRat
  split
  · exact ⟨Rat.mul_le_mul_of_nonneg_left hleft ‹0 <= 1 / h›,
      Rat.mul_le_mul_of_nonneg_left hright ‹0 <= 1 / h›⟩
  · have hn : 1 / h <= 0 := Rat.le_of_lt (Rat.not_le.mp ‹¬0 <= 1 / h›)
    exact ⟨rat_mul_le_mul_of_nonpos_left hright hn,
      rat_mul_le_mul_of_nonpos_left hleft hn⟩

/-- Independently shrinking two near intervals costs at most three times the
original tolerance: their original gap plus their two original widths. -/
theorem nearAt_refine {A B A' B' : QInterval} {eps delta : QPos}
    (h : A.NearAt B eps) (hA : A.ContainsInterval A') (hB : B.ContainsInterval B')
    (ha : A'.lo <= A'.hi) (hb : B'.lo <= B'.hi)
    (hbudget : 3 * eps.val <= delta.val) : A'.NearAt B' delta := by
  rcases h with ⟨h1, h2, h3, h4⟩
  rcases hA with ⟨ha1, ha2⟩
  rcases hB with ⟨hb1, hb2⟩
  have he := eps.property
  unfold NearAt width at *
  constructor
  · grind
  constructor
  · grind
  constructor <;> grind

end QInterval

namespace HasDerivativeOnInterval

/-- Refine the two schedules of any represented derivative, paying for
independently shrinking its secant and derivative boxes. -/
def refineSchedules {f df : FunctionOnInterval} (D : HasDerivativeOnInterval f df)
    (inner step : Nat → Nat) (eval : Rat → Rat → Nat → Nat)
    (hprecision : ∀ n, 3 * (precisionAtStage (inner n)).val <= (precisionAtStage n).val)
    (hstep : ∀ n, 1 / ((step n : Nat) : Rat) <=
      1 / ((D.stepPrecision (inner n) : Nat) : Rat))
    (heval : ∀ x h n, D.evalPrecision x h (inner n) <= eval x h n) :
    HasDerivativeOnInterval f df where
  same_lower := D.same_lower
  same_upper := D.same_upper
  stepPrecision := step
  evalPrecision := eval
  close := by
    intro x h n hx hxh hdx hh hsmall
    have ho := D.close x h (inner n) hx hxh hdx hh (Rat.le_trans hsmall (hstep n))
    have hA := (f.valid_on x (f.defined_on x hx)).2.1
      (D.evalPrecision x h (inner n)) (eval x h n) (heval x h n)
    have hB := (f.valid_on (x + h) (f.defined_on (x + h) hxh)).2.1
      (D.evalPrecision x h (inner n)) (eval x h n) (heval x h n)
    have hD := (df.valid_on x (df.defined_on x hdx)).2.1
      (D.evalPrecision x h (inner n)) (eval x h n) (heval x h n)
    have hQ := QInterval.differenceQuotient_contains_of_contains
      ⟨hA.1, hA.2.2⟩ ⟨hB.1, hB.2.2⟩ h
    have ha : (f.compute x hx (eval x h n)).lo <= (f.compute x hx (eval x h n)).hi := hA.2.1
    have hb : (f.compute (x + h) hxh (eval x h n)).lo <= (f.compute (x + h) hxh (eval x h n)).hi := hB.2.1
    have hqo : (QInterval.differenceQuotient
        (f.compute (x + h) hxh (eval x h n))
        (f.compute x hx (eval x h n)) h).lo <=
      (QInterval.differenceQuotient
        (f.compute (x + h) hxh (eval x h n))
        (f.compute x hx (eval x h n)) h).hi := by
      unfold QInterval.differenceQuotient QInterval.divRat QInterval.scaleRat
      split
      · apply Rat.mul_le_mul_of_nonneg_left _ ‹0 <= 1 / h›
        change _ - _ <= _ - _
        grind
      · apply rat_mul_le_mul_of_nonpos_left _ (Rat.le_of_lt (Rat.not_le.mp ‹¬0 <= 1 / h›))
        change _ - _ <= _ - _
        grind
    exact QInterval.nearAt_refine ho hQ ⟨hD.1, hD.2.2⟩ hqo hD.2.1 (hprecision n)

private theorem reciprocal_product_le_left (m n : Nat) :
    1 / (((m * n : Nat) : Rat)) <= 1 / ((m : Nat) : Rat) := by
  by_cases hm : m = 0
  · subst m
    simp only [Nat.zero_mul]
    exact Rat.le_refl
  have hmp : (0 : Rat) < (m : Rat) := Rat.natCast_pos.mpr (Nat.pos_of_ne_zero hm)
  by_cases hn : n = 0
  · subst n
    rw [Nat.mul_zero, show 1 / (((0 : Nat) : Rat)) = (0 : Rat) by decide +kernel]
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 hmp)
  have hnp : (0 : Rat) < (n : Rat) := Rat.natCast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnp1 : (1 : Rat) <= (n : Rat) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hprod := Rat.mul_pos hmp hnp
  have hc1 := Rat.mul_inv_cancel (m : Rat) (Rat.ne_of_gt hmp)
  have hc2 := Rat.mul_inv_cancel ((m : Rat) * (n : Rat)) (Rat.ne_of_gt hprod)
  have hle := Rat.mul_le_mul_of_nonneg_left hnp1 (Rat.le_of_lt hmp)
  rw [Rat.natCast_mul]
  apply Rat.le_of_mul_le_mul_left (c := (m : Rat) * ((m : Rat) * (n : Rat)))
  · simp only [Rat.div_def, Rat.one_mul]
    calc
      (m : Rat) * ((m : Rat) * (n : Rat)) * ((m : Rat) * (n : Rat))⁻¹ = (m : Rat) := by
        rw [Rat.mul_assoc, hc2, Rat.mul_one]
      _ <= (m : Rat) * (n : Rat) := by simpa only [Rat.mul_one] using hle
      _ = (m : Rat) * ((m : Rat) * (n : Rat)) * (m : Rat)⁻¹ := by
        rw [Rat.mul_comm (m : Rat) ((m : Rat) * (n : Rat)), Rat.mul_assoc, hc1, Rat.mul_one]
  · exact Rat.mul_pos hmp hprod

private def refinementStage (n : Nat) : Nat := 2 * (2 * (n + 1) + 1)

private theorem refinementStage_budget (n : Nat) :
    3 * (precisionAtStage (refinementStage n)).val <= (precisionAtStage n).val := by
  have ha := precisionAtStage_scaleRat_two n
  have hb := precisionAtStage_scaleRat_two (2 * (n + 1))
  have hp := (precisionAtStage (refinementStage n)).property
  change 2 * (precisionAtStage (refinementStage n)).val <= _ at hb
  grind

/-- Addition needs no compatibility assumptions on the original schedules. -/
def add {f g df dg : FunctionOnInterval}
    (F : HasDerivativeOnInterval f df) (G : HasDerivativeOnInterval g dg)
    (hlo : f.lower = g.lower) (hhi : f.upper = g.upper) :
    HasDerivativeOnInterval (FunctionOnInterval.add f g hlo hhi)
      (FunctionOnInterval.add df dg
        (by rw [F.same_lower, G.same_lower]; exact hlo)
        (by rw [F.same_upper, G.same_upper]; exact hhi)) := by
  let step := fun n => F.stepPrecision (refinementStage n) * G.stepPrecision (refinementStage n)
  let eval := fun x h n => max (F.evalPrecision x h (refinementStage n))
    (G.evalPrecision x h (refinementStage n))
  let F' := F.refineSchedules refinementStage step eval refinementStage_budget
    (fun n => reciprocal_product_le_left _ _) (fun x h n => Nat.le_max_left _ _)
  let G' := G.refineSchedules refinementStage step eval refinementStage_budget
    (fun n => by
      dsimp [step]
      rw [Nat.mul_comm]
      exact reciprocal_product_le_left _ _) (fun x h n => Nat.le_max_right _ _)
  exact F'.addOfCommonSchedule G' hlo hhi
    (by rw [F.same_lower, G.same_lower]; exact hlo)
    (by rw [F.same_upper, G.same_upper]; exact hhi)
    rfl rfl (fun n => 2 * (n + 1)) precisionAtStage_scaleRat_two

end HasDerivativeOnInterval
end ComputableAnalysis
