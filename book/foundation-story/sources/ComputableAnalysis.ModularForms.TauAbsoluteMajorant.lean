import ComputableAnalysis.ModularForms.Tau

/-! Executable nonnegative coefficient majorants for Euler products. -/
namespace ComputableAnalysis.ModularForms

def addShift (m : Nat) (a : Nat → Nat) : Nat → Nat :=
  fun n => if m≤n then a n+a (n-m) else a n

def positiveFactorPower (m : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, a => a
  | r+1, a => addShift m (positiveFactorPower m r a)

/-- Coefficients of the positive product with every minus sign replaced by plus. -/
def discriminantAbsoluteMajorant : Nat → Nat → Nat
  | 0 => fun n => if n=0 then 1 else 0
  | N+1 => positiveFactorPower (N+1) 24 (discriminantAbsoluteMajorant N)

theorem subtractShift_absolute_bound (m : Nat) (a : Coefficients) (b : Nat → Nat)
    (hab : ∀ n, (a n).natAbs≤b n) (n : Nat) :
    (subtractShift m a n).natAbs≤addShift m b n := by
  unfold subtractShift addShift
  split
  · exact Nat.le_trans (Int.natAbs_sub_le _ _) (Nat.add_le_add (hab n) (hab (n-m)))
  · exact hab n

theorem factorPower_absolute_bound (m r : Nat) (a : Coefficients) (b : Nat → Nat)
    (hab : ∀ n, (a n).natAbs≤b n) (n : Nat) :
    (factorPower m r a n).natAbs≤positiveFactorPower m r b n := by
  induction r generalizing n with
  | zero => exact hab n
  | succ r ih =>
    exact subtractShift_absolute_bound m (factorPower m r a)
      (positiveFactorPower m r b) ih n

/-- The actual finite coefficients are bounded by constructed positive coefficients. -/
theorem discriminantProduct_absolute_bound (N n : Nat) :
    (discriminantProduct N n).natAbs≤discriminantAbsoluteMajorant N n := by
  induction N generalizing n with
  | zero =>
    unfold discriminantProduct unitCoefficients discriminantAbsoluteMajorant
    split <;> decide
  | succ N ih =>
    exact factorPower_absolute_bound (N+1) 24 (discriminantProduct N)
      (discriminantAbsoluteMajorant N) ih n

theorem positiveFactorPower_below (m r n : Nat) (a : Nat → Nat) (hn : n<m) :
    positiveFactorPower m r a n=a n := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [positiveFactorPower,addShift,if_neg (Nat.not_le.mpr hn),ih]

/-- Positive majorant coefficients stabilize at each degree as well. -/
theorem discriminantAbsoluteMajorant_stable (n N : Nat) (hn : n≤N) :
    discriminantAbsoluteMajorant N n=discriminantAbsoluteMajorant n n := by
  induction N with
  | zero =>
    have he : n=0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases h : n≤N
    · rw [discriminantAbsoluteMajorant,positiveFactorPower_below (N+1) 24 n _ (by omega)]
      exact ih h
    · have he : n=N+1 := by omega
      subst n
      rfl

/-- A finite executable absolute bound for every tau coefficient. -/
theorem tau_absolute_majorant (n : Nat) :
    (tau (n+1)).natAbs≤discriminantAbsoluteMajorant n n :=
  discriminantProduct_absolute_bound n n

end ComputableAnalysis.ModularForms
