import ComputableAnalysis.Apery.Binomial

/-! Apéry's Picard–Fuchs operator, defined through the Euler derivative.
The equation is deduced from the independently defined binomial sums. -/
namespace ComputableAnalysis.Apery
open FormalPowerSeries

/-- Iteration of `theta + a`, where `theta = t d/dt`. -/
def eulerPower (a : Rat) : Nat → Coeffs → Coeffs
  | 0, c => c
  | j+1, c => shiftedEuler a (eulerPower a j c)

/-- Scaling parameter `r` changes the independent variable from `t` to `r*x`. -/
def operator (r : Rat) (c : Coeffs) : Coeffs := fun n =>
  eulerPower 0 3 c n - r*mulX (fun k =>
    34*eulerPower 0 3 c k+51*eulerPower 0 2 c k+27*eulerPower 0 1 c k+5*c k) n +
    r^2*mulX (mulX (eulerPower 1 3 c)) n

theorem operator_coefficient (r : Rat) (c : Coeffs) (n : Nat) :
    operator r c (n+2) = ((n : Rat)+2)^3*c (n+2) -
      r*recurrencePolynomial ((n : Rat)+1)*c (n+1) + r^2*((n : Rat)+1)^3*c n := by
  simp only [operator, eulerPower, shiftedEuler, mulX, recurrencePolynomial,
    Rat.pow_succ, Rat.pow_zero, Rat.one_mul, Rat.natCast_add]
  grind only

/-- The integer generating series solves the unscaled differential equation. -/
theorem number_equation (n : Nat) : operator 1 number n = 0 := by
  cases n with
  | zero => simp [operator, eulerPower, shiftedEuler, mulX]; grind
  | succ n => cases n with
    | zero => simp [operator, eulerPower, shiftedEuler, mulX, number_zero, number_one]; grind
    | succ n => rw [operator_coefficient]; have := number_recurrence n; grind

/-- Rational scaling, keeping every calculation inside a certified small disk. -/
def coefficients (n : Nat) : Rat := number n*((1 : Rat)/4096)^n

theorem coefficients_equation (n : Nat) : operator (1/4096) coefficients n = 0 := by
  cases n with
  | zero => simp [operator, coefficients, eulerPower, shiftedEuler, mulX]; grind
  | succ n => cases n with
    | zero => simp [operator, coefficients, eulerPower, shiftedEuler, mulX, number_zero, number_one]; decide +kernel
    | succ n =>
      rw [operator_coefficient]
      have h := number_recurrence n
      have hh := congrArg (fun z : Rat => z*((1 : Rat)/4096)^(n+2)) h
      simp only [coefficients, Rat.pow_succ] at *
      grind only

/-- Iterated ordinary derivatives, kept separate from the Euler operator. -/
def jet : Nat → Coeffs
  | 0 => coefficients
  | j+1 => coefficientShift (jet j)

theorem coefficients_bound (n : Nat) : qabs (coefficients n) ≤ ((1 : Rat)/64)^n := by
  have h := Rat.mul_le_mul_of_nonneg_right (number_growth n)
    (Rat.pow_nonneg (n := n) (by decide +kernel : (0 : Rat) ≤ 1/4096))
  unfold coefficients
  rw [qabs_mul, qabs_eq_self_of_nonneg (Rat.pow_nonneg (by decide +kernel : (0 : Rat) ≤ 1/4096))]
  rw [pow_product, show (64 : Rat)*(1/4096)=1/64 by decide +kernel] at h
  exact h

theorem jet_bound (j : Nat) (hj : j ≤ 3) (n : Nat) :
    qabs (jet j n) ≤ ((1 : Rat)/8)^n := by
  have h1 : ∀ k, qabs (jet 1 k) ≤ ((1 : Rat)/32)^k := by
    intro k
    have h := coefficientShift_unit_growth (by decide +kernel : (0 : Rat) ≤ 1/64)
      (by decide +kernel) coefficients_bound k
    simpa only [jet, show (2 : Rat)*(1/64)=1/32 by decide +kernel] using h
  have h2 : ∀ k, qabs (jet 2 k) ≤ ((1 : Rat)/16)^k := by
    intro k
    have h := coefficientShift_unit_growth (by decide +kernel : (0 : Rat) ≤ 1/32)
      (by decide +kernel) h1 k
    simpa only [jet, show (2 : Rat)*(1/32)=1/16 by decide +kernel] using h
  have h3 : ∀ k, qabs (jet 3 k) ≤ ((1 : Rat)/8)^k := by
    intro k
    have h := coefficientShift_unit_growth (by decide +kernel : (0 : Rat) ≤ 1/16)
      (by decide +kernel) h2 k
    simpa only [jet, show (2 : Rat)*(1/16)=1/8 by decide +kernel] using h
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases cases with h | h | h | h <;> subst j
  · exact Rat.le_trans (coefficients_bound n) (pow_base_mono (by decide +kernel) (by decide +kernel) n)
  · exact Rat.le_trans (h1 n) (pow_base_mono (by decide +kernel) (by decide +kernel) n)
  · exact Rat.le_trans (h2 n) (pow_base_mono (by decide +kernel) (by decide +kernel) n)
  · exact h3 n

/-- Literal finite-prefix boxes for `A(x/4096)` and its first three derivatives. -/
def value (j : Nat) (x : Rat) : RealRaw := geometricRaw (jet j) 1 x

theorem value_valid {j : Nat} (hj : j ≤ 3) {x : Rat} (hx : qabs x ≤ 1) :
    (value j x).Valid :=
  geometricRaw_rapid_valid (by decide) (by intro k; simpa using jet_bound j hj k) hx

/-- Actual finite-difference semantics, not merely a formal derivative. -/
theorem value_derivative {j : Nat} (hj : j < 3) (eps : QPos) {x h v w d : Rat} {n : Nat}
    (hh : h ≠ 0) (hx : qabs x ≤ 1) (hxh : qabs (x+h) ≤ 1)
    (hsmall : qabs h ≤ (derivativeRadius 1 (by decide) eps).val)
    (hn : derivativeStage 1 eps h ≤ n)
    (hv : InBox v ((value j x).compute n))
    (hw : InBox w ((value j (x+h)).compute n))
    (hd : InBox d ((value (j+1) x).compute n)) :
    qabs (w-v-h*d) ≤ eps.val*qabs h :=
  geometricRaw_hasBoxDerivative (by decide) (by intro k; simpa using jet_bound j (by omega) k)
    eps hh hx hxh hsmall hn hv hw hd

/-- Repeated multiplication by the independent variable. -/
def shift : Nat → Coeffs → Coeffs
  | 0, c => c
  | s+1, c => mulX (shift s c)

def derivative : Nat → Coeffs → Coeffs
  | 0, c => c
  | j+1, c => coefficientShift (derivative j c)

/-- The usual third-order differential expression, expanded into monomials. -/
def ordinary (r : Rat) (c : Coeffs) (n : Nat) : Rat :=
  shift 3 (derivative 3 c) n - 34*r*shift 4 (derivative 3 c) n + r^2*shift 5 (derivative 3 c) n +
  3*shift 2 (derivative 2 c) n - 153*r*shift 3 (derivative 2 c) n + 6*r^2*shift 4 (derivative 2 c) n +
  shift 1 (derivative 1 c) n - 112*r*shift 2 (derivative 1 c) n + 7*r^2*shift 3 (derivative 1 c) n -
  5*r*shift 1 c n + r^2*shift 2 c n

theorem operator_ordinary (r : Rat) (c : Coeffs) (n : Nat) : operator r c n = ordinary r c n := by
  rcases n with _ | n
  · simp [operator, ordinary, shift, mulX, eulerPower, shiftedEuler]; grind
  rcases n with _ | n
  · simp [operator, ordinary, shift, mulX, derivative, coefficientShift, eulerPower, shiftedEuler]
    grind
  rcases n with _ | n
  · simp [operator, ordinary, shift, mulX, derivative, coefficientShift, eulerPower, shiftedEuler]
    grind
  rcases n with _ | n
  · simp [operator, ordinary, shift, mulX, derivative, coefficientShift, eulerPower, shiftedEuler]
    grind
  rcases n with _ | n
  · simp [operator, ordinary, shift, mulX, derivative, coefficientShift, eulerPower, shiftedEuler]
    grind
  simp only [operator, ordinary, shift, mulX, derivative, coefficientShift, eulerPower,
    shiftedEuler, Rat.natCast_add, Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  grind only

/-- Finite evaluation commutes with a monomial shift at the matching truncation. -/
theorem shift_prefix (s : Nat) (c : Coeffs) (x : Rat) (N : Nat) :
    sumBelow (fun k => shift s c k*x^k) (N+s) = x^s*sumBelow (fun k => c k*x^k) N := by
  have hmul (c : Coeffs) (N : Nat) :
      sumBelow (fun k => mulX c k*x^k) (N+1) = x*sumBelow (fun k => c k*x^k) N := by
    induction N with
    | zero => simp [sumBelow_succ, mulX]; grind
    | succ N ih => simp only [sumBelow_succ, mulX, Rat.pow_succ] at *; grind only
  induction s with
  | zero => simp [shift]
  | succ s ih =>
    rw [show N+(s+1)=(N+s)+1 by omega]
    simp only [shift]
    rw [hmul, ih, Rat.pow_succ]
    grind only

private def monomials : List (Rat × Nat × Nat) :=
  [(1,3,3), (-34/4096,4,3), (1/4096^2,5,3),
   (3,2,2), (-153/4096,3,2), (6/4096^2,4,2),
   (1,1,1), (-112/4096,2,1), (7/4096^2,3,1),
   (-5/4096,1,0), (1/4096^2,2,0)]

private theorem monomial_bounds (m : Rat × Nat × Nat) (hm : m ∈ monomials) :
    m.2.1 ≤ 5 ∧ m.2.2 ≤ 3 := by
  simp only [monomials, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h <;> subst m <;> decide

private theorem monomial_equation (k : Nat) :
    ratListSum (monomials.map (fun m => m.1*shift m.2.1 (jet m.2.2) k)) = 0 := by
  have h := coefficients_equation k
  rw [operator_ordinary] at h
  simp only [ordinary, derivative] at h
  simp only [monomials, List.map, ratListSum, jet]
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at h
  grind only

private theorem sumBelow_listSum {α : Type} (l : List α) (f : α → Nat → Rat) (N : Nat) :
    sumBelow (fun k => ratListSum (l.map (fun a => f a k))) N =
      ratListSum (l.map (fun a => sumBelow (f a) N)) := by
  induction l with
  | nil => simp only [List.map, ratListSum]; induction N with
    | zero => rfl
    | succ N ih => rw [sumBelow_succ, ih]; decide +kernel
  | cons a l ih => simp only [List.map, ratListSum, sumBelow_add, ih]

private theorem finite_equation (x : Rat) (N : Nat) :
    ratListSum (monomials.map (fun m => m.1*x^m.2.1*
      sumBelow (fun k => jet m.2.2 k*x^k) (N+5-m.2.1))) = 0 := by
  have hz : sumBelow (fun k => ratListSum (monomials.map
      (fun m => m.1*shift m.2.1 (jet m.2.2) k*x^k))) (N+5) = 0 := by
    have hh (k : Nat) : ratListSum (monomials.map
        (fun m => m.1*shift m.2.1 (jet m.2.2) k*x^k)) = 0 := by
      have hmul (l : List (Rat × Nat × Nat)) : ratListSum (l.map
          (fun m => m.1*shift m.2.1 (jet m.2.2) k*x^k)) =
          ratListSum (l.map (fun m => m.1*shift m.2.1 (jet m.2.2) k))*x^k := by
        induction l with
        | nil => simp [ratListSum]
        | cons a l ih => simp only [List.map, ratListSum, ih]; grind only
      rw [hmul, monomial_equation]; grind
    have he : (fun k => ratListSum (monomials.map
        (fun m => m.1*shift m.2.1 (jet m.2.2) k*x^k))) = (fun _ => 0) := funext hh
    rw [he]
    induction (N+5) with
    | zero => rfl
    | succ K ih => rw [sumBelow_succ, ih]; decide +kernel
  rw [sumBelow_listSum] at hz
  have he : monomials.map (fun m => sumBelow
      (fun k => m.1*shift m.2.1 (jet m.2.2) k*x^k) (N+5)) =
      monomials.map (fun m => m.1*x^m.2.1*
        sumBelow (fun k => jet m.2.2 k*x^k) (N+5-m.2.1)) := by
    apply List.map_congr_left
    intro m hm
    have hb := (monomial_bounds m hm).1
    have hs := shift_prefix m.2.1 (jet m.2.2) x (N+5-m.2.1)
    rw [show N+5-m.2.1+m.2.1=N+5 by omega] at hs
    have hf : (fun k => m.1*shift m.2.1 (jet m.2.2) k*x^k) =
        (fun k => m.1*(shift m.2.1 (jet m.2.2) k*x^k)) := by funext k; grind
    rw [hf, sumBelow_mul, hs]
    grind only
  rw [he] at hz
  exact hz

private theorem weighted_sample_error {x : Rat} (hx : qabs x ≤ 1) (N : Nat)
    (samples : Nat → Rat) (hs : ∀ j, j ≤ 3 → InBox (samples j) ((value j x).compute N)) :
    qabs (ratListSum (monomials.map (fun m => m.1*x^m.2.1*samples m.2.2))) ≤
      24*((1 : Rat)/2)^N := by
  let delta := 4*((1 : Rat)/2)^N
  let approx := fun (m : Rat × Nat × Nat) => sumBelow (fun k => jet m.2.2 k*x^k) (N+5-m.2.1)
  have per (m : Rat × Nat × Nat) (hm : m ∈ monomials) :
      qabs (m.1*x^m.2.1*(samples m.2.2-approx m)) ≤ qabs m.1*delta := by
    have hb := monomial_bounds m hm
    have hp : InBox (approx m) ((value m.2.2 x).compute N) :=
      geometricRaw_contains_prefix (by decide) (by decide +kernel : (0 : Rat) ≤ 1/8)
        (by intro k; simpa using jet_bound m.2.2 hb.2 k) (by grind) (by omega)
    have hd := inBox_distance (hs m.2.2 hb.2) hp
    change qabs (samples m.2.2-approx m) ≤ ((geometricRaw (jet m.2.2) 1 x).compute N).width at hd
    rw [geometricRaw_width] at hd
    have hpow : qabs (x^m.2.1) ≤ 1 := by
      have all (s : Nat) : qabs (x^s) ≤ 1 := by
        induction s with
        | zero => simp [qabs]; decide
        | succ s ih =>
          rw [Rat.pow_succ, qabs_mul]
          have h := Rat.mul_le_mul_of_nonneg_left hx (qabs_nonneg (x^s))
          grind only
      exact all m.2.1
    rw [qabs_mul, qabs_mul]
    have h1 := Rat.mul_le_mul_of_nonneg_left hpow (qabs_nonneg m.1)
    have h2 := Rat.mul_le_mul_of_nonneg_right h1 (qabs_nonneg (samples m.2.2-approx m))
    have h3 := Rat.mul_le_mul_of_nonneg_left hd (qabs_nonneg m.1)
    dsimp [delta]
    grind only
  have bound (l : List (Rat × Nat × Nat)) (hl : ∀ m, m ∈ l → m ∈ monomials) :
      qabs (ratListSum (l.map (fun m => m.1*x^m.2.1*(samples m.2.2-approx m)))) ≤
        ratListSum (l.map (fun m => qabs m.1))*delta := by
    induction l with
    | nil => simp [ratListSum, qabs]
    | cons m l ih =>
      have h := per m (hl m (by simp))
      have hi := ih (fun a ha => hl a (by simp [ha]))
      simp only [List.map, ratListSum]
      have ht := qabs_add_le (m.1*x^m.2.1*(samples m.2.2-approx m))
        (ratListSum (l.map (fun m => m.1*x^m.2.1*(samples m.2.2-approx m))))
      grind only
  have h := bound monomials (fun _ h => h)
  have he := finite_equation x N
  have split (l : List (Rat × Nat × Nat)) :
      ratListSum (l.map (fun m => m.1*x^m.2.1*(samples m.2.2-approx m))) =
      ratListSum (l.map (fun m => m.1*x^m.2.1*samples m.2.2)) -
      ratListSum (l.map (fun m => m.1*x^m.2.1*approx m)) := by
    induction l with
    | nil => simp [ratListSum]; grind
    | cons m l ih => simp only [List.map, ratListSum, ih]; grind only
  rw [split, show ratListSum (monomials.map (fun m => m.1*x^m.2.1*approx m))=0 from he] at h
  have hw : ratListSum (monomials.map (fun m => qabs m.1)) ≤ 6 := by decide +kernel
  have hd : 0 ≤ delta := Rat.mul_nonneg (by decide) (Rat.pow_nonneg (by decide +kernel))
  have hh := Rat.mul_le_mul_of_nonneg_right hw hd
  dsimp [delta] at *
  grind only

/-- The differential equation on actual computed values and derivatives.
Every choice of samples from stage `N` boxes has this explicit residual bound. -/
theorem equation_error {x y d1 d2 d3 : Rat} (hx : qabs x ≤ 1) (N : Nat)
    (hy : InBox y ((value 0 x).compute N))
    (h1 : InBox d1 ((value 1 x).compute N))
    (h2 : InBox d2 ((value 2 x).compute N))
    (h3 : InBox d3 ((value 3 x).compute N)) :
    qabs (x^3*(1-34*x/4096+x^2/4096^2)*d3 +
      x^2*(3-153*x/4096+6*x^2/4096^2)*d2 +
      x*(1-112*x/4096+7*x^2/4096^2)*d1 + (-5*x/4096+x^2/4096^2)*y) ≤
      24*((1 : Rat)/2)^N := by
  let samples : Nat → Rat := fun j => if j=0 then y else if j=1 then d1 else if j=2 then d2 else d3
  have hs (j : Nat) (hj : j ≤ 3) : InBox (samples j) ((value j x).compute N) := by
    have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases h with h | h | h | h <;> subst j
    · exact hy
    · exact h1
    · exact h2
    · exact h3
  have h := weighted_sample_error hx N samples hs
  have he : ratListSum (monomials.map (fun m => m.1*x^m.2.1*samples m.2.2)) =
      x^3*(1-34*x/4096+x^2/4096^2)*d3 + x^2*(3-153*x/4096+6*x^2/4096^2)*d2 +
      x*(1-112*x/4096+7*x^2/4096^2)*d1 + (-5*x/4096+x^2/4096^2)*y := by
    simp only [monomials, List.map, ratListSum, samples, ite_true, ite_false,
      show ¬(3:Nat)=0 by decide, show ¬(3:Nat)=1 by decide, show ¬(3:Nat)=2 by decide,
      show ¬(2:Nat)=0 by decide, show ¬(2:Nat)=1 by decide, show ¬(1:Nat)=0 by decide,
      Rat.pow_succ, Rat.pow_zero, Rat.one_mul, Rat.div_def]
    grind only
  rw [he] at h
  exact h

/-- A computed stage realizes every positive rational tolerance in the ODE. -/
theorem equation (eps : QPos) {x y d1 d2 d3 : Rat} (hx : qabs x ≤ 1)
    {N : Nat} (hN : RationalMajorant.halfDecayShift 24 eps ≤ N)
    (hy : InBox y ((value 0 x).compute N))
    (h1 : InBox d1 ((value 1 x).compute N))
    (h2 : InBox d2 ((value 2 x).compute N))
    (h3 : InBox d3 ((value 3 x).compute N)) :
    qabs (x^3*(1-34*x/4096+x^2/4096^2)*d3 +
      x^2*(3-153*x/4096+6*x^2/4096^2)*d2 +
      x*(1-112*x/4096+7*x^2/4096^2)*d1 + (-5*x/4096+x^2/4096^2)*y) ≤ eps.val := by
  have he := equation_error hx N hy h1 h2 h3
  have hb := Rat.mul_le_mul_of_nonneg_left (half_pow_antitone hN) (by decide : (0 : Rat) ≤ 24)
  exact Rat.le_trans he (Rat.le_trans hb (RationalMajorant.halfDecayShift_spec (by decide) eps))

end ComputableAnalysis.Apery
