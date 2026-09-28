import ComputableAnalysis.FiniteApproximateIdentity

/-!
# Finite convolution and moment cancellation

Executable convolution of positive rational quadrature kernels.  The action
laws express equality of weighted sums, not equality of the lists encoding
them.  These are finite probability theorems and ingredients for continuous
convolution; no Gaussian integral or central limit theorem is assumed.
-/

namespace ComputableAnalysis
namespace WeightedPoint

/-- Translate a list and multiply its weights by one outer weight. -/
def translateWeight (outer : WeightedPoint) (samples : List WeightedPoint) :
    List WeightedPoint :=
  samples.map fun inner =>
    ⟨outer.point + inner.point, outer.weight * inner.weight⟩

/-- All pairwise sums, retaining multiplicities and multiplying weights. -/
def convolution : List WeightedPoint → List WeightedPoint → List WeightedPoint
  | [], _ => []
  | outer :: rest, right => translateWeight outer right ++ convolution rest right

theorem action_translateWeight (outer : WeightedPoint)
    (samples : List WeightedPoint) (f : Rat → Rat) :
    action (translateWeight outer samples) f =
      outer.weight * action samples (fun y => f (outer.point + y)) := by
  induction samples with
  | nil => simp [translateWeight, action]
  | cons inner rest ih =>
      simp only [translateWeight, List.map_cons, action] at *
      rw [ih]
      grind [Rat.mul_add, Rat.mul_assoc]

theorem action_convolution (left right : List WeightedPoint) (f : Rat → Rat) :
    action (convolution left right) f =
      action left (fun x => action right (fun y => f (x + y))) := by
  induction left with
  | nil => rfl
  | cons outer rest ih =>
      simp only [convolution, action_append, action_translateWeight, action, ih]

theorem totalWeight_convolution (left right : List WeightedPoint) :
    totalWeight (convolution left right) = totalWeight left * totalWeight right := by
  have h := action_convolution left right (fun _ => 1)
  simpa [action_const, Rat.mul_comm] using h

theorem convolution_nonnegative (left right : List WeightedPoint)
    (hl : ∀ s, s ∈ left → 0 ≤ s.weight)
    (hr : ∀ s, s ∈ right → 0 ≤ s.weight) :
    ∀ s, s ∈ convolution left right → 0 ≤ s.weight := by
  induction left with
  | nil => simp [convolution]
  | cons outer rest ih =>
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · obtain ⟨inner, hi, rfl⟩ := List.mem_map.mp hs
        exact Rat.mul_nonneg (hl outer (by simp)) (hr inner hi)
      · exact ih (fun t ht => hl t (by simp [ht])) s hs

theorem action_congr (samples : List WeightedPoint) {f g : Rat → Rat}
    (h : ∀ x, f x = g x) : action samples f = action samples g := by
  exact congrArg (action samples) (funext h)

/-- Finite interchange, proved by list induction. -/
theorem action_swap (left right : List WeightedPoint) (f : Rat → Rat → Rat) :
    action left (fun x => action right (f x)) =
      action right (fun y => action left (fun x => f x y)) := by
  induction left with
  | nil => simp [action, action_const]
  | cons outer rest ih =>
      simp only [action, action_add, action_scale]
      rw [ih]

theorem action_convolution_comm (left right : List WeightedPoint) (f : Rat → Rat) :
    action (convolution left right) f = action (convolution right left) f := by
  rw [action_convolution, action_convolution, action_swap]
  apply action_congr
  intro y
  apply action_congr
  intro x
  rw [Rat.add_comm]

theorem action_convolution_assoc (a b c : List WeightedPoint) (f : Rat → Rat) :
    action (convolution (convolution a b) c) f =
      action (convolution a (convolution b c)) f := by
  simp only [action_convolution]
  apply action_congr
  intro x
  apply action_congr
  intro y
  apply action_congr
  intro z
  rw [Rat.add_assoc]

/-- Weighted pointwise error bounds may vary across the support. -/
theorem qabs_action_le_action_bound (samples : List WeightedPoint)
    (f bound : Rat → Rat)
    (hw : ∀ s, s ∈ samples → 0 ≤ s.weight)
    (hf : ∀ s, s ∈ samples → qabs (f s.point) ≤ bound s.point) :
    qabs (action samples f) ≤ action samples bound := by
  induction samples with
  | nil => change qabs 0 ≤ 0; decide
  | cons s rest ih =>
      have hs := hw s (by simp)
      have he := hf s (by simp)
      have hr := ih (fun t ht => hw t (by simp [ht]))
        (fun t ht => hf t (by simp [ht]))
      have hterm := Rat.mul_le_mul_of_nonneg_left he hs
      have ht := qabs_add_le (s.weight * f s.point) (action rest f)
      have habs : qabs s.weight = s.weight := qabs_eq_self_of_nonneg hs
      rw [qabs_mul, habs] at ht
      change qabs (s.weight * f s.point + action rest f) ≤
        s.weight * bound s.point + action rest bound
      grind only

end WeightedPoint

namespace FiniteProbabilityKernel

/-- A concrete probability kernel for the sum of two independent finite laws. -/
def convolution (a b : FiniteProbabilityKernel) : FiniteProbabilityKernel where
  samples := WeightedPoint.convolution a.samples b.samples
  weights_nonnegative := WeightedPoint.convolution_nonnegative _ _
    a.weights_nonnegative b.weights_nonnegative
  totalWeight_eq_one := by
    rw [WeightedPoint.totalWeight_convolution, a.totalWeight_eq_one,
      b.totalWeight_eq_one, Rat.one_mul]

theorem action_convolution (a b : FiniteProbabilityKernel) (f : Rat → Rat) :
    (a.convolution b).action f = a.action (fun x => b.action (fun y => f (x + y))) :=
  WeightedPoint.action_convolution _ _ _

theorem action_const (a : FiniteProbabilityKernel) (c : Rat) :
    a.action (fun _ => c) = c := by
  simp [action, WeightedPoint.action_const, a.totalWeight_eq_one]

theorem action_add (a : FiniteProbabilityKernel) (f g : Rat → Rat) :
    a.action (fun x => f x + g x) = a.action f + a.action g :=
  WeightedPoint.action_add _ _ _

theorem action_scale (a : FiniteProbabilityKernel) (c : Rat) (f : Rat → Rat) :
    a.action (fun x => c * f x) = c * a.action f :=
  WeightedPoint.action_scale _ _ _

theorem action_mul_id (a : FiniteProbabilityKernel) (c : Rat) :
    a.action (fun x => c * x) = c * a.action id :=
  action_scale a c id

theorem action_const_add_id (a : FiniteProbabilityKernel) (c : Rat) :
    a.action (fun x => c + x) = c + a.action id := by
  rw [show (fun x => c + x) = (fun x => (fun _ => c) x + id x) from rfl,
    action_add, action_const]

theorem action_id_add_const (a : FiniteProbabilityKernel) (c : Rat) :
    a.action (fun x => x + c) = a.action id + c := by
  rw [show (fun x => x + c) = (fun x => id x + (fun _ => c) x) from rfl,
    action_add, action_const]

theorem action_sub (a : FiniteProbabilityKernel) (f g : Rat → Rat) :
    a.action (fun x => f x - g x) = a.action f - a.action g := by
  have h : (fun x => f x - g x) = (fun x => f x + (-1) * g x) := by
    funext x; grind
  rw [h, action_add, action_scale]
  grind only

theorem action_difference_le (a : FiniteProbabilityKernel)
    (f g : Rat → Rat) (error : Rat)
    (h : ∀ s, s ∈ a.samples → qabs (f s.point - g s.point) ≤ error) :
    qabs (a.action f - a.action g) ≤ error := by
  have ha := WeightedPoint.qabs_action_le_action_bound a.samples
    (fun x => f x - g x) (fun _ => error) a.weights_nonnegative h
  change qabs (a.action (fun x => f x - g x)) ≤ a.action (fun _ => error) at ha
  rwa [action_sub, action_const] at ha

/-- First moment and centered second moment of the supplied finite law. -/
def mean (a : FiniteProbabilityKernel) : Rat := a.action id
def secondMoment (a : FiniteProbabilityKernel) : Rat := a.action (fun x => x * x)
def variance (a : FiniteProbabilityKernel) : Rat :=
  a.action (fun x => (x - a.mean) * (x - a.mean))

theorem mean_convolution (a b : FiniteProbabilityKernel) :
    (a.convolution b).mean = a.mean + b.mean := by
  simp only [mean, action_convolution, id_eq, action_const_add_id, action_id_add_const]

theorem secondMoment_convolution (a b : FiniteProbabilityKernel) :
    (a.convolution b).secondMoment =
      a.secondMoment + 2 * a.mean * b.mean + b.secondMoment := by
  unfold secondMoment
  rw [action_convolution]
  have hexpand : ∀ x y : Rat,
      (x + y) * (x + y) = x * x + (2 * x) * y + y * y := by
    intros; grind
  simp only [hexpand, action_add, action_const, action_mul_id]
  have hscale : (fun x => 2 * x * b.action id) =
      (fun x => (2 * b.action id) * x) := by funext x; grind
  change a.action (fun x => x * x) +
    a.action (fun x => 2 * x * b.action id) + b.action (fun y => y * y) = _
  rw [hscale, action_mul_id]
  unfold mean
  grind only

theorem variance_eq_secondMoment_sub_mean_sq (a : FiniteProbabilityKernel) :
    a.variance = a.secondMoment - a.mean * a.mean := by
  unfold variance
  have hexpand : ∀ x : Rat, (x - a.mean) * (x - a.mean) =
      x * x + (-2 * a.mean) * x + a.mean * a.mean := by
    intro x; grind
  simp only [hexpand, action_add, action_mul_id, action_const]
  change a.secondMoment + (-2 * a.mean) * a.mean + a.mean * a.mean = _
  grind

theorem variance_convolution (a b : FiniteProbabilityKernel) :
    (a.convolution b).variance = a.variance + b.variance := by
  simp only [variance_eq_secondMoment_sub_mean_sq, mean_convolution,
    secondMoment_convolution]
  grind

/-- Convolution acts on functions by averaging translates. -/
def convolveFunction (a : FiniteProbabilityKernel) (f : Rat → Rat) (x : Rat) : Rat :=
  a.action (fun y => f (x - y))

theorem convolveFunction_convolution (a b : FiniteProbabilityKernel)
    (f : Rat → Rat) (x : Rat) :
    (a.convolution b).convolveFunction f x =
      a.convolveFunction (b.convolveFunction f) x := by
  unfold convolveFunction
  rw [action_convolution]
  apply WeightedPoint.action_congr
  intro y
  apply WeightedPoint.action_congr
  intro z
  congr 1
  grind

/-- Equal first two moments cancel every quadratic test function exactly. -/
theorem quadratic_action_eq (a b : FiniteProbabilityKernel)
    (hmean : a.mean = b.mean) (hsecond : a.secondMoment = b.secondMoment)
    (c l q : Rat) :
    a.action (fun x => c + l * x + q * (x * x)) =
      b.action (fun x => c + l * x + q * (x * x)) := by
  simp only [action_add, action_const, action_mul_id, action_scale]
  change c + l * a.mean + q * a.secondMoment =
    c + l * b.mean + q * b.secondMoment
  rw [hmean, hsecond]

/-- One replacement step: after equal-moment cancellation only the two
remainder budgets remain.  The approximation hypotheses are pointwise on
the actual supports, not assumptions of the desired action comparison. -/
theorem replacement_bound (a b : FiniteProbabilityKernel)
    (hmean : a.mean = b.mean) (hsecond : a.secondMoment = b.secondMoment)
    (f : Rat → Rat) (c l q ea eb : Rat)
    (ha : ∀ s, s ∈ a.samples →
      qabs (f s.point - (c + l * s.point + q * (s.point * s.point))) ≤ ea)
    (hb : ∀ s, s ∈ b.samples →
      qabs (f s.point - (c + l * s.point + q * (s.point * s.point))) ≤ eb) :
    qabs (a.action f - b.action f) ≤ ea + eb := by
  let p := fun x => c + l * x + q * (x * x)
  have hzero : ∀ x : Rat, x - 0 = x := by intro x; grind
  have hpa := a.action_approximates_center (fun x => f x - p x) 0 ea (by
    intro s hs; simpa only [p, hzero] using ha s hs)
  have hpb := b.action_approximates_center (fun x => f x - p x) 0 eb (by
    intro s hs; simpa only [p, hzero] using hb s hs)
  rw [action_sub] at hpa hpb
  have hp : a.action p = b.action p := quadratic_action_eq a b hmean hsecond c l q
  have heq : a.action f - b.action f =
      (a.action f - a.action p) + -(b.action f - b.action p) := by rw [hp]; grind
  rw [heq]
  have ht := qabs_add_le (a.action f - a.action p) (-(b.action f - b.action p))
  rw [qabs_neg] at ht
  simp only [hzero] at hpa hpb
  grind only

/-- The absolute third moment gives the natural cubic remainder budget. -/
def thirdAbsoluteMoment (a : FiniteProbabilityKernel) : Rat :=
  a.action (fun x => qabs x * qabs x * qabs x)

theorem cubic_replacement_bound (a b : FiniteProbabilityKernel)
    (hmean : a.mean = b.mean) (hsecond : a.secondMoment = b.secondMoment)
    (f : Rat → Rat) (c l q C : Rat)
    (ha : ∀ s, s ∈ a.samples →
      qabs (f s.point - (c + l * s.point + q * (s.point * s.point))) ≤
        C * (qabs s.point * qabs s.point * qabs s.point))
    (hb : ∀ s, s ∈ b.samples →
      qabs (f s.point - (c + l * s.point + q * (s.point * s.point))) ≤
        C * (qabs s.point * qabs s.point * qabs s.point)) :
    qabs (a.action f - b.action f) ≤
      C * (a.thirdAbsoluteMoment + b.thirdAbsoluteMoment) := by
  let p := fun x => c + l * x + q * (x * x)
  have hpa := WeightedPoint.qabs_action_le_action_bound a.samples
    (fun x => f x - p x) (fun x => C * (qabs x * qabs x * qabs x))
    a.weights_nonnegative ha
  have hpb := WeightedPoint.qabs_action_le_action_bound b.samples
    (fun x => f x - p x) (fun x => C * (qabs x * qabs x * qabs x))
    b.weights_nonnegative hb
  change qabs (a.action (fun x => f x - p x)) ≤
    a.action (fun x => C * (qabs x * qabs x * qabs x)) at hpa
  change qabs (b.action (fun x => f x - p x)) ≤
    b.action (fun x => C * (qabs x * qabs x * qabs x)) at hpb
  rw [action_sub, action_scale] at hpa hpb
  have hp : a.action p = b.action p := quadratic_action_eq a b hmean hsecond c l q
  have heq : a.action f - b.action f =
      (a.action f - a.action p) + -(b.action f - b.action p) := by rw [hp]; grind
  rw [heq]
  have ht := qabs_add_le (a.action f - a.action p) (-(b.action f - b.action p))
  rw [qabs_neg] at ht
  unfold thirdAbsoluteMoment
  grind only

/-- The convolution identity, represented by a single point. -/
def dirac (x : Rat) : FiniteProbabilityKernel where
  samples := [⟨x, 1⟩]
  weights_nonnegative := by
    intro s hs; simp only [List.mem_singleton] at hs; subst s
    change (0 : Rat) ≤ 1
    decide
  totalWeight_eq_one := by change (1 : Rat) + 0 = 1; grind

theorem action_dirac (x : Rat) (f : Rat → Rat) : (dirac x).action f = f x := by
  change 1 * f x + 0 = f x
  grind

/-- Literal repeated finite convolution; no limiting law is built in. -/
def convolutionPower (a : FiniteProbabilityKernel) : Nat → FiniteProbabilityKernel
  | 0 => dirac 0
  | n + 1 => a.convolution (a.convolutionPower n)

theorem mean_convolutionPower (a : FiniteProbabilityKernel) (n : Nat) :
    (a.convolutionPower n).mean = (n : Rat) * a.mean := by
  induction n with
  | zero => simp [convolutionPower, mean, action_dirac]
  | succ n ih =>
      rw [convolutionPower, mean_convolution, ih]
      have hc : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by exact_mod_cast rfl
      rw [hc]
      grind

theorem variance_convolutionPower (a : FiniteProbabilityKernel) (n : Nat) :
    (a.convolutionPower n).variance = (n : Rat) * a.variance := by
  induction n with
  | zero =>
      simp [convolutionPower, variance, mean, action_dirac]
      grind
  | succ n ih =>
      rw [convolutionPower, variance_convolution, ih]
      have hc : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by exact_mod_cast rfl
      rw [hc]
      grind

/-- Finite Lindeberg telescoping: a uniform translated one-step bound costs
at most the number of replaced factors times that bound. -/
theorem convolutionPower_replacement_bound (a b : FiniteProbabilityKernel)
    (f : Rat → Rat) (error : Rat)
    (h : ∀ z, qabs (a.action (fun x => f (z + x)) -
      b.action (fun x => f (z + x))) ≤ error)
    (n : Nat) (z : Rat) :
    qabs ((a.convolutionPower n).action (fun x => f (z + x)) -
      (b.convolutionPower n).action (fun x => f (z + x))) ≤ (n : Rat) * error := by
  induction n generalizing z with
  | zero =>
      simp only [convolutionPower, action_dirac]
      have he : f (z + 0) - f (z + 0) = 0 := by grind
      rw [he]
      change qabs 0 ≤ 0 * error
      simp [qabs]
  | succ n ih =>
      let A := a.convolutionPower n
      let B := b.convolutionPower n
      let u := fun x => A.action (fun y => f (z + (x + y)))
      let v := fun x => B.action (fun y => f (z + (x + y)))
      have hfirst : qabs (a.action u - a.action v) ≤ (n : Rat) * error := by
        apply action_difference_le
        intro s _
        simpa only [u, v, A, B, Rat.add_assoc] using ih (z + s.point)
      have hsecond : qabs (a.action v - b.action v) ≤ error := by
        have hswapA := WeightedPoint.action_swap a.samples B.samples
          (fun x y => f (z + (x + y)))
        have hswapB := WeightedPoint.action_swap b.samples B.samples
          (fun x y => f (z + (x + y)))
        change a.action v = B.action (fun y => a.action (fun x => f (z + (x + y)))) at hswapA
        change b.action v = B.action (fun y => b.action (fun x => f (z + (x + y)))) at hswapB
        rw [hswapA, hswapB]
        apply action_difference_le
        intro s _
        have he : ∀ x : Rat, z + (x + s.point) = (z + s.point) + x := by intro x; grind
        simpa only [he] using h (z + s.point)
      rw [convolutionPower, convolutionPower, action_convolution, action_convolution]
      change qabs (a.action u - b.action v) ≤ _
      have he : a.action u - b.action v =
        (a.action u - a.action v) + (a.action v - b.action v) := by grind
      rw [he]
      have ht := qabs_add_le (a.action u - a.action v) (a.action v - b.action v)
      have hc : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by exact_mod_cast rfl
      rw [hc]
      grind only

/-- A finite, quantitative smooth-test comparison for rescaled convolution
powers. The caller supplies local quadratic remainder bounds. Gaussian
stability, continuous quadrature comparison, and CLT convergence are separate
analytic obligations, none of which is a field of this theorem. -/
theorem scaled_convolutionPower_cubic_bound (a b : FiniteProbabilityKernel)
    (hmean : a.mean = b.mean) (hsecond : a.secondMoment = b.secondMoment)
    (f c l q : Rat → Rat) (scale C : Rat)
    (ha : ∀ z s, s ∈ a.samples →
      qabs (f (z + scale * s.point) -
        (c z + l z * s.point + q z * (s.point * s.point))) ≤
        (C * (qabs scale * qabs scale * qabs scale)) *
          (qabs s.point * qabs s.point * qabs s.point))
    (hb : ∀ z s, s ∈ b.samples →
      qabs (f (z + scale * s.point) -
        (c z + l z * s.point + q z * (s.point * s.point))) ≤
        (C * (qabs scale * qabs scale * qabs scale)) *
          (qabs s.point * qabs s.point * qabs s.point))
    (n : Nat) :
    qabs ((a.convolutionPower n).action (fun x => f (scale * x)) -
      (b.convolutionPower n).action (fun x => f (scale * x))) ≤
      (n : Rat) * ((C * (qabs scale * qabs scale * qabs scale)) *
        (a.thirdAbsoluteMoment + b.thirdAbsoluteMoment)) := by
  have h := convolutionPower_replacement_bound a b (fun x => f (scale * x))
    ((C * (qabs scale * qabs scale * qabs scale)) *
      (a.thirdAbsoluteMoment + b.thirdAbsoluteMoment)) (by
        intro z
        simpa only [Rat.mul_add] using
          cubic_replacement_bound a b hmean hsecond
            (fun x => f (scale * z + scale * x))
            (c (scale * z)) (l (scale * z)) (q (scale * z))
            (C * (qabs scale * qabs scale * qabs scale))
            (ha (scale * z)) (hb (scale * z))) n 0
  simpa only [Rat.zero_add] using h

end FiniteProbabilityKernel
end ComputableAnalysis
