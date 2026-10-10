import Init.Grind.Ordered.Rat

/-!
Finite arithmetic for rational boundary sampling and radial-shell exhaustion.
No integral, completed real, sphere-volume hypothesis, or Gamma function.
The geometric interpretation is stated separately in the chapter.
-/
namespace ComputableAnalysis.RationalBall

def sum (xs : List Rat) : Rat := xs.foldr (· + ·) 0

theorem sum_mul (xs : List Rat) (c : Rat) :
    sum (xs.map (fun x => c * x)) = c * sum xs := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih =>
    change c * x + sum (xs.map (fun y => c * y)) = c * (x + sum xs)
    rw [ih]; grind [Rat.mul_add]

def normSq (xs : List Rat) : Rat := sum (xs.map (fun x => x*x))

def sphereChart (xs : List Rat) : List Rat :=
  let s := normSq xs
  xs.map (fun x => 2*x/(1+s)) ++ [(1-s)/(1+s)]

theorem normSq_nonneg (xs : List Rat) : 0 ≤ normSq xs := by
  induction xs with
  | nil => simp [normSq, sum]
  | cons x xs ih =>
    change 0 ≤ x*x + normSq xs
    have hx : 0 ≤ x*x := by
      by_cases h : 0 ≤ x
      · exact Rat.mul_nonneg h h
      · have h' : x ≤ 0 := by grind
        have hh := Rat.mul_nonneg (a := -x) (b := -x) (by grind) (by grind)
        simpa only [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] using hh
    grind

private theorem normSq_append (xs ys : List Rat) :
    normSq (xs++ys) = normSq xs + normSq ys := by
  induction xs with
  | nil => simp [normSq, sum]; grind
  | cons x xs ih =>
    change x*x + normSq (xs++ys) = (x*x+normSq xs)+normSq ys
    rw [ih]; grind

private theorem normSq_scale (xs : List Rat) (c : Rat) :
    normSq (xs.map (fun x => c*x)) = c*c*normSq xs := by
  induction xs with
  | nil => simp [normSq, sum]
  | cons x xs ih =>
    change (c*x)*(c*x) + normSq (xs.map (fun x => c*x)) = c*c*(x*x+normSq xs)
    rw [ih]; grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

/-- Rational stereographic coordinates satisfy the exact unit equation
in every list dimension. -/
theorem sphereChart_unit (xs : List Rat) : normSq (sphereChart xs) = 1 := by
  have hs := normSq_nonneg xs
  have hd : 1 + normSq xs ≠ 0 := by grind
  have he : xs.map (fun x => 2*x/(1+normSq xs)) =
      xs.map (fun x => (2/(1+normSq xs))*x) := by
    congr 1; funext x; grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  change normSq (xs.map (fun x => 2*x/(1+normSq xs)) ++ [(1-normSq xs)/(1+normSq xs)]) = 1
  rw [he, normSq_append, normSq_scale]
  simp only [normSq, sum, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Rat.add_zero]
  change (2/(1+normSq xs))*(2/(1+normSq xs))*normSq xs +
    ((1-normSq xs)/(1+normSq xs))*((1-normSq xs)/(1+normSq xs)) = 1
  generalize normSq xs = s at hd ⊢
  have hc := Rat.mul_inv_cancel (1+s) hd
  grind only [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul]

/-- The single chart stays in the positive orthant on its rational parameter ball. -/
theorem sphereChart_components_nonnegative (xs : List Rat)
    (hpositive : ∀ x ∈ xs, 0 ≤ x) (hball : normSq xs ≤ 1) :
    (∀ x ∈ xs, 0 ≤ 2*x/(1+normSq xs)) ∧
      0 ≤ (1-normSq xs)/(1+normSq xs) := by
  have hden : 0 < 1+normSq xs := by have hs := normSq_nonneg xs; grind
  have hinv : 0 ≤ (1+normSq xs)⁻¹ := by have hi := Rat.inv_pos.mpr hden; grind
  constructor
  · intro x hx
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.mul_nonneg (by decide) (hpositive x hx)) hinv
  · rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind) hinv

theorem sphereChart_positiveOrthant (xs : List Rat)
    (hpositive : ∀ x ∈ xs, 0 ≤ x) (hball : normSq xs ≤ 1) :
    normSq (sphereChart xs) = 1 ∧ ∀ y ∈ sphereChart xs, 0 ≤ y := by
  refine ⟨sphereChart_unit xs, ?_⟩
  intro y hy
  have hparts := sphereChart_components_nonnegative xs hpositive hball
  change y ∈ xs.map (fun x => 2*x/(1+normSq xs)) ++
    [(1-normSq xs)/(1+normSq xs)] at hy
  rcases List.mem_append.mp hy with hy | hy
  · rcases List.mem_map.mp hy with ⟨x,hx,rfl⟩
    exact hparts.1 x hx
  · have he : y = (1-normSq xs)/(1+normSq xs) := by simpa using hy
    rw [he]; exact hparts.2

/-- Difference of powers, proved by finite recursion. -/
def powerTerms (a b : Rat) : Nat → Rat
  | 0 => 0
  | k+1 => b^k + a * powerTerms a b k

theorem power_difference (a b : Rat) (k : Nat) :
    b^k - a^k = (b-a)*powerTerms a b k := by
  induction k with
  | zero => simp [powerTerms]; grind
  | succ k ih =>
    simp only [powerTerms, Rat.pow_succ]
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem power_mono {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (k : Nat) :
    a^k ≤ b^k := by
  have hb : 0 ≤ b := by grind
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Rat.pow_succ, Rat.pow_succ]
    have h1 := Rat.mul_le_mul_of_nonneg_right ih ha
    have h2 := Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg hb (n := k))
    grind

/-- Derivative-free bounds for the finite difference of every power. -/
theorem powerTerms_bounds {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (k : Nat) :
    ((k+1 : Nat) : Rat)*a^k ≤ powerTerms a b (k+1) ∧
      powerTerms a b (k+1) ≤ ((k+1 : Nat) : Rat)*b^k := by
  have hb : 0 ≤ b := by grind
  induction k with
  | zero => simp [powerTerms]; grind
  | succ k ih =>
    have hpow := power_mono ha hab (k+1)
    have hlo := Rat.mul_le_mul_of_nonneg_left ih.1 ha
    have hhi := Rat.mul_le_mul_of_nonneg_left ih.2 ha
    have hc : 0 ≤ ((k+1 : Nat) : Rat)*b^k :=
      Rat.mul_nonneg Rat.natCast_nonneg (Rat.pow_nonneg hb)
    have hm := Rat.mul_le_mul_of_nonneg_right hab hc
    simp only [powerTerms] at *
    rw [Rat.pow_succ, Rat.pow_succ] at hpow ⊢
    constructor <;> grind [Rat.natCast_add, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]

theorem power_cell_bounds {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (k : Nat) :
    (b-a)*(((k+1 : Nat) : Rat)*a^k) ≤ b^(k+1)-a^(k+1) ∧
      b^(k+1)-a^(k+1) ≤ (b-a)*(((k+1 : Nat) : Rat)*b^k) := by
  have hd : 0 ≤ b-a := by grind
  rw [power_difference]
  exact ⟨Rat.mul_le_mul_of_nonneg_left (powerTerms_bounds ha hab k).1 hd,
    Rat.mul_le_mul_of_nonneg_left (powerTerms_bounds ha hab k).2 hd⟩

def ordered (a : Rat) : List Rat → Prop
  | [] => True
  | b::rest => a ≤ b ∧ ordered b rest

def leftPowerSum (k : Nat) (a : Rat) : List Rat → Rat
  | [] => 0
  | b::rest => (b-a)*a^k + leftPowerSum k b rest

def rightPowerSum (k : Nat) (a : Rat) : List Rat → Rat
  | [] => 0
  | b::rest => (b-a)*b^k + rightPowerSum k b rest

def lastPoint (a : Rat) : List Rat → Rat
  | [] => a
  | b::rest => lastPoint b rest

/-- Every increasing rational partition satisfies the power-sum sandwich. -/
theorem partition_power_bounds (k : Nat) (a : Rat) (rest : List Rat)
    (ha : 0 ≤ a) (horder : ordered a rest) :
    ((k+1 : Nat) : Rat)*leftPowerSum k a rest ≤
        (lastPoint a rest)^(k+1)-a^(k+1) ∧
    (lastPoint a rest)^(k+1)-a^(k+1) ≤
        ((k+1 : Nat) : Rat)*rightPowerSum k a rest := by
  induction rest generalizing a with
  | nil => simp [leftPowerSum, rightPowerSum, lastPoint]; constructor <;> grind
  | cons b rest ih =>
    have ho : a ≤ b ∧ ordered b rest := horder
    have hb : 0 ≤ b := by grind
    have hc := power_cell_bounds ha ho.1 k
    have ht := ih b hb ho.2
    simp only [leftPowerSum, rightPowerSum, lastPoint]
    constructor <;> grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

def meshBound (d a : Rat) : List Rat → Prop
  | [] => True
  | b::rest => a ≤ b ∧ b-a ≤ d ∧ meshBound d b rest

/-- The gap between the two sums is bounded by mesh times the telescoping
power difference. No limiting integral theorem is used. -/
theorem partition_power_gap (k : Nat) (d a : Rat) (rest : List Rat)
    (ha : 0 ≤ a) (hm : meshBound d a rest) :
    0 ≤ rightPowerSum k a rest - leftPowerSum k a rest ∧
    rightPowerSum k a rest - leftPowerSum k a rest ≤
      d*((lastPoint a rest)^k-a^k) := by
  induction rest generalizing a with
  | nil => simp [leftPowerSum, rightPowerSum, lastPoint]; constructor <;> grind
  | cons b rest ih =>
    have ho : a ≤ b ∧ b-a ≤ d ∧ meshBound d b rest := hm
    have hb : 0 ≤ b := by grind
    have hd : 0 ≤ b-a := by grind
    have hp := power_mono ha ho.1 k
    have hpd : 0 ≤ b^k-a^k := by grind
    have hpos := Rat.mul_nonneg hd hpd
    have hbound := Rat.mul_le_mul_of_nonneg_right ho.2.1 hpd
    have ht := ih b hb ho.2.2
    simp only [leftPowerSum, rightPowerSum, lastPoint]
    constructor <;> grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

private theorem mesh_order (d a : Rat) (rest : List Rat)
    (hm : meshBound d a rest) : ordered a rest := by
  induction rest generalizing a with
  | nil => trivial
  | cons b rest ih => exact ⟨hm.1, ih b hm.2.2⟩

/-- A normalized partition gives an explicit rational error schedule for
all positive powers. This is finite arithmetic, not an integral statement. -/
theorem unit_partition_power_estimate (k : Nat) (hk : 0 < k)
    (d : Rat) (rest : List Rat) (hm : meshBound d 0 rest)
    (hend : lastPoint 0 rest = 1) :
    leftPowerSum k 0 rest ≤ 1 / ((k+1 : Nat) : Rat) ∧
      1 / ((k+1 : Nat) : Rat) - leftPowerSum k 0 rest ≤ d := by
  have ho := mesh_order d 0 rest hm
  have hb := partition_power_bounds k 0 rest (by decide) ho
  have hg := partition_power_gap k d 0 rest (by decide) hm
  have hp : (0 : Rat)^k = 0 := by
    cases k with
    | zero => omega
    | succ k => simp [Rat.pow_succ]
  have hp' : (0 : Rat)^(k+1) = 0 := by simp [Rat.pow_succ]
  rw [hend] at hb hg
  have hone : ∀ m : Nat, (1 : Rat)^m = 1 := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [Rat.pow_succ, ih, Rat.one_mul]
  rw [hp', hone (k+1)] at hb
  rw [hp, hone k] at hg
  have hb' : ((k+1 : Nat) : Rat)*leftPowerSum k 0 rest ≤ 1 ∧
      1 ≤ ((k+1 : Nat) : Rat)*rightPowerSum k 0 rest := by grind
  have hg' : rightPowerSum k 0 rest-leftPowerSum k 0 rest ≤ d := by grind
  have hc : 0 < ((k+1 : Nat) : Rat) := Rat.natCast_pos.mpr (Nat.succ_pos k)
  have hn : ((k+1 : Nat) : Rat) ≠ 0 := by grind
  have hi := Rat.mul_inv_cancel ((k+1 : Nat) : Rat) hn
  have he : ((k+1 : Nat) : Rat) * (1 / ((k+1 : Nat) : Rat)) = 1 := by
    simpa only [Rat.div_def, Rat.one_mul] using hi
  have hl := Rat.le_of_mul_le_mul_left (c := ((k+1 : Nat) : Rat))
    (a := leftPowerSum k 0 rest) (b := 1 / ((k+1 : Nat) : Rat))
    (by rw [he]; exact hb'.1) hc
  have hr := Rat.le_of_mul_le_mul_left (c := ((k+1 : Nat) : Rat))
    (a := 1 / ((k+1 : Nat) : Rat)) (b := rightPowerSum k 0 rest)
    (by rw [he]; exact hb'.2) hc
  exact ⟨hl, by grind⟩

/-- Finite sums along adjacent partition points; these are rational sums. -/
def shellLower (n : Nat) : List Rat → Rat
  | a::b::rest => (1-b*b)*(b^n-a^n) + shellLower n (b::rest)
  | _ => 0

def shellUpper (n : Nat) : List Rat → Rat
  | a::b::rest => (1-a*a)*(b^n-a^n) + shellUpper n (b::rest)
  | _ => 0

def moment (n : Nat) : List Rat → Rat
  | a::b::rest => a^n*(b*b-a*a) + moment n (b::rest)
  | _ => 0

def shellGap (n : Nat) : List Rat → Rat
  | a::b::rest => (b*b-a*a)*(b^n-a^n) + shellGap n (b::rest)
  | _ => 0

def edgeTerm (n : Nat) (a : Rat) : Rat := (1-a*a)*a^n

theorem shells_gap (n : Nat) (points : List Rat) :
    shellUpper n points - shellLower n points = shellGap n points := by
  induction points with
  | nil => simp [shellUpper, shellLower, shellGap]; grind
  | cons a points ih =>
    cases points with
    | nil => simp [shellUpper, shellLower, shellGap]; grind
    | cons b rest =>
      change (1-a*a)*(b^n-a^n)+shellUpper n (b::rest) -
        ((1-b*b)*(b^n-a^n)+shellLower n (b::rest)) =
          (b*b-a*a)*(b^n-a^n)+shellGap n (b::rest)
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- Summation by parts with both endpoint terms retained. -/
theorem shells_by_parts (n : Nat) (a : Rat) (rest : List Rat) :
    shellLower n (a::rest) = moment n (a::rest) +
      edgeTerm n (lastPoint a rest) - edgeTerm n a := by
  induction rest generalizing a with
  | nil => simp [shellLower, moment, lastPoint]; grind
  | cons b rest ih =>
    change (1-b*b)*(b^n-a^n)+shellLower n (b::rest) =
      a^n*(b*b-a*a)+moment n (b::rest)+
      edgeTerm n (lastPoint a (b::rest))-edgeTerm n a
    rw [ih b]
    simp only [lastPoint]
    unfold edgeTerm
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- The last endpoint is one and the first zero, with positive dimension. -/
theorem shells_zero_one (n : Nat) (hn : 0 < n) (rest : List Rat)
    (hlast : lastPoint 0 rest = 1) :
    shellLower n (0::rest) = moment n (0::rest) := by
  rw [shells_by_parts, hlast]
  have hz : (0 : Rat)^n = 0 := by
    cases n with
    | zero => omega
    | succ n => simp [Rat.pow_succ]
  simp [edgeTerm, hz]; grind

end ComputableAnalysis.RationalBall
