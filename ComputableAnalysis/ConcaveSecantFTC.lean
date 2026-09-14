import ComputableAnalysis.MonotonicityConvexity
import ComputableAnalysis.IntervalSelections
import ComputableAnalysis.DovetailedFTC

/-! Concave calculus for literal rational-interval algorithms. Supporting
secant bounds, a computed derivative, and the FTC remain separate claims. -/
namespace ComputableAnalysis
namespace ConcaveFTC
open IntervalSelections

abbrev valueRaw (F : RealFunRaw) (x : Rat) : RealRaw := { compute := F.compute x }

/-- Supporting slope data, stated without presupposing differentiation. -/
def SecantBounds (F : RealFunRaw) (D : Rat -> RealRaw) (a b : Rat) : Prop :=
  ∀ x y, inDomainInterval a b x -> inDomainInterval a b y -> x < y ->
    (D y).Le (secantRaw F x y) ∧ (secantRaw F x y).Le (D x)

/-- Finite supporting-line inequalities imply the exact raw-real secant
bounds. The proof divides only by a strictly positive rational. -/
theorem secant_bounds_of_selected_support
    (F : RealFunRaw) (D : Rat -> RealRaw) (f d : Rat -> Nat -> Rat)
    (a b : Rat)
    (hF : ∀ x, inDomainInterval a b x -> (valueRaw F x).Valid)
    (hD : ∀ x, inDomainInterval a b x -> (D x).Valid)
    (hf : ∀ x, inDomainInterval a b x -> ∀ n, InBox (f x n) (F.compute x n))
    (hd : ∀ x, inDomainInterval a b x -> ∀ n, InBox (d x n) ((D x).compute n))
    (hs : ∀ x y, inDomainInterval a b x -> inDomainInterval a b y ->
      ∀ eps : QPos, ∃ N, ∀ n, N <= n ->
        f y n-f x n <= (y-x)*d x n+eps.val ∧
        (y-x)*d y n <= f y n-f x n+eps.val) :
    SecantBounds F D a b := by
  intro x y hx hy hxy
  have hp : 0 < y-x := by grind
  have hi : 0 <= (y-x)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hp)
  have hc := Rat.mul_inv_cancel (y-x) (Rat.ne_of_gt hp)
  have hQ := secantRaw_valid_of_valid (hF x hx) (hF y hy) hxy
  let q := fun n => (f y n-f x n)/(y-x)
  have hq : ∀ n, InBox (q n) ((secantRaw F x y).compute n) :=
    fun n => secant_mem hxy n (hf x hx n) (hf y hy n)
  have hnear : ∀ eps : QPos, ∃ N, ∀ n, N <= n ->
      d y n <= q n+eps.val ∧ q n <= d x n+eps.val := by
    intro eps
    let eta : QPos := ⟨eps.val*(y-x), Rat.mul_pos eps.property hp⟩
    obtain ⟨N, hN⟩ := hs x y hx hy eta
    refine ⟨N, ?_⟩
    intro n hn
    have hh := hN n hn
    have hl := Rat.mul_le_mul_of_nonneg_right hh.2 hi
    have hu := Rat.mul_le_mul_of_nonneg_right hh.1 hi
    have he : eta.val*(y-x)⁻¹ = eps.val := by dsimp [eta]; grind
    have hdx : ((y-x)*d x n)*(y-x)⁻¹ = d x n := by grind
    have hdy : ((y-x)*d y n)*(y-x)⁻¹ = d y n := by grind
    rw [hdy, Rat.add_mul, he] at hl
    rw [Rat.add_mul, hdx, he] at hu
    dsimp [q]
    simp only [Rat.div_def]
    exact ⟨hl, hu⟩
  constructor
  · apply le_of_eventually (hD y hy) hQ (d y) q (hd y hy) hq
    intro eps
    obtain ⟨N, hN⟩ := hnear eps
    exact ⟨N, fun n hn => (hN n hn).1⟩
  · apply le_of_eventually hQ (hD x hx) q (d x) hq (hd x hx)
    intro eps
    obtain ⟨N, hN⟩ := hnear eps
    exact ⟨N, fun n hn => (hN n hn).2⟩

theorem slopes_antitone
    {F : RealFunRaw} {D : Rat -> RealRaw} {a b : Rat}
    (hF : ∀ x, inDomainInterval a b x -> (valueRaw F x).Valid)
    (hD : ∀ x, inDomainInterval a b x -> (D x).Valid)
    (hs : SecantBounds F D a b) {x y : Rat}
    (hx : inDomainInterval a b x) (hy : inDomainInterval a b y) (hxy : x <= y) :
    (D y).Le (D x) := by
  by_cases heq : x = y
  · subst y
    exact RealRaw.le_refl _ (hD x hx)
  · have hp : x < y := by grind
    have hh := hs x y hx hy hp
    exact RealRaw.le_trans
      (secantRaw_valid_of_valid (hF x hx) (hF y hy) hp) hh.1 hh.2

/-- The supporting-slope criterion proves concavity without using a
second derivative or a convexity-dependent derivative construction. -/
theorem concave_of_secant_bounds
    (F : RealFunRaw) (D : Rat -> RealRaw) (a b : Rat)
    (hdom : ∀ x, inDomainInterval a b x -> F.domain x)
    (hF : ∀ x, inDomainInterval a b x -> (valueRaw F x).Valid)
    (hD : ∀ x, inDomainInterval a b x -> (D x).Valid)
    (hs : SecantBounds F D a b) : ExactConcaveOn F a b where
  domain_on := hdom
  valid_on := hF
  secant_antimono := by
    intro w x y z hw hx hy hz hwx hxy hyz
    have hleft := hs w x hw hx hwx
    have hright := hs y z hy hz hyz
    have hmiddle := slopes_antitone hF hD hs hx hy hxy
    exact RealRaw.le_trans (hD y hy) hright.2
      (RealRaw.le_trans (hD x hx) hmiddle hleft.1)

/-- A particular concave function and supporting slope computation. The
following theorems verify, rather than assume, the secant derivative program. -/
structure DerivativeData (F : RealFunRaw) (D : Rat -> RealRaw) (a b : Rat) where
  concave : ExactConcaveOn F a b
  valid : ∀ x, inDomainInterval a b x -> (D x).Valid
  secants : SecantBounds F D a b
  K : Nat
  lipschitz : ∀ x y, inDomainInterval a b x -> inDomainInterval a b y ->
    ∀ n m, ((D y).compute n).lo <= ((D x).compute m).hi+(K : Rat)*qabs (y-x)

/-- Both indices are fixed in advance: h_k = radius/(k+1), while every
retained secant pair is evaluated at the current stage n. -/
def step (radius : QPos) (k : Nat) : Rat := radius.val/((k+1 : Nat) : Rat)

theorem step_pos (radius : QPos) (k : Nat) : 0 < step radius k := by
  unfold step
  rw [Rat.div_def]
  exact Rat.mul_pos radius.property
    ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.succ_pos k)))

theorem step_le_radius (radius : QPos) (k : Nat) : step radius k <= radius.val := by
  have hp : 0 < ((k+1 : Nat) : Rat) := (Rat.natCast_pos).2 (Nat.succ_pos k)
  have hi := Rat.le_of_lt ((Rat.inv_pos).2 hp)
  have hn : (1 : Rat) <= ((k+1 : Nat) : Rat) := by exact_mod_cast (by omega : 1 <= k+1)
  have hc := Rat.mul_inv_cancel ((k+1 : Nat) : Rat) (Rat.ne_of_gt hp)
  have hb := Rat.mul_le_mul_of_nonneg_right hn hi
  have hi1 : (((k+1 : Nat) : Rat))⁻¹ <= 1 := by grind
  have hm := Rat.mul_le_mul_of_nonneg_left hi1 (Rat.le_of_lt radius.property)
  simpa only [step, Rat.div_def, Rat.mul_one] using hm

def bracket (F : RealFunRaw) (x : Rat) (radius : QPos) (k n : Nat) : QInterval :=
  { lo := (secantSlopeIntervalOfRealFun F x (x+step radius k) n).lo
    hi := (secantSlopeIntervalOfRealFun F (x-step radius k) x n).hi }

/-- The derivative reads F only. Its domain of use explicitly includes the
concavity certificate; the candidate D is not a runtime input. -/
def derivative {F : RealFunRaw} {a b : Rat}
    (_H : ExactConcaveOn F a b) (x : Rat) (radius : QPos) : RealRaw :=
  Integral.Dovetail.ofBoxes (bracket F x radius)

private theorem step_points_mem {a b x : Rat} (r : QPos)
    (hl : a <= x-r.val) (hr : x+r.val <= b) (k : Nat) :
    inDomainInterval a b (x-step r k) ∧
    inDomainInterval a b x ∧ inDomainInterval a b (x+step r k) := by
  have hp := Rat.le_of_lt (step_pos r k)
  have hb := step_le_radius r k
  have rp := Rat.le_of_lt r.property
  unfold inDomainInterval
  constructor
  · constructor <;> grind
  constructor <;> constructor <;> grind

/-- Orderedness of all fixed secant brackets follows from concavity alone,
without an assumed derivative value. -/
theorem bracket_compatible {F : RealFunRaw} {a b x : Rat}
    (H : ExactConcaveOn F a b) (r : QPos)
    (hl : a <= x-r.val) (hr : x+r.val <= b) (k l q t : Nat) :
    (bracket F x r k q).lo <= (bracket F x r l t).hi := by
  have hk := step_points_mem r hl hr k
  have hh := step_points_mem r hl hr l
  have hkp := step_pos r k
  have hlp := step_pos r l
  exact H.secant_antimono (x-step r l) x x (x+step r k)
    hh.1 hh.2.1 hk.2.1 hk.2.2 (by grind) (Rat.le_refl) (by grind) q t

private theorem bracket_nested {F : RealFunRaw} {a b x : Rat}
    (H : ExactConcaveOn F a b) (r : QPos)
    (hl : a <= x-r.val) (hr : x+r.val <= b) (k q t : Nat) (hqt : q <= t) :
    (bracket F x r k q).ContainsInterval (bracket F x r k t) := by
  have hm := step_points_mem r hl hr k
  have hp := step_pos r k
  have hL := secantRaw_valid_of_valid (H.valid_on _ hm.1) (H.valid_on _ hm.2.1)
    (by grind : x-step r k < x)
  have hR := secantRaw_valid_of_valid (H.valid_on _ hm.2.1) (H.valid_on _ hm.2.2)
    (by grind : x < x+step r k)
  exact ⟨(hR.2.1 q t hqt).1, (hL.2.1 q t hqt).2.2⟩

/-- The candidate derivative lies in every retained secant bracket in the
all-stage overlap sense, not necessarily by containment of its whole box. -/
theorem bracket_overlaps {F : RealFunRaw} {D : Rat -> RealRaw} {a b x : Rat}
    (H : DerivativeData F D a b) (r : QPos)
    (hl : a <= x-r.val) (hr : x+r.val <= b) (k q t : Nat) :
    (bracket F x r k q).Overlaps ((D x).compute t) := by
  have hm := step_points_mem r hl hr k
  have hp := step_pos r k
  have hL := H.secants (x-step r k) x hm.1 hm.2.1 (by grind)
  have hR := H.secants x (x+step r k) hm.2.1 hm.2.2 (by grind)
  exact ⟨hR.2 q t, hL.1 t q⟩

private theorem bracket_small {F : RealFunRaw} {D : Rat -> RealRaw} {a b x : Rat}
    (H : DerivativeData F D a b) (r : QPos) (hr1 : r.val <= 1)
    (hl : a <= x-r.val) (hr : x+r.val <= b) :
    ∀ eps : QPos, ∃ k N, ∀ n, N <= n -> (bracket F x r k n).width <= eps.val := by
  have hshrink : ShrinksToZero (fun k => 2*(H.K : Rat)*step r k) := by
    apply shrinksToZero_of_natOverSuccBound (C := 2*H.K)
    intro k
    have hi : 0 <= (((k+1 : Nat) : Rat))⁻¹ :=
      Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.succ_pos k)))
    have hk0 : 0 <= (H.K : Rat) := by exact_mod_cast (Nat.zero_le H.K)
    have hh := Rat.mul_le_mul_of_nonneg_right hr1 hi
    have hm := Rat.mul_le_mul_of_nonneg_left hh (Rat.mul_nonneg (by decide : (0 : Rat) <= 2) hk0)
    have htwo : ((2 : Nat) : Rat) = (2 : Rat) := by decide +kernel
    simp only [step, Rat.div_def, Rat.natCast_mul, htwo]
    simpa only [Rat.mul_assoc, Rat.one_mul] using hm
  intro eps
  let half : QPos := ⟨eps.val/2, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  let eighth : QPos := ⟨eps.val/8, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  obtain ⟨k, hk⟩ := hshrink half
  have hm := step_points_mem r hl hr k
  have hp := step_pos r k
  let L := secantRaw F (x-step r k) x
  let R := secantRaw F x (x+step r k)
  have hL : L.Valid := secantRaw_valid_of_valid (H.concave.valid_on _ hm.1)
    (H.concave.valid_on _ hm.2.1) (by grind)
  have hR : R.Valid := secantRaw_valid_of_valid (H.concave.valid_on _ hm.2.1)
    (H.concave.valid_on _ hm.2.2) (by grind)
  obtain ⟨NL, hNL⟩ := hL.2.2 eighth
  obtain ⟨NR, hNR⟩ := hR.2.2 eighth
  obtain ⟨NDL, hNDL⟩ := (H.valid _ hm.1).2.2 eighth
  obtain ⟨NDR, hNDR⟩ := (H.valid _ hm.2.2).2.2 eighth
  refine ⟨k, max NL (max NR (max NDL NDR)), ?_⟩
  intro n hn
  have wL := hNL n (by omega)
  have wR := hNR n (by omega)
  have wDL := hNDL n (by omega)
  have wDR := hNDR n (by omega)
  have hleft := (H.secants (x-step r k) x hm.1 hm.2.1 (by grind)).2 n n
  have hright := (H.secants x (x+step r k) hm.2.1 hm.2.2 (by grind)).1 n n
  have hLip := H.lipschitz (x+step r k) (x-step r k) hm.2.2 hm.1 n n
  have he : qabs ((x-step r k)-(x+step r k)) = 2*step r k := by
    have heq : (x-step r k)-(x+step r k) = -(2*step r k) := by grind
    rw [heq, qabs_neg, qabs_eq_self_of_nonneg (Rat.mul_nonneg (by decide) (Rat.le_of_lt hp))]
  rw [he] at hLip
  have herr := hk k (Nat.le_refl k)
  change (L.compute n).lo <= ((D (x-step r k)).compute n).hi at hleft
  change ((D (x+step r k)).compute n).lo <= (R.compute n).hi at hright
  change (L.compute n).hi-(R.compute n).lo <= eps.val
  unfold QInterval.width at wL wR wDL wDR
  dsimp [eighth, half] at wL wR wDL wDR herr
  simp only [Rat.div_def] at wL wR wDL wDR herr
  grind

/-- A genuinely computed derivative: orderedness uses concavity, and
shrinking uses the specified secants and a proved quantitative slope bound. -/
theorem derivative_valid {F : RealFunRaw} {D : Rat -> RealRaw} {a b x : Rat}
    (H : DerivativeData F D a b) (r : QPos) (hr1 : r.val <= 1)
    (hl : a <= x-r.val) (hr : x+r.val <= b) :
    (derivative H.concave x r).Valid :=
  Integral.Dovetail.ofBoxes_valid (bracket_compatible H.concave r hl hr)
    (bracket_nested H.concave r hl hr) (bracket_small H r hr1 hl hr)

theorem derivative_equiv {F : RealFunRaw} {D : Rat -> RealRaw} {a b x : Rat}
    (H : DerivativeData F D a b) (r : QPos)
    (hl : a <= x-r.val) (hr : x+r.val <= b) :
    (derivative H.concave x r).Equiv (D x) :=
  Integral.Dovetail.ofBoxes_equiv (bracket_overlaps H r hl hr)

end ConcaveFTC
end ComputableAnalysis
