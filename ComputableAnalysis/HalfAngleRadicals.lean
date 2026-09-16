import ComputableAnalysis.ClosedArctanInverse
import ComputableAnalysis.DovetailedFTC

/-!
# Rationally enclosed nested half-angle radicals

At each outer stage the finite half-angle path is rebuilt with a prescribed
square-root precision. Only rational arithmetic and square bisection occur
in the runtime. The arctangent integral is an independent proof anchor.
-/
namespace ComputableAnalysis
namespace HalfAngleRadicals
open ArctanGeometry ClosedArctanInverse

private theorem le_of_slack {a b : Rat} (h : ∀ eps : QPos, a <= b+eps.val) : a <= b := by
  by_cases hab : a <= b
  · exact hab
  · let eps : QPos := ⟨(a-b)/2, by
      rw [Rat.div_def]; exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 (by decide))⟩
    have hh := h eps
    dsimp [eps] at hh
    simp only [Rat.div_def] at hh
    grind

def rootBox (u : Rat) (p : Nat) : QInterval := sqrtBisect (1+u*u) p {lo:=1,hi:=2}

def halfStep (u : Rat) (p : Nat) : Rat := u/(1+(rootBox u p).hi)

def path (p : Nat) : Nat -> Rat
  | 0 => 1
  | j+1 => halfStep (path p j) p

theorem rootBox_spec {u : Rat} (hu : Unit u) (p : Nat) :
    SqrtIntervalSpec (1+u*u) (rootBox u p) ∧
      1 <= (rootBox u p).lo ∧ (rootBox u p).hi <= 2 ∧
      (rootBox u p).width = meshRadius p := by
  have hs := Rat.mul_le_mul_of_nonneg_left hu.2 hu.1
  have hsq0 := Rat.mul_nonneg hu.1 hu.1
  have hi : SqrtIntervalSpec (1+u*u) {lo:=1,hi:=2} := by
    unfold SqrtIntervalSpec sq
    constructor
    · decide
    constructor
    · decide
    constructor <;> grind
  have hc := sqrtBisect_contains_of_le_fuel hi (Nat.zero_le p)
  have hw := sqrtBisect_width_eq (1+u*u) p ({lo:=1,hi:=2} : QInterval)
  have hcast : ((2^p : Nat) : Rat) = 2^p := by simp
  rw [show ({lo:=1,hi:=2} : QInterval).width = 1 by decide +kernel,hcast] at hw
  exact ⟨sqrtBisect_spec (1+u*u) p _ hi,hc.1,hc.2,hw⟩

/-- The half-angle formula with an upper square-root endpoint errs in a
known direction. The exact doubled slope is at most u and within 4 box widths. -/
theorem halfStep_algebra {u : Rat} (hu : Unit u) (p : Nat) :
    let v := halfStep u p
    let w := (v+v)/(1-v*v)
    0 <= v ∧ v <= u/2 ∧ 0 <= w ∧ w <= u ∧ u-w <= 4*meshRadius p := by
  have H := rootBox_spec hu p
  let l := (rootBox u p).lo
  let r := (rootBox u p).hi
  let v := halfStep u p
  let d := (1+r)*(1+r)-u*u
  have hs := H.1
  change 0 <= l ∧ l <= r ∧ l*l <= 1+u*u ∧ 1+u*u <= r*r at hs
  have hl : 1 <= l := H.2.1
  have hr : r <= 2 := H.2.2.1
  have hr1 : 1 <= r := by grind
  have hsq := Rat.mul_le_mul_of_nonneg_left hu.2 hu.1
  have hsq0 := Rat.mul_nonneg hu.1 hu.1
  have hd : 0 < d := by dsimp [d]; grind
  have hd1 : 1 <= d := by dsimp [d]; grind
  have hden : 0 < 1+r := by grind
  have hc := Rat.mul_inv_cancel (1+r) (Rat.ne_of_gt hden)
  have hdc := Rat.mul_inv_cancel d (Rat.ne_of_gt hd)
  have vi : v*(1+r)=u := by dsimp [v,halfStep]; change (u/(1+r))*(1+r)=u; simp only [Rat.div_def]; grind
  have v0 : 0 <= v := by
    dsimp [v,halfStep]
    rw [Rat.div_def]
    exact Rat.mul_nonneg hu.1 (Rat.le_of_lt ((Rat.inv_pos).2 hden))
  have vh : v <= u/2 := by
    have hm := Rat.mul_le_mul_of_nonneg_left hr1 v0
    simp only [Rat.div_def]
    grind
  have vhalf : v <= (1 : Rat)/2 := by simp only [Rat.div_def] at vh ⊢; grind
  have vv := Rat.mul_le_mul_of_nonneg_left vhalf v0
  have vd : 0 < 1-v*v := by simp only [Rat.div_def] at vhalf vv; grind
  have vc := Rat.mul_inv_cancel (1-v*v) (Rat.ne_of_gt vd)
  let w := (v+v)/(1-v*v)
  have w0 : 0 <= w := by
    dsimp [w]; rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind) (Rat.le_of_lt ((Rat.inv_pos).2 vd))
  have hid : (u-w)*d = u*(r*r-1-u*u) := by
    dsimp [w,d] at *
    simp only [Rat.div_def] at *
    grind
  have hu0r : 0 <= u*(r*r-1-u*u) := Rat.mul_nonneg hu.1 (by grind)
  have uw0 : 0 <= u-w := by
    have h := Rat.le_of_mul_le_mul_right (a:=0) (b:=u-w) (c:=d) (by rw [hid]; grind) hd
    exact h
  have hwidth : r-l = meshRadius p := H.2.2.2
  have hsum : r+l <= 4 := by grind
  have hw0 := Rat.le_of_lt (meshRadius_pos p)
  have he := Rat.mul_le_mul_of_nonneg_right hsum hw0
  have herr : r*r-1-u*u <= 4*meshRadius p := by
    have hdiff : r*r-l*l = (r+l)*(r-l) := by grind
    rw [hwidth] at hdiff
    grind
  have herr0 : 0 <= r*r-1-u*u := by grind
  have hum := Rat.mul_le_mul_of_nonneg_right hu.2 herr0
  have hlarger := Rat.mul_le_mul_of_nonneg_left hd1 uw0
  dsimp only
  change 0 <= v ∧ v <= u/2 ∧ 0 <= w ∧ w <= u ∧ _
  exact ⟨v0,vh,w0,by grind,by grind⟩

theorem path_unit (p j : Nat) : Unit (path p j) := by
  induction j with
  | zero => change Unit (1 : Rat); constructor <;> decide +kernel
  | succ j ih =>
    have h := halfStep_algebra ih p
    dsimp only at h
    change Unit (halfStep (path p j) p)
    exact ⟨h.1,by have hx:=ih.2; simp only [Rat.div_def] at h; grind⟩

theorem meshRadius_succ (n : Nat) : meshRadius (n+1) = meshRadius n/2 := by
  simp only [meshRadius,Rat.pow_succ,Rat.div_def,Rat.one_mul,Rat.inv_mul_rev]
  exact Rat.mul_comm _ _

theorem path_small (p j : Nat) : path p j <= meshRadius j := by
  induction j with
  | zero => change (1 : Rat) <= meshRadius 0; decide +kernel
  | succ j ih =>
    have h := (halfStep_algebra (path_unit p j) p).2.1
    rw [path,meshRadius_succ]
    simp only [Rat.div_def] at h ⊢
    grind

/-- The finite arctangent addition theorem, transported to rectangle boxes. -/
theorem clock_double {v : Rat} (hv0 : 0 <= v) (hvhalf : v <= (1 : Rat)/2)
    (hw : (v+v)/(1-v*v) <= 1) :
    (arctanIntegralRectangleRaw v + arctanIntegralRectangleRaw v).Equiv
      (arctanIntegralRectangleRaw ((v+v)/(1-v*v))) := by
  have hv1 : v <= 1 := by simp only [Rat.div_def] at hvhalf; grind
  have vsq := Rat.mul_le_mul_of_nonneg_left hvhalf hv0
  have vd : 0 < 1-v*v := by simp only [Rat.div_def] at vsq hvhalf; grind
  have hw0 : 0 <= (v+v)/(1-v*v) := by
    rw [Rat.div_def]; exact Rat.mul_nonneg (by grind) (Rat.le_of_lt ((Rat.inv_pos).2 vd))
  have hV := arctanIntegralRectangleRaw_valid hv0 hv1
  have hG := arctanGeom_valid_on_unit hv0 hv1
  have hW := arctanIntegralRectangleRaw_valid hw0 hw
  have hGW := arctanGeom_valid_on_unit hw0 hw
  have hg := arctanGeom_chartAdd_add_of_half hv0 hvhalf hv0 hv1 hw
  have hb := arctanIntegralRectangleRaw_equiv_arctanGeom hv0
  exact RealRaw.equiv_trans (RealRaw.add_valid hV hV) (RealRaw.add_valid hG hG) hW
    (RealRaw.add_equiv hV hG hV hG hb hb)
    (RealRaw.equiv_trans (RealRaw.add_valid hG hG) hGW hW hg
      (RealRaw.equiv_symm (arctanIntegralRectangleRaw_equiv_arctanGeom hw0)))

theorem halfStep_clock {u : Rat} (hu : Unit u) (p n m : Nat) :
    2*(A (halfStep u p) n).lo <= (A u m).hi ∧
      (A u m).lo <= 2*(A (halfStep u p) n).hi+4*meshRadius p := by
  let v := halfStep u p
  let w := (v+v)/(1-v*v)
  have h := halfStep_algebra hu p
  dsimp only at h
  have hvhalf : v <= (1 : Rat)/2 := by have hx:=hu.2; simp only [Rat.div_def] at h ⊢; grind
  have hv : Unit v := ⟨h.1,by simp only [Rat.div_def] at hvhalf; grind⟩
  have hw : Unit w := ⟨h.2.2.1,Rat.le_trans h.2.2.2.1 hu.2⟩
  have hAw := arctanIntegralRectangleRaw_valid hw.1 hw.2
  have hAv := arctanIntegralRectangleRaw_valid hv.1 hv.2
  have heq := clock_double hv.1 hvhalf hw.2
  have hevery := RealRaw.allStagesOverlap_of_equiv (RealRaw.add_valid hAv hAv) hAw heq
  have hs : ∀ eps : QPos,
      2*(A v n).lo <= (A u m).hi+eps.val ∧
      (A u m).lo <= (2*(A v n).hi+4*meshRadius p)+eps.val := by
    intro eps
    obtain ⟨K,hK⟩ := hAw.2.2 eps
    have ww := hK K (Nat.le_refl K)
    change (A w K).width <= eps.val at ww
    have hb := (RealRaw.compareAt_overlap_iff _ _ n K).1 (hevery n K)
    change (A v n).lo+(A v n).lo <= (A w K).hi ∧
      (A w K).lo <= (A v n).hi+(A v n).hi at hb
    have hm := clock_increment hw hu h.2.2.2.1 K m
    have he := h.2.2.2.2
    change u-w <= 4*meshRadius p at he
    unfold QInterval.width at ww
    simp only [Rat.div_def] at hm
    constructor <;> grind
  exact ⟨le_of_slack (fun eps => (hs eps).1),le_of_slack (fun eps => (hs eps).2)⟩

/-- The accumulated halving error is explicit; the clock is not evaluated
by the final program. All q,r are independent output stages. -/
theorem path_clock (p j q r : Nat) :
    (2^j : Rat)*(A (path p j) r).lo <= (A 1 q).hi ∧
      (A 1 q).lo <= (2^j : Rat)*(A (path p j) r).hi+
        ((2^j : Rat)-1)*(4*meshRadius p) := by
  induction j generalizing r with
  | zero =>
    have hov := (RealRaw.compareAt_overlap_iff _ _ r q).1
      (RealRaw.allStagesOverlap_refl (arctanIntegralRectangleRaw 1)
        (arctanIntegralRectangleRaw_valid (by decide) (by decide)) r q)
    change (A 1 r).lo <= (A 1 q).hi ∧ (A 1 q).lo <= (A 1 r).hi at hov
    simpa only [path,Rat.pow_zero,Rat.one_mul,Rat.sub_self,Rat.zero_mul,Rat.add_zero] using hov
  | succ j ih =>
    let s : Rat := 2^j
    have sp : 0 < s := Rat.pow_pos (by decide)
    have s0 := Rat.le_of_lt sp
    have hs : ∀ eps : QPos,
        s*2*(A (path p (j+1)) r).lo <= (A 1 q).hi+eps.val ∧
        (A 1 q).lo <= s*2*(A (path p (j+1)) r).hi+
          (s*2-1)*(4*meshRadius p)+eps.val := by
      intro eps
      let eta : QPos := ⟨eps.val/s, by
        rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 sp)⟩
      have hU := path_unit p j
      obtain ⟨K,hK⟩ := (arctanIntegralRectangleRaw_valid hU.1 hU.2).2.2 eta
      have ww := hK K (Nat.le_refl K)
      change (A (path p j) K).width <= eta.val at ww
      have hstep := halfStep_clock hU p r K
      change 2*(A (path p (j+1)) r).lo <= (A (path p j) K).hi ∧
        (A (path p j) K).lo <= 2*(A (path p (j+1)) r).hi+4*meshRadius p at hstep
      have hPrev := ih K
      change s*(A (path p j) K).lo <= _ ∧ _ <= s*(A (path p j) K).hi+(s-1)*(4*meshRadius p) at hPrev
      have hl := Rat.mul_le_mul_of_nonneg_left hstep.1 s0
      have hh := Rat.mul_le_mul_of_nonneg_left hstep.2 s0
      have hw := Rat.mul_le_mul_of_nonneg_left ww s0
      have hc := Rat.mul_inv_cancel s (Rat.ne_of_gt sp)
      have hbudget : s*eta.val = eps.val := by dsimp [eta]; simp only [Rat.div_def]; grind
      rw [hbudget] at hw
      unfold QInterval.width at hw
      constructor <;> grind
    rw [Rat.pow_succ]
    exact ⟨le_of_slack (fun eps => (hs eps).1),le_of_slack (fun eps => (hs eps).2)⟩

end HalfAngleRadicals
end ComputableAnalysis
