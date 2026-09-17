import ComputableAnalysis.MonotoneSampleIntegral
import ComputableAnalysis.RationalSampleLimits

/-! A finite quadrature for a supplied bounded rational function and a concrete
Lipschitz bound. This is a constructor with data, not an integrability predicate.
It is useful for polynomial integrands with finitely many turns. -/
namespace ComputableAnalysis.RationalLipschitzIntegral
open ClosedArctanInverse MonotoneAverage RationalSampleLimits

abbrev Lipschitz (f : Rat → Rat) (L : Rat) : Prop :=
  ∀ a b, Unit a → Unit b → qabs (f a-f b)≤L*qabs (a-b)

private theorem left_near (f : Rat → Rat) (L : Rat) (hL : 0≤L) (hf : Lipschitz f L)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a≤b) (n : Nat) :
    qabs (left f a b n-f a)≤L*(b-a) := by
  induction n generalizing a b with
  | zero =>
    change qabs (f a-f a)≤L*(b-a)
    rw [Rat.sub_self,qabs_eq_self_of_nonneg (by decide)]
    exact Rat.mul_nonneg hL (by grind)
  | succ n ih =>
    let m : Rat := (a+b)/2
    have hm:=midpoint_unit ha hb
    have hbet:=midpoint_between hab
    have h1:=ih ha hm hbet.1
    have h2:=ih hm hb hbet.2
    have h3:=hf ((a+b)/2) a hm ha
    rw [qabs_eq_self_of_nonneg (by have h:=hbet.1;grind : 0≤(a+b)/2-a)] at h3
    have ht:=qabs_add_le (left f a m n-f a) (left f m b n-f m)
    have htt:=qabs_add_le ((left f a m n-f a)+(left f m b n-f m)) (f m-f a)
    have he : (left f a m n-f a)+(left f m b n-f m)+(f m-f a)=
      2*(left f a b (n+1)-f a) := by
      simp only [left];dsimp [m];simp only [Rat.div_def];grind only
    rw [he,qabs_mul,show qabs (2:Rat)=2 by decide +kernel] at htt
    change qabs (left f a m n-f a)≤L*(m-a) at h1
    change qabs (left f m b n-f m)≤L*(b-m) at h2
    change qabs (f m-f a)≤L*(m-a) at h3
    have hnon:=Rat.mul_nonneg hL (show 0≤b-a by grind)
    dsimp [m] at h1 h2 h3
    simp only [Rat.div_def] at h1 h2 h3
    grind only

theorem refinement (f : Rat → Rat) (L : Rat) (hL : 0≤L) (hf : Lipschitz f L)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a≤b) (d k : Nat) :
    qabs (left f a b (d+k)-left f a b d)≤L*(b-a)*meshRadius d := by
  induction d generalizing a b with
  | zero =>
    rw [Nat.zero_add,show meshRadius 0=(1:Rat) by decide +kernel,Rat.mul_one]
    exact left_near f L hL hf ha hb hab k
  | succ d ih =>
    let m : Rat:=(a+b)/2
    have hm:=midpoint_unit ha hb;have hbet:=midpoint_between hab
    have h1:=ih ha hm hbet.1
    have h2:=ih hm hb hbet.2
    have ht:=qabs_add_le (left f a m (d+k)-left f a m d)
      (left f m b (d+k)-left f m b d)
    have he : (left f a m (d+k)-left f a m d)+(left f m b (d+k)-left f m b d)=
      2*(left f a b ((d+1)+k)-left f a b (d+1)) := by
      rw [show (d+1)+k=(d+k)+1 by omega]
      simp only [left];dsimp [m];simp only [Rat.div_def];grind only
    rw [he,qabs_mul,show qabs (2:Rat)=2 by decide +kernel] at ht
    have hr : meshRadius (d+1)=meshRadius d/2 := by
      simp only [meshRadius,Rat.pow_succ,Rat.div_def,Rat.one_mul,Rat.inv_mul_rev];exact Rat.mul_comm _ _
    rw [hr]
    simp only [Rat.div_def] at h1 h2 ⊢
    grind only

theorem mesh_error (f : Rat → Rat) (L : Rat) (hL : 0≤L) (hf : Lipschitz f L)
    (d q : Nat) (hdq : d≤q) :
    qabs (left f 0 1 q-left f 0 1 d)≤L*meshRadius d := by
  have h:=refinement f L hL hf (a:=0) (b:=1)
    ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ (by decide) d (q-d)
  rw [show d+(q-d)=q by omega,show (1:Rat)-0=1 by decide +kernel,Rat.mul_one] at h
  exact h

structure Data where
  sample : Rat → Rat
  range : ∀ x, Unit x → Unit (sample x)
  constant : Nat
  bound : Lipschitz sample (constant:Rat)

def centre (D : Data) (k : Nat) : Rat := left D.sample 0 1 k
def radius (D : Data) (k : Nat) : Rat := (D.constant:Rat)*meshRadius k

def candidate (D : Data) : RealRaw where
  compute := fun k=>{lo:=centre D k,hi:=centre D k}

theorem centre_unit (D : Data) (k : Nat) : Unit (centre D k) :=
  left_bounds D.sample 0 1 D.range ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ k

theorem future (D : Data) (k m : Nat) (hkm : k≤m) :
    (QInterval.expand ((candidate D).compute k) (radius D k)).ContainsInterval ((candidate D).compute m) := by
  have h:=mesh_error D.sample D.constant Rat.natCast_nonneg D.bound k m hkm
  have hp:=self_le_qabs (centre D m-centre D k)
  have hn:=neg_qabs_le_self (centre D m-centre D k)
  change qabs (centre D m-centre D k)≤radius D k at h
  change centre D k-radius D k≤centre D m ∧ centre D m≤centre D k+radius D k
  constructor <;> grind only

theorem radius_shrinks (D : Data) : ShrinksToZero (radius D) := by
  apply shrinksToZero_of_natOverSuccBound (C:=D.constant)
  intro n
  have h:=Rat.mul_le_mul_of_nonneg_left (meshRadius_le n) (Rat.natCast_nonneg (a:=D.constant))
  simpa only [radius,Rat.div_def,Rat.one_mul] using h

def stabilized (D : Data) : RealRaw := RealRaw.prefixStabilize (candidate D) (radius D)

theorem stabilized_valid (D : Data) : (stabilized D).Valid := by
  apply RealRaw.prefixStabilize_valid_of_future (candidate:=candidate D) (radius:=radius D)
    (fun k=>by change 0≤centre D k-centre D k;grind)
  · intro eps
    exact ⟨0,fun k _=>by change centre D k-centre D k≤eps.val;have h:=eps.property;grind⟩
  · exact future D
  · exact radius_shrinks D

def raw (D : Data) : RealRaw where
  compute := fun k=>QInterval.intersection {lo:=0,hi:=1} ((stabilized D).compute k)

theorem contains_future (D : Data) (k m : Nat) (hkm : k≤m) :
    ((raw D).compute k).ContainsInterval ((candidate D).compute m) :=
  QInterval.intersection_contains (centre_unit D m)
    (RealRaw.prefixStabilize_contains_future (future D) k m hkm)

theorem range (D : Data) (k : Nat) : subintervalOf ((raw D).compute k) 0 1 := by
  have h:=contains_future D k k (Nat.le_refl k)
  have hc:=QInterval.intersection_contained_left ({lo:=0,hi:=1}:QInterval) ((stabilized D).compute k)
  exact ⟨hc.1,Rat.le_trans h.1 h.2,hc.2⟩

theorem valid (D : Data) : (raw D).Valid := by
  have H:=stabilized_valid D
  refine ⟨?_,?_,?_⟩
  · intro k
    have h:=(range D k).2.1
    change 0≤((raw D).compute k).hi-((raw D).compute k).lo;grind
  · intro k m hkm
    have h:=H.2.1 k m hkm
    exact ⟨by change max 0 _≤max 0 _;grind,(range D m).2.1,
      by change min 1 _≤min 1 _;grind⟩
  · intro eps
    obtain ⟨N,hN⟩:=H.2.2 eps
    exact ⟨N,fun k hk=>Rat.le_trans (QInterval.width_le_of_contains
      (QInterval.intersection_contained_right ({lo:=0,hi:=1}:QInterval) ((stabilized D).compute k))) (hN k hk)⟩


/-- The fixed subdivision schedule has an explicit enclosure-width certificate. -/
theorem width (D : Data) (n : Nat) : ((raw D).compute n).width ≤ 2*radius D n := by
  have h1:=QInterval.width_le_of_contains
    (QInterval.intersection_contained_right ({lo:=0,hi:=1}:QInterval) ((stabilized D).compute n))
  have h2:=RealRaw.prefixStabilize_width_le_current_expand (candidate D) (radius D) n
  have hz : ((candidate D).compute n).width=0 := by change centre D n-centre D n=0; grind
  rw [hz] at h2
  change ((raw D).compute n).width ≤ _ at h1
  change ((stabilized D).compute n).width ≤ _ at h2
  grind

end ComputableAnalysis.RationalLipschitzIntegral
