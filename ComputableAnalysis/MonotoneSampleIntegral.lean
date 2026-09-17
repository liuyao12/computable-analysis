import ComputableAnalysis.MonotoneAverage

/-! A particular successful joint schedule for uniformly controlled monotone
sample algorithms. This is a finite construction, not an integrability predicate. -/
namespace ComputableAnalysis.MonotoneSampleIntegral
open ClosedArctanInverse MonotoneAverage

structure Data where
  sample : Rat → Nat → Rat
  bound : ∀ x q, Unit x → 0 ≤ sample x q ∧ sample x q ≤ 1
  decreasing : ∀ q, MonotoneAverage.Decreases (fun x => sample x q)
  errorConstant : Nat
  evaluation_error : ∀ x, Unit x → ∀ q r,
    qabs (sample x q-sample x r) ≤ (errorConstant:Rat)*(meshRadius q+meshRadius r)

def centre (D : Data) (k : Nat) : Rat := left (fun x => D.sample x k) 0 1 k

def radius (D : Data) (k : Nat) : Rat := (1+2*(D.errorConstant:Rat))*meshRadius k

def candidate (D : Data) : RealRaw where
  compute := fun k => {lo:=centre D k,hi:=centre D k}

theorem centre_unit (D : Data) (k : Nat) : Unit (centre D k) :=
  left_bounds _ 0 1 (fun x hx => D.bound x k hx) ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ k

theorem centres_close (D : Data) {k m : Nat} (hkm : k ≤ m) :
    qabs (centre D k-centre D m) ≤ radius D k := by
  have hp:=perturbation (fun x=>D.sample x k) (fun x=>D.sample x m)
    ((D.errorConstant:Rat)*(meshRadius k+meshRadius m)) (fun x hx=>D.evaluation_error x hx k m)
    (a:=0) (b:=1) ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ k
  have hm:=mesh_error (fun x=>D.sample x m) (D.decreasing m)
    (D.bound 1 m ⟨by decide,by decide⟩).1 (D.bound 0 m ⟨by decide,by decide⟩).2 hkm
  have ht:=qabs_add_le (left (fun x=>D.sample x k) 0 1 k-left (fun x=>D.sample x m) 0 1 k)
    (left (fun x=>D.sample x m) 0 1 k-left (fun x=>D.sample x m) 0 1 m)
  have he : (left (fun x=>D.sample x k) 0 1 k-left (fun x=>D.sample x m) 0 1 k)+
      (left (fun x=>D.sample x m) 0 1 k-left (fun x=>D.sample x m) 0 1 m)=centre D k-centre D m := by unfold centre; grind
  rw [he] at ht
  have hmono:=meshRadius_antitone hkm
  have hscale:=Rat.mul_le_mul_of_nonneg_left hmono (Rat.natCast_nonneg (a:=D.errorConstant))
  unfold radius; grind

theorem radius_shrinks (D : Data) : ShrinksToZero (radius D) := by
  apply shrinksToZero_of_natOverSuccBound (C:=1+2*D.errorConstant)
  intro n
  have hp : 0 ≤ 1+2*(D.errorConstant:Rat) := by have h:=Rat.natCast_nonneg (a:=D.errorConstant); grind
  have h:=Rat.mul_le_mul_of_nonneg_left (meshRadius_le n) hp
  simpa only [radius,Rat.natCast_add,Rat.natCast_mul,show ((1:Nat):Rat)=1 by decide,
    show ((2:Nat):Rat)=2 by decide,Rat.div_def,Rat.one_mul] using h

theorem candidate_future (D : Data) (k m : Nat) (hkm : k ≤ m) :
    (QInterval.expand ((candidate D).compute k) (radius D k)).ContainsInterval ((candidate D).compute m) := by
  have hc:=centres_close D hkm
  have hp:=self_le_qabs (centre D k-centre D m)
  have hn:=neg_qabs_le_self (centre D k-centre D m)
  change centre D k-radius D k ≤ centre D m ∧ centre D m ≤ centre D k+radius D k
  constructor <;> grind

def stabilized (D : Data) : RealRaw := RealRaw.prefixStabilize (candidate D) (radius D)

theorem stabilized_valid (D : Data) : (stabilized D).Valid := by
  apply RealRaw.prefixStabilize_valid_of_future (candidate:=candidate D) (radius:=radius D)
    (fun n=>by change 0 ≤ centre D n-centre D n; grind)
  · intro eps
    exact ⟨0,fun n _=>by change centre D n-centre D n ≤ eps.val; have h:=eps.property; grind⟩
  · exact candidate_future D
  · exact radius_shrinks D

/-- Fixed mesh depth k and evaluation stage k, with the proved uncertainty
radius. Prefix intersection and the known range make outputs nested. -/
def raw (D : Data) : RealRaw where
  compute := fun k => QInterval.intersection {lo:=0,hi:=1} ((stabilized D).compute k)

theorem contains_future (D : Data) (k m : Nat) (hkm : k ≤ m) :
    ((raw D).compute k).ContainsInterval ((candidate D).compute m) :=
  QInterval.intersection_contains (centre_unit D m)
    (RealRaw.prefixStabilize_contains_future (candidate_future D) k m hkm)

theorem range (D : Data) (k : Nat) : subintervalOf ((raw D).compute k) 0 1 := by
  have h:=contains_future D k k (Nat.le_refl k)
  have hc:=QInterval.intersection_contained_left ({lo:=0,hi:=1}:QInterval) ((stabilized D).compute k)
  exact ⟨hc.1,Rat.le_trans h.1 h.2,hc.2⟩

theorem valid (D : Data) : (raw D).Valid := by
  have H:=stabilized_valid D
  refine ⟨?_,?_,?_⟩
  · intro n
    have h:=(range D n).2.1
    change 0 ≤ ((raw D).compute n).hi-((raw D).compute n).lo
    grind
  · intro n m hnm
    have h:=H.2.1 n m hnm
    exact ⟨by change max 0 _ ≤ max 0 _; grind,(range D m).2.1,
      by change min 1 _ ≤ min 1 _; grind⟩
  · intro eps
    obtain ⟨N,hN⟩:=H.2.2 eps
    exact ⟨N,fun n hn=>Rat.le_trans (QInterval.width_le_of_contains
      (QInterval.intersection_contained_right ({lo:=0,hi:=1}:QInterval) ((stabilized D).compute n))) (hN n hn)⟩

theorem width (D : Data) (n : Nat) : ((raw D).compute n).width ≤ 2*radius D n := by
  have h1:=QInterval.width_le_of_contains
    (QInterval.intersection_contained_right ({lo:=0,hi:=1}:QInterval) ((stabilized D).compute n))
  have h2:=RealRaw.prefixStabilize_width_le_current_expand (candidate D) (radius D) n
  have hz : ((candidate D).compute n).width=0 := by change centre D n-centre D n=0; grind
  rw [hz] at h2
  change ((raw D).compute n).width ≤ _ at h1
  change ((stabilized D).compute n).width ≤ _ at h2
  grind

end ComputableAnalysis.MonotoneSampleIntegral
