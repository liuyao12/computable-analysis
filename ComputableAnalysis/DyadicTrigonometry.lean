import ComputableAnalysis.HalfAngleRadicals
import ComputableAnalysis.ClockTrigIdentities

/-!
# Dyadic angle values from nested square-root bisections

The numerical path starts at slope 1 and repeatedly applies
`u / (1 + sqrt(1+u*u))`, enclosing the square root by rational bisection.
Neither pi nor the arctangent clock is evaluated by this program. The clock
is used only to prove agreement with the closed inverse-arctangent functions.
Arguments in this module are fractions of a quarter turn.
-/
namespace ComputableAnalysis
namespace DyadicTrigonometry
open ClosedArctanInverse ArctanGeometry SinPiIntegral IntervalSelections

abbrev angle (d : Nat) : Rat := meshRadius d

theorem angle_unit (d : Nat) : Unit (angle d) := by
  have h := meshRadius_antitone (Nat.zero_le d)
  have hz : meshRadius 0=1 := by decide +kernel
  rw [hz] at h
  exact ⟨Rat.le_of_lt (meshRadius_pos d),h⟩

theorem path_clock_error (p d n : Nat) :
    qabs ((A (HalfAngleRadicals.path p d) n).lo-angle d*(A 1 n).lo) <=
      4*meshRadius p+2*meshRadius n := by
  have hh:=HalfAngleRadicals.path_clock p d n n
  have ha:=angle_unit d
  have hu:=HalfAngleRadicals.path_unit p d
  have w:=clock_width _ hu n
  have w1:=clock_width 1 (by constructor <;> decide) n
  have hp : 0 < (2 : Rat)^d := Rat.pow_pos (by decide)
  have hc : angle d*(2 : Rat)^d=1 := by
    simp only [angle,meshRadius,Rat.div_def,Rat.one_mul]
    exact Rat.inv_mul_cancel _ (Rat.ne_of_gt hp)
  have hL:=Rat.mul_le_mul_of_nonneg_left hh.1 ha.1
  have hU:=Rat.mul_le_mul_of_nonneg_left hh.2 ha.1
  have hLW:=Rat.mul_le_mul_of_nonneg_left w1 ha.1
  have hLW2:=Rat.mul_le_mul_of_nonneg_right ha.2 (Rat.le_of_lt (meshRadius_pos n))
  have hr0:=Rat.le_of_lt (meshRadius_pos p)
  have hbounded : 0 <= angle d*(4*meshRadius p) := Rat.mul_nonneg ha.1 (Rat.mul_nonneg (by decide) hr0)
  have hc1 : angle d*((2 : Rat)^d*(A (HalfAngleRadicals.path p d) n).lo) =
      (A (HalfAngleRadicals.path p d) n).lo := by grind [Rat.mul_assoc]
  have hc2 : angle d*((2 : Rat)^d*(A (HalfAngleRadicals.path p d) n).hi) =
      (A (HalfAngleRadicals.path p d) n).hi := by grind [Rat.mul_assoc]
  have hc3 : angle d*((2 : Rat)^d-1)*(4*meshRadius p) =
      4*meshRadius p-angle d*(4*meshRadius p) := by grind
  rw [hc1] at hL
  rw [Rat.mul_add,hc2] at hU
  have htail : angle d*(((2 : Rat)^d-1)*(4*meshRadius p)) <= 4*meshRadius p := by grind [Rat.mul_assoc]
  unfold QInterval.width at w w1 hLW
  apply qabs_le_of_neg_le_le <;> grind

theorem path_center_close (p d n : Nat) :
    qabs (HalfAngleRadicals.path p d-center (angle d) n) <=
      8*meshRadius p+18*meshRadius n := by
  have h1:=path_clock_error p d n
  have h2:=center_residual (angle d) (angle_unit d) n
  have htri:=qabs_sub_le ((A (HalfAngleRadicals.path p d) n).lo-angle d*(A 1 n).lo)
    ((A (center (angle d) n) n).lo-angle d*(A 1 n).lo)
  have he : ((A (HalfAngleRadicals.path p d) n).lo-angle d*(A 1 n).lo)-
      ((A (center (angle d) n) n).lo-angle d*(A 1 n).lo) =
      (A (HalfAngleRadicals.path p d) n).lo-(A (center (angle d) n) n).lo := by grind
  rw [he] at htri
  have hi:=clock_inverse_bound (HalfAngleRadicals.path_unit p d) (center_unit (angle d) n) n n
  have w1:=clock_width _ (HalfAngleRadicals.path_unit p d) n
  have w2:=clock_width _ (center_unit (angle d) n) n
  grind

theorem paths_close (d p q : Nat) :
    qabs (HalfAngleRadicals.path p d-HalfAngleRadicals.path q d) <=
      40*(meshRadius p+meshRadius q) := by
  have h1:=path_center_close p d p
  have h2:=path_center_close q d q
  have hc:=centers_close (angle d) (angle_unit d) p q
  have ht:=qabs_add_le (HalfAngleRadicals.path p d-center (angle d) p)
    (center (angle d) p-center (angle d) q)
  have ht2:=qabs_sub_le ((HalfAngleRadicals.path p d-center (angle d) p)+
    (center (angle d) p-center (angle d) q)) (HalfAngleRadicals.path q d-center (angle d) q)
  have he : (HalfAngleRadicals.path p d-center (angle d) p)+
      (center (angle d) p-center (angle d) q)-(HalfAngleRadicals.path q d-center (angle d) q) =
      HalfAngleRadicals.path p d-HalfAngleRadicals.path q d := by grind
  rw [he] at ht2
  grind

def candidate (d : Nat) : RealRaw where
  compute := fun n=>{lo:=HalfAngleRadicals.path n d,hi:=HalfAngleRadicals.path n d}
def radius (n : Nat) : Rat := 80*meshRadius n

theorem radius_shrinks : ShrinksToZero radius := by
  apply shrinksToZero_of_natOverSuccBound (C:=80)
  intro n
  have h:=Rat.mul_le_mul_of_nonneg_left (meshRadius_le n) (by decide : (0 : Rat) <=80)
  simpa only [radius,Rat.div_def,Rat.one_mul,show ((80 : Nat) : Rat)=80 by decide +kernel] using h

theorem candidate_future (d n m : Nat) (hnm : n <=m) :
    (QInterval.expand ((candidate d).compute n) (radius n)).ContainsInterval ((candidate d).compute m) := by
  have hh:=paths_close d n m
  have hm:=meshRadius_antitone hnm
  have hu:=self_le_qabs (HalfAngleRadicals.path n d-HalfAngleRadicals.path m d)
  have hl:=neg_qabs_le_self (HalfAngleRadicals.path n d-HalfAngleRadicals.path m d)
  change HalfAngleRadicals.path n d-radius n <= HalfAngleRadicals.path m d ∧
    HalfAngleRadicals.path m d <= HalfAngleRadicals.path n d+radius n
  unfold radius
  constructor <;> grind

def stabilized (d : Nat) : RealRaw := RealRaw.prefixStabilize (candidate d) radius

theorem stabilized_valid (d : Nat) : (stabilized d).Valid := by
  apply RealRaw.prefixStabilize_valid_of_future
    (candidate:=candidate d) (radius:=radius)
    (fun n=>by change 0 <= HalfAngleRadicals.path n d-HalfAngleRadicals.path n d; grind)
  · intro eps
    exact ⟨0,fun n _=>by change HalfAngleRadicals.path n d-HalfAngleRadicals.path n d <=eps.val; have h:=eps.property; grind⟩
  · exact candidate_future d
  · exact radius_shrinks

def parameter (d : Nat) : RealRaw where
  compute := fun n=>QInterval.intersection {lo:=0,hi:=1} ((stabilized d).compute n)

theorem parameter_contains (d n m : Nat) (hnm : n <=m) :
    ((parameter d).compute n).ContainsInterval ((candidate d).compute m) :=
  QInterval.intersection_contains (HalfAngleRadicals.path_unit m d)
    (RealRaw.prefixStabilize_contains_future (candidate_future d) n m hnm)

theorem parameter_unit (d n : Nat) : subintervalOf ((parameter d).compute n) 0 1 := by
  have h:=parameter_contains d n n (Nat.le_refl _)
  have hc:=QInterval.intersection_contained_left ({lo:=0,hi:=1} : QInterval) ((stabilized d).compute n)
  exact ⟨hc.1,Rat.le_trans h.1 h.2,hc.2⟩

theorem parameter_valid (d : Nat) : (parameter d).Valid := by
  have H:=stabilized_valid d
  refine ⟨?_,?_,?_⟩
  · intro n
    have h:=(parameter_unit d n).2.1
    change 0 <= ((parameter d).compute n).hi-((parameter d).compute n).lo
    grind
  · intro n m hnm
    have h:=H.2.1 n m hnm
    refine ⟨?_,(parameter_unit d m).2.1,?_⟩
    · change max 0 _ <= max 0 _; grind
    · change min 1 _ <= min 1 _; grind
  · intro eps
    obtain ⟨N,hN⟩:=H.2.2 eps
    exact ⟨N,fun n hn=>Rat.le_trans (QInterval.width_le_of_contains
      (QInterval.intersection_contained_right ({lo:=0,hi:=1} : QInterval) ((stabilized d).compute n))) (hN n hn)⟩

theorem parameter_equiv (d : Nat) : (parameter d).Equiv (ClosedArctanInverse.raw (angle d)) := by
  apply ClockTrigonometry.equiv_of_geometric_error (parameter_valid d)
    (ClosedArctanInverse.raw_valid _ (angle_unit d)) (fun n=>HalfAngleRadicals.path n d) (center (angle d))
    (fun n=>parameter_contains d n n (Nat.le_refl n))
    (fun n=>ClosedArctanInverse.raw_contains_centers _ (angle_unit d) n n (Nat.le_refl n)) 26
  intro n
  have h:=path_center_close n d n
  change qabs _ <=26*meshRadius n
  grind

private theorem cosine_mono {a b : Rat} (ha : 0 <=a) (hab : a <=b) (hb : b <=1) :
    rationalCircleCos b <=rationalCircleCos a := by
  have h:=(rationalCircleCosInterval_width_le (U:={lo:=a,hi:=b}) ⟨ha,hab,hb⟩).1
  change 0 <=rationalCircleCos a-rationalCircleCos b at h
  grind

theorem cosine_map_valid (X : RealRaw) (hX : X.Valid)
    (hU : ∀ n, subintervalOf (X.compute n) 0 1) :
    RealRaw.ValidCompute (fun n=>rationalCircleCosInterval (X.compute n)) := by
  refine ⟨?_,?_,?_⟩
  · intro n
    exact (rationalCircleCosInterval_width_le (hU n)).1
  · intro n m hnm
    have hn:=hX.2.1 n m hnm
    have hu:=hU n; have hv:=hU m
    exact ⟨cosine_mono (Rat.le_trans hv.1 hv.2.1) hn.2.2 hu.2.2,
      cosine_mono hv.1 hv.2.1 hv.2.2,cosine_mono hu.1 hn.1 (Rat.le_trans hv.2.1 hv.2.2)⟩
  · intro eps
    let eta : QPos:=⟨eps.val/4,by rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
    obtain ⟨N,hN⟩:=hX.2.2 eta
    refine ⟨N,fun n hn=>?_⟩
    have hw:=hN n hn
    have hc:=(rationalCircleCosInterval_width_le (hU n)).2
    dsimp [eta] at hw
    simp only [Rat.div_def] at hw
    grind

def cosine (d : Nat) : RealRaw where
  compute := fun n=>rationalCircleCosInterval ((parameter d).compute n)
def sine (d : Nat) : RealRaw where
  compute := fun n=>rationalCircleSinInterval ((parameter d).compute n)

theorem cosine_valid (d : Nat) : (cosine d).Valid :=
  cosine_map_valid _ (parameter_valid d) (parameter_unit d)
theorem sine_valid (d : Nat) : (sine d).Valid :=
  rationalCircleSinInterval_valid (parameter d).compute (parameter_valid d)
    (fun n=>⟨(parameter_unit d n).1,(parameter_unit d n).2.2⟩)

theorem cosine_sample_mem (d n : Nat) :
    InBox (rationalCircleCos (HalfAngleRadicals.path n d)) ((cosine d).compute n) := by
  have hp:=parameter_contains d n n (Nat.le_refl n)
  have hu:=parameter_unit d n
  have hx:=HalfAngleRadicals.path_unit n d
  exact ⟨cosine_mono hx.1 hp.2 hu.2.2,cosine_mono hu.1 hp.1 hx.2⟩

theorem sine_sample_mem (d n : Nat) :
    InBox (rationalCircleSin (HalfAngleRadicals.path n d)) ((sine d).compute n) := by
  have hp:=parameter_contains d n n (Nat.le_refl n)
  have hu:=parameter_unit d n
  have hx:=HalfAngleRadicals.path_unit n d
  exact ⟨rationalCircleSin_mono_public hu.1 hp.1 hx.2,
    rationalCircleSin_mono_public hx.1 hp.2 hu.2.2⟩

/-- A closed nested-radical cosine at every repeatedly halved quarter turn. -/
theorem cosine_equiv (d : Nat) : (cosine d).Equiv (ClockTrigonometry.cosine (angle d)) := by
  apply ClockTrigonometry.equiv_of_geometric_error (cosine_valid d)
    (ClockTrigonometry.cosine_valid (angle_unit d))
    (fun n=>rationalCircleCos (HalfAngleRadicals.path n d)) (ClockTrigonometry.c (angle d))
    (cosine_sample_mem d) (ClockTrigonometry.c_mem (angle_unit d)) 104
  intro n
  have h:=path_center_close n d n
  have hu:=HalfAngleRadicals.path_unit n d; have hv:=center_unit (angle d) n
  have hc:=rationalCircleCos_difference_le_qabs hu.1 hu.2 hv.1 hv.2
  change qabs (rationalCircleCos (HalfAngleRadicals.path n d)-rationalCircleCos (center (angle d) n)) <=104*meshRadius n
  grind

theorem sine_equiv (d : Nat) : (sine d).Equiv (ClockTrigonometry.sine (angle d)) := by
  apply ClockTrigonometry.equiv_of_geometric_error (sine_valid d)
    (ClockTrigonometry.sine_valid (angle_unit d))
    (fun n=>rationalCircleSin (HalfAngleRadicals.path n d)) (ClockTrigonometry.s (angle d))
    (sine_sample_mem d) (ClockTrigonometry.s_mem (angle_unit d)) 52
  intro n
  have h:=path_center_close n d n
  have hu:=HalfAngleRadicals.path_unit n d; have hv:=center_unit (angle d) n
  have hc:=rationalCircleSin_difference_le_qabs hu.1 hu.2 hv.1 hv.2
  change qabs (rationalCircleSin (HalfAngleRadicals.path n d)-rationalCircleSin (center (angle d) n)) <=52*meshRadius n
  grind

end DyadicTrigonometry
end ComputableAnalysis
