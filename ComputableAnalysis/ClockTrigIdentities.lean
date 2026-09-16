import ComputableAnalysis.ClockTrigonometry
import ComputableAnalysis.TrigSpecialValues

/-! Addition, complementary angles, and half-angle squares for the closed
inverse-arctangent functions. Every angular argument here is in quarter turns.
The `sinPi`/`cosPi` adapters preserve the public half-turn convention. -/
namespace ComputableAnalysis
namespace ClockTrigonometry
open ClosedArctanInverse ArctanGeometry SinPiIntegral IntervalSelections

theorem sample_bounds (t : Rat) (n : Nat) :
    0 <= c t n ∧ c t n <= 1 ∧ 0 <= s t n ∧ s t n <= 1 := by
  have hu := center_unit t n
  have hc := rationalCircleCos_bounds hu.1 hu.2
  have hs := rationalCircleSin_bounds hu.1 hu.2
  exact ⟨hc.1,hc.2,hs.1,hs.2⟩

private theorem mul_error {a e b : Rat} (ha : 0 <= a) (ha1 : a <= 1) (he : qabs e <= b) :
    qabs (a*e) <= b := by
  rw [qabs_mul,qabs_eq_self_of_nonneg ha]
  have hm := Rat.mul_le_mul_of_nonneg_right ha1 (qabs_nonneg e)
  grind

private theorem solve_rotation {ca sa cb sb cc sc e : Rat}
    (hb : cb*cb+sb*sb=1) (hcb : 0 <= cb) (hcb1 : cb <= 1)
    (hsb : 0 <= sb) (hsb1 : sb <= 1)
    (he1 : qabs (ca-(cc*cb+sc*sb)) <= 152*e)
    (he2 : qabs (sa-(sc*cb-cc*sb)) <= 76*e) :
    qabs (cc-(ca*cb-sa*sb)) <= 228*e ∧
    qabs (sc-(sa*cb+ca*sb)) <= 228*e := by
  have hc1 := mul_error hcb hcb1 he1
  have hc2 := mul_error hsb hsb1 he2
  have hs1 := mul_error hsb hsb1 he1
  have hs2 := mul_error hcb hcb1 he2
  have ht1 := qabs_sub_le (sb*(sa-(sc*cb-cc*sb))) (cb*(ca-(cc*cb+sc*sb)))
  have ht2 := qabs_add_le (sb*(ca-(cc*cb+sc*sb))) (cb*(sa-(sc*cb-cc*sb)))
  have hi1 : cc-(ca*cb-sa*sb)=sb*(sa-(sc*cb-cc*sb))-cb*(ca-(cc*cb+sc*sb)) := by grind
  have hi2 : sc-(sa*cb+ca*sb)= -(sb*(ca-(cc*cb+sc*sb))+cb*(sa-(sc*cb-cc*sb))) := by grind
  rw [hi1,hi2,qabs_neg]
  constructor <;> grind

theorem sample_addition {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a+b <= 1) (n : Nat) :
    qabs (c (a+b) n-(c a n*c b n-s a n*s b n)) <= 228*meshRadius n ∧
    qabs (s (a+b) n-(s a n*c b n+c a n*s b n)) <= 228*meshRadius n := by
  have hsum : Unit (a+b) := ⟨Rat.add_nonneg ha.1 hb.1,hab⟩
  have hdiff := sample_difference hb hsum (by have h0:=ha.1; grind) n
  rw [show a+b-b=a by grind] at hdiff
  have hB:=sample_bounds b n
  exact solve_rotation (sample_unit b n) hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 hdiff.1 hdiff.2

theorem cosine_addition {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a+b <= 1) :
    (cosine (a+b)).Equiv
      (RealRaw.mul (cosine a) (cosine b)-RealRaw.mul (sine a) (sine b)) := by
  have hs : Unit (a+b) := ⟨Rat.add_nonneg ha.1 hb.1,hab⟩
  apply equiv_of_geometric_error (cosine_valid hs)
    (RealRaw.sub_valid (RealRaw.mul_valid (cosine_valid ha) (cosine_valid hb))
      (RealRaw.mul_valid (sine_valid ha) (sine_valid hb)))
    (c (a+b)) (fun n=>c a n*c b n-s a n*s b n) (c_mem hs)
    (fun n=>sub_mem (mul_mem (c_mem ha n) (c_mem hb n)) (mul_mem (s_mem ha n) (s_mem hb n))) 228
  exact fun n=>(sample_addition ha hb hab n).1

theorem sine_addition {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a+b <= 1) :
    (sine (a+b)).Equiv
      (RealRaw.mul (sine a) (cosine b)+RealRaw.mul (cosine a) (sine b)) := by
  have hs : Unit (a+b) := ⟨Rat.add_nonneg ha.1 hb.1,hab⟩
  apply equiv_of_geometric_error (sine_valid hs)
    (RealRaw.add_valid (RealRaw.mul_valid (sine_valid ha) (cosine_valid hb))
      (RealRaw.mul_valid (cosine_valid ha) (sine_valid hb)))
    (s (a+b)) (fun n=>s a n*c b n+c a n*s b n) (s_mem hs)
    (fun n=>add_mem (mul_mem (s_mem ha n) (c_mem hb n)) (mul_mem (c_mem ha n) (s_mem hb n))) 228
  exact fun n=>(sample_addition ha hb hab n).2

/-- Exact-clock endpoint candidates identify the inverse, with no preexisting
endpoint values for sine or cosine used in the proof. -/
theorem center_at_endpoint {t : Rat} (ht : t=0 ∨ t=1) (n : Nat) :
    qabs (center t n-t) <= 14*meshRadius n := by
  have htU : Unit t := by rcases ht with rfl|rfl <;> constructor <;> decide +kernel
  have he : (A t n).lo=t*(A 1 n).lo := by
    rcases ht with rfl|rfl
    · rw [arctanIntegralRectangleCompute_zero_lower,Rat.zero_mul]
    · rw [Rat.one_mul]
  have hc:=center_residual t htU n
  have hi:=clock_inverse_bound (center_unit t n) htU n n
  rw [he] at hi
  have w1:=clock_width (center t n) (center_unit t n) n
  have w2:=clock_width t htU n
  grind

theorem sample_endpoint {t : Rat} (ht : t=0 ∨ t=1) (n : Nat) :
    qabs (c t n-(1-t)) <= 56*meshRadius n ∧ qabs (s t n-t) <= 28*meshRadius n := by
  have htU : Unit t := by rcases ht with rfl|rfl <;> constructor <;> decide +kernel
  have hu:=center_unit t n
  have hi:=center_at_endpoint ht n
  have hC:=rationalCircleCos_difference_le_qabs hu.1 hu.2 htU.1 htU.2
  have hS:=rationalCircleSin_difference_le_qabs hu.1 hu.2 htU.1 htU.2
  have hc : rationalCircleCos t=1-t := by rcases ht with rfl|rfl <;> decide +kernel
  have hs : rationalCircleSin t=t := by rcases ht with rfl|rfl <;> decide +kernel
  rw [hc] at hC; rw [hs] at hS
  constructor <;> dsimp [c,s] <;> grind

theorem cosine_endpoint {t : Rat} (ht : t=0 ∨ t=1) : (cosine t).Equiv (RealRaw.ofRat (1-t)) := by
  have htU : Unit t := by rcases ht with rfl|rfl <;> constructor <;> decide +kernel
  apply equiv_of_geometric_error (cosine_valid htU) (RealRaw.ofRat_valid (1-t))
    (c t) (fun _=>1-t) (c_mem htU) (rat_mem (1-t)) 56
  exact fun n=>(sample_endpoint ht n).1

theorem sine_endpoint {t : Rat} (ht : t=0 ∨ t=1) : (sine t).Equiv (RealRaw.ofRat t) := by
  have htU : Unit t := by rcases ht with rfl|rfl <;> constructor <;> decide +kernel
  apply equiv_of_geometric_error (sine_valid htU) (RealRaw.ofRat_valid t)
    (s t) (fun _=>t) (s_mem htU) (rat_mem t) 28
  exact fun n=>(sample_endpoint ht n).2

theorem sample_complement {t : Rat} (ht : Unit t) (n : Nat) :
    qabs (c (1-t) n-s t n) <= 236*meshRadius n ∧
    qabs (s (1-t) n-c t n) <= 160*meshRadius n := by
  have hd:=sample_difference ht (b:=1) ⟨by decide,by decide⟩ ht.2 n
  have he:=sample_endpoint (t:=1) (Or.inr rfl) n
  rw [show (1 : Rat)-1=0 by decide +kernel] at he
  have hb:=sample_bounds t n
  have hC:=mul_error hb.1 hb.2.1 he.1
  have hS:=mul_error hb.2.2.1 hb.2.2.2 he.2
  have hC':=mul_error hb.2.2.1 hb.2.2.2 he.1
  have hS':=mul_error hb.1 hb.2.1 he.2
  have ht1:=qabs_add_le (c (1-t) n-(c 1 n*c t n+s 1 n*s t n))
    (c t n*(c 1 n-0)+s t n*(s 1 n-1))
  have ht2:=qabs_add_le (c t n*(c 1 n-0)) (s t n*(s 1 n-1))
  have ht3:=qabs_add_le (s (1-t) n-(s 1 n*c t n-c 1 n*s t n))
    (c t n*(s 1 n-1)-s t n*(c 1 n-0))
  have ht4:=qabs_sub_le (c t n*(s 1 n-1)) (s t n*(c 1 n-0))
  have hi1 : c (1-t) n-(c 1 n*c t n+s 1 n*s t n)+
      (c t n*(c 1 n-0)+s t n*(s 1 n-1)) = c (1-t) n-s t n := by grind
  have hi2 : s (1-t) n-(s 1 n*c t n-c 1 n*s t n)+
      (c t n*(s 1 n-1)-s t n*(c 1 n-0)) = s (1-t) n-c t n := by grind
  rw [hi1] at ht1; rw [hi2] at ht3
  constructor <;> grind

theorem cosine_complement {t : Rat} (ht : Unit t) : (cosine (1-t)).Equiv (sine t) := by
  have hc : Unit (1-t) := by have h0:=ht.1; have h1:=ht.2; constructor <;> grind
  exact equiv_of_geometric_error (cosine_valid hc) (sine_valid ht) (c (1-t)) (s t)
    (c_mem hc) (s_mem ht) 236 (fun n=>(sample_complement ht n).1)

theorem sine_complement {t : Rat} (ht : Unit t) : (sine (1-t)).Equiv (cosine t) := by
  have hc : Unit (1-t) := by have h0:=ht.1; have h1:=ht.2; constructor <;> grind
  exact equiv_of_geometric_error (sine_valid hc) (cosine_valid ht) (s (1-t)) (c t)
    (s_mem hc) (c_mem ht) 160 (fun n=>(sample_complement ht n).2)

theorem sample_half_squares {t : Rat} (ht : Unit t) (n : Nat) :
    qabs (c (t/2) n*c (t/2) n-(1+c t n)/2) <= 114*meshRadius n ∧
    qabs (s (t/2) n*s (t/2) n-(1-c t n)/2) <= 114*meshRadius n := by
  have hh : Unit (t/2) := by have h0:=ht.1; have h1:=ht.2; simp only [Rat.div_def]; constructor <;> grind
  have he : t/2+t/2=t := by simp only [Rat.div_def]; grind
  have ha:= (sample_addition hh hh (by rw [he]; exact ht.2) n).1
  rw [he] at ha
  have hn:=sample_unit (t/2) n
  have hneg:=neg_qabs_le_self (c t n-(c (t/2) n*c (t/2) n-s (t/2) n*s (t/2) n))
  have hpos:=self_le_qabs (c t n-(c (t/2) n*c (t/2) n-s (t/2) n*s (t/2) n))
  constructor <;> apply qabs_le_of_neg_le_le <;> simp only [Rat.div_def] <;> grind

theorem cosine_half_square {t : Rat} (ht : Unit t) :
    (RealRaw.mul (cosine (t/2)) (cosine (t/2))).Equiv
      (RealRaw.scaleRat (1/2) (RealRaw.one+cosine t)) := by
  have hh : Unit (t/2) := by have h0:=ht.1; have h1:=ht.2; simp only [Rat.div_def]; constructor <;> grind
  apply equiv_of_geometric_error
    (RealRaw.mul_valid (cosine_valid hh) (cosine_valid hh))
    (RealRaw.scaleRat_valid (RealRaw.add_valid (RealRaw.ofRat_valid 1) (cosine_valid ht)))
    (fun n=>c (t/2) n*c (t/2) n) (fun n=>(1+c t n)/2)
    (fun n=>mul_mem (c_mem hh n) (c_mem hh n)) ?_ 114
    (fun n=>(sample_half_squares ht n).1)
  intro n
  have hm:=scale_mem (add_mem (rat_mem 1 n) (c_mem ht n)) (r:=1/2) (by decide +kernel)
  have he : (1 : Rat)/2*(1+c t n)=(1+c t n)/2 := by simp only [Rat.div_def]; grind
  rw [he] at hm; exact hm

theorem sine_half_square {t : Rat} (ht : Unit t) :
    (RealRaw.mul (sine (t/2)) (sine (t/2))).Equiv
      (RealRaw.scaleRat (1/2) (RealRaw.one-cosine t)) := by
  have hh : Unit (t/2) := by have h0:=ht.1; have h1:=ht.2; simp only [Rat.div_def]; constructor <;> grind
  apply equiv_of_geometric_error
    (RealRaw.mul_valid (sine_valid hh) (sine_valid hh))
    (RealRaw.scaleRat_valid (RealRaw.sub_valid (RealRaw.ofRat_valid 1) (cosine_valid ht)))
    (fun n=>s (t/2) n*s (t/2) n) (fun n=>(1-c t n)/2)
    (fun n=>mul_mem (s_mem hh n) (s_mem hh n)) ?_ 114
    (fun n=>(sample_half_squares ht n).2)
  intro n
  have hm:=scale_mem (sub_mem (rat_mem 1 n) (c_mem ht n)) (r:=1/2) (by decide +kernel)
  have he : (1 : Rat)/2*(1-c t n)=(1-c t n)/2 := by simp only [Rat.div_def]; grind
  rw [he] at hm; exact hm

/-- Nonnegativity selects the positive half-angle square root. -/
theorem cosine_nonnegative {t : Rat} (ht : Unit t) (n : Nat) : 0 <= ((cosine t).compute n).lo := by
  have h := ClosedArctanInverse.raw_unit t ht n
  exact (rationalCircleCos_bounds (Rat.le_trans h.1 h.2.1) h.2.2).1

end ClockTrigonometry
end ComputableAnalysis
