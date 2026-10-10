import FiniteRationalBall

/-! Finite Archimedes shell estimates, uniform in dimension. These are
rational dissection coefficients; no curved-region volume or integral is
introduced. The geometric product/dissection bridge is a separate theorem. -/
namespace ComputableAnalysis.RationalBall

private theorem one_power (n : Nat) : (1:Rat)^n=1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Rat.pow_succ,ih,Rat.one_mul]


private theorem mesh_order' (d a : Rat) (rest : List Rat)
    (hm : meshBound d a rest) : ordered a rest := by
  induction rest generalizing a with
  | nil => trivial
  | cons b rest ih => exact ⟨hm.1,ih b hm.2.2⟩

private theorem ordered_last (a : Rat) (rest : List Rat) (ho : ordered a rest) :
    a ≤ lastPoint a rest := by
  induction rest generalizing a with
  | nil => exact Rat.le_refl
  | cons b rest ih =>
    have ht := ih b ho.2
    simp only [lastPoint]
    exact Rat.le_trans ho.1 ht

theorem shellGap_mesh (n : Nat) (d a : Rat) (rest : List Rat)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hm : meshBound d a rest)
    (hend : lastPoint a rest ≤ 1) :
    0 ≤ shellGap n (a::rest) ∧
      shellGap n (a::rest) ≤ 2*d*((lastPoint a rest)^n-a^n) := by
  induction rest generalizing a with
  | nil => simp only [shellGap,lastPoint]; constructor <;> grind
  | cons b rest ih =>
    have hb : 0 ≤ b := by grind [meshBound]
    have hb1 : b ≤ 1 := by
      have ht := ordered_last b rest (mesh_order' d b rest hm.2.2)
      change lastPoint b rest ≤ 1 at hend
      grind
    have ha1 : a ≤ 1 := by grind [meshBound]
    have hab : a ≤ b := hm.1
    have hstep : b-a ≤ d := hm.2.1
    have hp := power_mono ha hab n
    have hsq := power_mono ha hab 2
    have hdiff : 0 ≤ b^n-a^n := by grind
    have hsqdiff : 0 ≤ b*b-a*a := by
      have hsq' : a*a ≤ b*b := by simpa [Rat.pow_succ] using hsq
      grind
    have hbound : b*b-a*a ≤ 2*d := by
      have hs : 0 ≤ b-a := by grind
      have hsum : b+a ≤ 2 := by grind
      have hmul := Rat.mul_le_mul_of_nonneg_left hsum hs
      grind [Rat.mul_add,Rat.mul_comm]
    have hpos := Rat.mul_nonneg hsqdiff hdiff
    have hmul := Rat.mul_le_mul_of_nonneg_right hbound hdiff
    have ht := ih b hb hm.2.2 hend
    simp only [shellGap,lastPoint]
    constructor <;> grind [Rat.mul_add,Rat.mul_assoc]

theorem moment_power_error (n : Nat) (d a : Rat) (rest : List Rat)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hm : meshBound d a rest)
    (hend : lastPoint a rest ≤ 1) :
    0 ≤ moment n (a::rest)-2*leftPowerSum (n+1) a rest ∧
      moment n (a::rest)-2*leftPowerSum (n+1) a rest ≤
        d*(lastPoint a rest-a) := by
  induction rest generalizing a with
  | nil => simp only [moment,leftPowerSum,lastPoint]; constructor <;> grind
  | cons b rest ih =>
    have hab : a ≤ b := hm.1
    have hs : 0 ≤ b-a := by grind
    have hb : 0 ≤ b := by grind
    have hb1 : b ≤ 1 := by
      have ht := ordered_last b rest (mesh_order' d b rest hm.2.2)
      change lastPoint b rest ≤ 1 at hend
      grind
    have ha1 : a ≤ 1 := by grind
    have hpow := power_mono ha ha1 n
    have hone := one_power n
    rw [hone] at hpow
    have hpn : 0 ≤ a^n := Rat.pow_nonneg ha
    have hsquare : 0 ≤ (b-a)*(b-a) := Rat.mul_nonneg hs hs
    have hsqbound := Rat.mul_le_mul_of_nonneg_right hm.2.1 hs
    have hlocalpos := Rat.mul_nonneg hpn hsquare
    have hlocalbound := Rat.mul_le_mul_of_nonneg_right hpow hsquare
    have ht := ih b hb hm.2.2 hend
    simp only [moment,leftPowerSum,lastPoint,Rat.pow_succ]
    constructor <;> grind [Rat.mul_add,Rat.add_mul,
      Rat.mul_assoc,Rat.mul_comm]

theorem shells_recurrence_estimate (n : Nat) (hn : 0 < n) (d : Rat)
    (hd : 0 ≤ d) (rest : List Rat) (hm : meshBound d 0 rest)
    (hend : lastPoint 0 rest=1) :
    2/((n+2:Nat):Rat)-2*d ≤ shellLower n (0::rest) ∧
    shellLower n (0::rest) ≤ 2/((n+2:Nat):Rat)+d ∧
    shellLower n (0::rest) ≤ shellUpper n (0::rest) ∧
    shellUpper n (0::rest) ≤ 2/((n+2:Nat):Rat)+3*d := by
  have hp := unit_partition_power_estimate (n+1) (by omega) d rest hm hend
  have hmom := moment_power_error n d 0 rest hd (by decide) hm (by rw [hend]; decide)
  have hgap := shellGap_mesh n d 0 rest hd (by decide) hm (by rw [hend]; decide)
  have hz : (0:Rat)^n=0 := by cases n with
    | zero => omega
    | succ n => simp [Rat.pow_succ]
  have hone := one_power n
  rw [hend,hz,hone] at hgap
  rw [hend] at hmom
  rw [← shells_zero_one n hn rest hend] at hmom
  have hg := shells_gap n (0::rest)
  have htwo : 2/((n+2:Nat):Rat)=2*(1/((n+2:Nat):Rat)) := by
    grind [Rat.div_def]
  constructor
  · grind
  constructor
  · grind
  constructor <;> grind

/-- A uniform partition is constructed by extending the preceding endpoint. -/
def equalPartition (a h : Rat) : Nat → List Rat
  | 0 => []
  | m+1 => (a+h)::equalPartition (a+h) h m

theorem equalPartition_last (a h : Rat) (m : Nat) :
    lastPoint a (equalPartition a h m) = a+(m:Rat)*h := by
  induction m generalizing a with
  | zero => simp [equalPartition,lastPoint]; grind
  | succ m ih =>
    simp only [equalPartition,lastPoint]
    rw [ih]
    rw [Rat.natCast_add]
    change a+h+(m:Rat)*h=a+((m:Rat)+1)*h
    rw [Rat.add_mul,Rat.one_mul]
    rw [Rat.add_assoc,Rat.add_comm h ((m:Rat)*h),← Rat.add_assoc]

theorem equalPartition_mesh (a h : Rat) (m : Nat) (hh : 0 ≤ h) :
    meshBound h a (equalPartition a h m) := by
  induction m generalizing a with
  | zero => trivial
  | succ m ih =>
    refine ⟨?_,?_,ih (a+h)⟩ <;> grind

theorem unit_equalPartition_last (N : Nat) (hN : 0 < N) :
    lastPoint 0 (equalPartition 0 (1/(N:Rat)) N)=1 := by
  rw [equalPartition_last]
  have hNq : 0 < (N:Rat) := Rat.natCast_pos.mpr hN
  have hz : (N:Rat) ≠ 0 := by grind
  have hi := Rat.mul_inv_cancel (N:Rat) hz
  grind [Rat.div_def]

/-- An executable rational partition supplies the general-dimensional
Archimedes shell bounds with explicit error constants divided by N. -/
theorem uniform_shells_recurrence_estimate (n N : Nat) (hn : 0 < n) (hN : 0 < N) :
    let points := 0::equalPartition 0 (1/(N:Rat)) N
    2/((n+2:Nat):Rat)-2/(N:Rat) ≤ shellLower n points ∧
    shellLower n points ≤ 2/((n+2:Nat):Rat)+1/(N:Rat) ∧
    shellLower n points ≤ shellUpper n points ∧
    shellUpper n points ≤ 2/((n+2:Nat):Rat)+3/(N:Rat) := by
  have hNq : 0 < (N:Rat) := Rat.natCast_pos.mpr hN
  have hh : 0 ≤ 1/(N:Rat) := Rat.le_of_lt (by
    simpa [Rat.div_def] using (Rat.inv_pos.mpr hNq))
  have he := shells_recurrence_estimate n hn (1/(N:Rat)) hh
    (equalPartition 0 (1/(N:Rat)) N)
    (equalPartition_mesh 0 _ N hh) (unit_equalPartition_last N hN)
  dsimp
  grind [Rat.div_def]

theorem normSq_concat (xs ys : List Rat) :
    normSq (xs++ys)=normSq xs+normSq ys := by
  induction xs with
  | nil => simp [normSq,sum]; grind
  | cons x xs ih =>
    change x*x+normSq (xs++ys)=(x*x+normSq xs)+normSq ys
    rw [ih]
    grind

/-- The inner shell/disk bound is a rational coordinate containment, valid
in arbitrary finite dimension before assigning any volume to a surface. -/
theorem shell_disk_inner (xs ys : List Rat) (b : Rat)
    (hx : normSq xs ≤ b*b) (hy : normSq ys ≤ 1-b*b) :
    normSq (xs++ys) ≤ 1 := by
  rw [normSq_concat]
  grind

/-- The outer shell/disk bound follows from the same quadratic identity. -/
theorem shell_disk_outer (xs ys : List Rat) (a : Rat)
    (hx : a*a ≤ normSq xs) (hball : normSq (xs++ys) ≤ 1) :
    normSq ys ≤ 1-a*a := by
  rw [normSq_concat] at hball
  grind

#print axioms shellGap_mesh
#print axioms moment_power_error
#print axioms shells_recurrence_estimate
#print axioms equalPartition_last
#print axioms equalPartition_mesh
#print axioms uniform_shells_recurrence_estimate
#print axioms shell_disk_inner
#print axioms shell_disk_outer
end ComputableAnalysis.RationalBall
