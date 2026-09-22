import ComputableAnalysis.TaggedQuadrature

/-!
# Meaning of a particular quadrature computation

Validity of a number alone says nothing about its integrand. This certificate
also relates independently valid input/output computations to all tagged sums
on every fixed dyadic mesh. Spatial error shrinks with the mesh; evaluation
precision is refined only after fixing that finite mesh and its tags.

This is an additive, quantitative certificate for a supplied computation,
not a universal existence assertion. Legacy integral wrappers are unchanged.
-/
namespace ComputableAnalysis.Quadrature
open ClosedArctanInverse RationalSampleLimits TaggedQuadrature

structure Certificate (f : Rat → RealRaw) (a b : Rat) (value : RealRaw) where
  ordered : a ≤ b
  function_valid : ∀ x, a ≤ x → x ≤ b → (f x).Valid
  value_valid : value.Valid
  sample : Rat → Nat → Rat
  sample_mem : ∀ x q, a ≤ x → x ≤ b →
    IntervalSelections.InBox (sample x q) ((f x).compute q)
  output : Nat → Rat
  output_mem : ∀ q, IntervalSelections.InBox (output q) (value.compute q)
  error : Rat
  error_nonneg : 0 ≤ error
  estimate : ∀ (d : Nat) (tag : Tag) (eps : QPos), ∃ N, ∀ q, N ≤ q →
    qabs (output q-(b-a)*average (fun x => sample x q) tag a b d) ≤
      error*meshRadius d+eps.val

/-- Different evaluators, sample choices and schedules give the same answer
when they satisfy the certificate for equivalent integrands. The proof only
synchronizes finitely many evaluations on one fixed mesh at a time. -/
theorem Certificate.equiv_of_pointwise {f g : Rat → RealRaw} {a b : Rat}
    {I J : RealRaw} (hI : Certificate f a b I) (hJ : Certificate g a b J)
    (hfg : ∀ x, a ≤ x → x ≤ b → (f x).Equiv (g x)) : I.Equiv J := by
  apply equiv_of_close hI.value_valid hJ.value_valid hI.output hJ.output hI.output_mem hJ.output_mem
  intro eps
  let eta : QPos := ⟨eps.val/4,by
    rw [Rat.div_def];exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  have hK : 0 ≤ hI.error+hJ.error := Rat.add_nonneg hI.error_nonneg hJ.error_nonneg
  have hs : Small (fun d => (hI.error+hJ.error)*meshRadius d) :=
    small_of_geometric_bound _ hK (fun d => by
      rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg hK (Rat.le_of_lt (meshRadius_pos d)))]
      exact Rat.le_refl)
  obtain ⟨d,hd⟩ := hs eta
  obtain ⟨NI,hNI⟩ := hI.estimate d leftTag eta
  obtain ⟨NJ,hNJ⟩ := hJ.estimate d leftTag eta
  have hsample : ∀ x, a ≤ x → x ≤ b → Close (hI.sample x) (hJ.sample x) := by
    intro x hax hxb
    exact close_of_equiv (hI.function_valid x hax hxb) (hJ.function_valid x hax hxb)
      _ _ (fun q => hI.sample_mem x q hax hxb) (fun q => hJ.sample_mem x q hax hxb)
      (hfg x hax hxb)
  have hc := close_scale (b-a) (average_close hI.sample hJ.sample leftTag hI.ordered hsample d)
  obtain ⟨NS,hNS⟩ := hc eta
  refine ⟨max NI (max NJ NS),fun q hq => ?_⟩
  have hi := hNI q (by omega)
  have hj := hNJ q (by omega)
  have ht := hNS q (by omega)
  have he := Rat.le_trans (self_le_qabs ((hI.error+hJ.error)*meshRadius d)) (hd d (Nat.le_refl d))
  let si := (b-a)*average (fun x => hI.sample x q) leftTag a b d
  let sj := (b-a)*average (fun x => hJ.sample x q) leftTag a b d
  have h1 := qabs_add_le (hI.output q-si) (si-sj)
  have h2 := qabs_sub_le ((hI.output q-si)+(si-sj)) (hJ.output q-sj)
  have hid : (hI.output q-si)+(si-sj)-(hJ.output q-sj)=hI.output q-hJ.output q := by grind only
  rw [hid] at h2
  change qabs (hI.output q-si) ≤ _ at hi
  change qabs (hJ.output q-sj) ≤ _ at hj
  change qabs (si-sj) ≤ _ at ht
  dsimp [eta] at hi hj ht he
  simp only [Rat.div_def] at hi hj ht he
  grind only

theorem Certificate.equiv {f : Rat → RealRaw} {a b : Rat} {I J : RealRaw}
    (hI : Certificate f a b I) (hJ : Certificate f a b J) : I.Equiv J :=
  hI.equiv_of_pointwise hJ (fun x hax hxb => RealRaw.equiv_refl _ (hI.function_valid x hax hxb))

/-- Replace an integrand by an equivalent computation. Only a fixed finite
set of input evaluations is synchronized, so no uniform pointwise convergence
rate is silently assumed. -/
def Certificate.congr_function {f g : Rat → RealRaw} {a b : Rat} {I : RealRaw}
    (A : Certificate f a b I)
    (hg : ∀ x, a ≤ x → x ≤ b → (g x).Valid)
    (hfg : ∀ x, a ≤ x → x ≤ b → (f x).Equiv (g x)) : Certificate g a b I where
  ordered := A.ordered
  function_valid := hg
  value_valid := A.value_valid
  sample := fun x q => ((g x).compute q).lo
  sample_mem := by
    intro x q hx hy
    have h := (hg x hx hy).1 q
    exact ⟨Rat.le_refl,by unfold QInterval.width at h;grind only⟩
  output := A.output
  output_mem := A.output_mem
  error := A.error
  error_nonneg := A.error_nonneg
  estimate := by
    intro d tag eps
    let eta : QPos := ⟨eps.val/2,by
      rw [Rat.div_def];exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
    obtain ⟨NA,hNA⟩ := A.estimate d tag eta
    have hc := close_scale (b-a) (average_close A.sample (fun x q => ((g x).compute q).lo)
      tag A.ordered (by
        intro x hx hy
        exact close_of_equiv (A.function_valid x hx hy) (hg x hx hy) _ _
          (fun q => A.sample_mem x q hx hy)
          (fun q => ⟨Rat.le_refl,by
            have h := (hg x hx hy).1 q;unfold QInterval.width at h;grind only⟩)
          (hfg x hx hy)) d)
    obtain ⟨NG,hNG⟩ := hc eta
    refine ⟨max NA NG,fun q hq => ?_⟩
    have ha := hNA q (by omega)
    have hg := hNG q (by omega)
    have ht := qabs_add_le
      (A.output q-(b-a)*average (fun x => A.sample x q) tag a b d)
      ((b-a)*average (fun x => A.sample x q) tag a b d-
        (b-a)*average (fun x => ((g x).compute q).lo) tag a b d)
    have he : (A.output q-(b-a)*average (fun x => A.sample x q) tag a b d)+
      ((b-a)*average (fun x => A.sample x q) tag a b d-
        (b-a)*average (fun x => ((g x).compute q).lo) tag a b d)=
      A.output q-(b-a)*average (fun x => ((g x).compute q).lo) tag a b d := by grind only
    rw [he] at ht
    dsimp [eta] at ha hg
    simp only [Rat.div_def] at ha hg
    grind only

/-- A useful evaluation principle: a fixed tagged rule is exactly v at every
mesh. The certificate then identifies the independently supplied value with v.
It also allows a pointwise-equivalent rational sample implementation. -/
theorem Certificate.value_of_exact_rule {f : Rat → RealRaw} {a b : Rat} {I : RealRaw}
    (hI : Certificate f a b I) (r : Rat → Rat)
    (he : ∀ x, a ≤ x → x ≤ b → (f x).Equiv (RealRaw.ofRat (r x)))
    (tag : Tag) (v : Rat)
    (hv : ∀ d, (b-a)*average r tag a b d=v) : I.Equiv (RealRaw.ofRat v) := by
  apply equiv_of_close hI.value_valid (RealRaw.ofRat_valid _) hI.output (fun _ => v)
    hI.output_mem (fun _ => ⟨Rat.le_refl,Rat.le_refl⟩)
  intro eps
  let eta : QPos := ⟨eps.val/3,by
    rw [Rat.div_def];exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  have hs : Small (fun d => hI.error*meshRadius d) :=
    small_of_geometric_bound _ hI.error_nonneg (fun d => by
      rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg hI.error_nonneg (Rat.le_of_lt (meshRadius_pos d)))]
      exact Rat.le_refl)
  obtain ⟨d,hd⟩ := hs eta
  obtain ⟨NI,hNI⟩ := hI.estimate d tag eta
  have hc := close_scale (b-a) (average_close hI.sample (fun x _ => r x) tag hI.ordered
    (fun x hax hxb => close_of_equiv (hI.function_valid x hax hxb) (RealRaw.ofRat_valid _)
      _ _ (fun q => hI.sample_mem x q hax hxb) (fun _ => ⟨Rat.le_refl,Rat.le_refl⟩)
      (he x hax hxb)) d)
  obtain ⟨NS,hNS⟩ := hc eta
  refine ⟨max NI NS,fun q hq => ?_⟩
  have hi := hNI q (by omega)
  have ht := hNS q (by omega)
  change qabs ((b-a)*average (fun x => hI.sample x q) tag a b d-(b-a)*average r tag a b d) ≤ eta.val at ht
  rw [hv d] at ht
  have hs := Rat.le_trans (self_le_qabs (hI.error*meshRadius d)) (hd d (Nat.le_refl d))
  have hx := qabs_add_le (hI.output q-(b-a)*average (fun x => hI.sample x q) tag a b d)
    ((b-a)*average (fun x => hI.sample x q) tag a b d-v)
  have hid : (hI.output q-(b-a)*average (fun x => hI.sample x q) tag a b d)+
      ((b-a)*average (fun x => hI.sample x q) tag a b d-v)=hI.output q-v := by grind only
  rw [hid] at hx
  dsimp [eta] at hi ht hs
  simp only [Rat.div_def] at hi ht hs
  grind only

/-- No accumulated length means zero quadrature, for any certified computed
integrand. No value or continuity property of that integrand is needed. -/
theorem Certificate.zero_interval {f : Rat → RealRaw} {a : Rat} {I : RealRaw}
    (A : Certificate f a a I) : I.Equiv (RealRaw.ofRat 0) := by
  apply equiv_of_close A.value_valid (RealRaw.ofRat_valid _)
    A.output (fun _ => 0) A.output_mem (fun _ => ⟨Rat.le_refl,Rat.le_refl⟩)
  intro eps
  let eta : QPos := ⟨eps.val/2,by
    rw [Rat.div_def];exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  have hs : Small (fun d => A.error*meshRadius d) :=
    small_of_geometric_bound _ A.error_nonneg (fun d => by
      rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg A.error_nonneg (Rat.le_of_lt (meshRadius_pos d)))]
      exact Rat.le_refl)
  obtain ⟨d,hd⟩ := hs eta
  obtain ⟨N,hN⟩ := A.estimate d leftTag eta
  refine ⟨N,fun q hq => ?_⟩
  have h1 := hN q hq
  have h2 := Rat.le_trans (self_le_qabs (A.error*meshRadius d)) (hd d (Nat.le_refl d))
  rw [Rat.sub_self,Rat.zero_mul] at h1
  dsimp [eta] at h1 h2
  simp only [Rat.div_def] at h1 h2
  grind only

/-- Linearity transports validity, samples and spatial error together. -/
def Certificate.add {f g : Rat → RealRaw} {a b : Rat} {I J : RealRaw}
    (A : Certificate f a b I) (B : Certificate g a b J) :
    Certificate (fun x => RealRaw.add (f x) (g x)) a b (RealRaw.add I J) where
  ordered := A.ordered
  function_valid := fun x hx hy => RealRaw.add_valid (A.function_valid x hx hy) (B.function_valid x hx hy)
  value_valid := RealRaw.add_valid A.value_valid B.value_valid
  sample := fun x q => A.sample x q+B.sample x q
  sample_mem := by
    intro x q hx hy
    have ha := A.sample_mem x q hx hy
    have hb := B.sample_mem x q hx hy
    change ((f x).compute q).lo+((g x).compute q).lo ≤ A.sample x q+B.sample x q ∧
      A.sample x q+B.sample x q ≤ ((f x).compute q).hi+((g x).compute q).hi
    unfold IntervalSelections.InBox at ha hb
    constructor <;> grind only
  output := fun q => A.output q+B.output q
  output_mem := by
    intro q
    have ha := A.output_mem q
    have hb := B.output_mem q
    change (I.compute q).lo+(J.compute q).lo ≤ A.output q+B.output q ∧
      A.output q+B.output q ≤ (I.compute q).hi+(J.compute q).hi
    unfold IntervalSelections.InBox at ha hb
    constructor <;> grind only
  error := A.error+B.error
  error_nonneg := Rat.add_nonneg A.error_nonneg B.error_nonneg
  estimate := by
    intro d tag eps
    let eta : QPos := ⟨eps.val/2,by
      rw [Rat.div_def];exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
    obtain ⟨NA,hNA⟩ := A.estimate d tag eta
    obtain ⟨NB,hNB⟩ := B.estimate d tag eta
    refine ⟨max NA NB,fun q hq => ?_⟩
    have ha := hNA q (by omega)
    have hb := hNB q (by omega)
    rw [average_add]
    have ht := qabs_add_le
      (A.output q-(b-a)*average (fun x => A.sample x q) tag a b d)
      (B.output q-(b-a)*average (fun x => B.sample x q) tag a b d)
    have hid : (A.output q-(b-a)*average (fun x => A.sample x q) tag a b d)+
      (B.output q-(b-a)*average (fun x => B.sample x q) tag a b d) =
      A.output q+B.output q-(b-a)*(average (fun x => A.sample x q) tag a b d+
        average (fun x => B.sample x q) tag a b d) := by grind only
    rw [hid] at ht
    dsimp [eta] at ha hb
    simp only [Rat.div_def] at ha hb
    grind only

private theorem scale_sample_mem {I : RealRaw} {x c : Rat} {q : Nat}
    (hx : IntervalSelections.InBox x (I.compute q)) :
    IntervalSelections.InBox (c*x) ((RealRaw.scaleRat c I).compute q) := by
  change IntervalSelections.InBox (c*x) (if 0≤c then
    {lo:=c*(I.compute q).lo,hi:=c*(I.compute q).hi} else
    {lo:=c*(I.compute q).hi,hi:=c*(I.compute q).lo})
  by_cases hc : 0≤c
  · rw [if_pos hc]
    exact ⟨Rat.mul_le_mul_of_nonneg_left hx.1 hc,Rat.mul_le_mul_of_nonneg_left hx.2 hc⟩
  · rw [if_neg hc]
    exact ⟨rat_mul_le_mul_of_nonpos_left hx.2 (by grind),
      rat_mul_le_mul_of_nonpos_left hx.1 (by grind)⟩

/-- Signed scaling includes negation and zero without requiring a positive
integrand or a newly implemented quadrature. -/
def Certificate.scale {f : Rat → RealRaw} {a b : Rat} {I : RealRaw}
    (A : Certificate f a b I) (c : Rat) :
    Certificate (fun x => RealRaw.scaleRat c (f x)) a b (RealRaw.scaleRat c I) where
  ordered := A.ordered
  function_valid := fun x hx hy => RealRaw.scaleRat_valid (A.function_valid x hx hy)
  value_valid := RealRaw.scaleRat_valid A.value_valid
  sample := fun x q => c*A.sample x q
  sample_mem := fun x q hx hy => scale_sample_mem (A.sample_mem x q hx hy)
  output := fun q => c*A.output q
  output_mem := fun q => scale_sample_mem (A.output_mem q)
  error := qabs c*A.error
  error_nonneg := Rat.mul_nonneg (qabs_nonneg c) A.error_nonneg
  estimate := by
    intro d tag eps
    have habs := qabs_nonneg c
    have hpos : 0<qabs c+1 := by grind only
    let eta : QPos := ⟨eps.val/(qabs c+1),by
      rw [Rat.div_def];exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hpos)⟩
    obtain ⟨N,hN⟩ := A.estimate d tag eta
    refine ⟨N,fun q hq => ?_⟩
    have ha := Rat.mul_le_mul_of_nonneg_left (hN q hq) habs
    have hc := Rat.mul_inv_cancel (qabs c+1) (Rat.ne_of_gt hpos)
    have hp := Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt ((Rat.inv_pos).2 hpos))
    have he : qabs c*eta.val ≤ eps.val := by
      calc
        qabs c*eta.val ≤ (qabs c+1)*eta.val :=
          Rat.mul_le_mul_of_nonneg_right (by grind only) (Rat.le_of_lt eta.property)
        _ = eps.val := by
          dsimp [eta]
          rw [Rat.div_def]
          calc
            _ = eps.val*((qabs c+1)*(qabs c+1)⁻¹) := by grind only
            _ = eps.val := by rw [hc,Rat.mul_one]
    rw [average_scale]
    rw [show c*A.output q-(b-a)*(c*average (fun x => A.sample x q) tag a b d)=
      c*(A.output q-(b-a)*average (fun x => A.sample x q) tag a b d) by grind only,qabs_mul]
    grind only

/-- Constant functions have a direct certificate with zero spatial error. -/
def constant (c a b : Rat) (hab : a ≤ b) :
    Certificate (fun _ => RealRaw.ofRat c) a b (RealRaw.ofRat ((b-a)*c)) where
  ordered := hab
  function_valid := fun _ _ _ => RealRaw.ofRat_valid _
  value_valid := RealRaw.ofRat_valid _
  sample := fun _ _ => c
  sample_mem := fun _ _ _ _ => ⟨Rat.le_refl,Rat.le_refl⟩
  output := fun _ => (b-a)*c
  output_mem := fun _ => ⟨Rat.le_refl,Rat.le_refl⟩
  error := 0
  error_nonneg := by decide
  estimate := by
    intro d tag eps
    refine ⟨0,fun q _ => ?_⟩
    rw [average_const,Rat.sub_self,Rat.zero_mul,Rat.zero_add]
    simpa only [show qabs (0:Rat)=0 by decide] using Rat.le_of_lt eps.property

/-- Total computational view of a supplied interval function. The rational
interval test is decidable; the outside-zero branch has no mathematical role
in certificates on the declared interval. -/
def intervalRaw (F : FunctionOnInterval) (x : Rat) : RealRaw :=
  if hx : F.lower ≤ x ∧ x ≤ F.upper then
    {compute := F.compute x hx}
  else RealRaw.ofRat 0

theorem intervalRaw_valid (F : FunctionOnInterval) (x : Rat) : (intervalRaw F x).Valid := by
  unfold intervalRaw
  split
  · rename_i hx
    exact F.valid_on x (F.defined_on x hx)
  · exact RealRaw.ofRat_valid 0

/-- Safe domain-aware packaging. Unlike the legacy `Integral.ConstructionFor`,
this record preserves the numerical relation to the integrand. -/
structure ConstructionFor (F : FunctionOnInterval) where
  value : RealRaw
  meaning : Certificate (intervalRaw F) F.lower F.upper value

def ConstructionFor.toLegacy {F : FunctionOnInterval} (c : ConstructionFor F) :
    Integral.ConstructionFor F := ⟨c.value.compute,c.meaning.value_valid⟩

theorem ConstructionFor.equiv {F : FunctionOnInterval} (c d : ConstructionFor F) :
    c.value.Equiv d.value := c.meaning.equiv d.meaning

end ComputableAnalysis.Quadrature
