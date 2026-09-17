import ComputableAnalysis.MonotoneAverage
import ComputableAnalysis.RationalSampleLimits

/-! Quantitative finite-sample calculus. A local derivative certificate is a
quadratic remainder estimate at rational endpoints, not an assumed integral
identity. Its data is closed under sums and products. The finite FTC follows
by telescoping on a fixed dyadic mesh before letting that mesh refine. -/
namespace ComputableAnalysis.FiniteSampleCalculus
open ClosedArctanInverse MonotoneAverage RationalSampleLimits

abbrev SampleFunction := Rat → Nat → Rat

/-- All numerical constants are supplied. The cutoff is proof-side evidence
for a fixed rational cell; it is not an oracle used by the integral program. -/
structure Model (F D : SampleFunction) where
  valueBound : Rat
  slopeBound : Rat
  errorBound : Rat
  valueBound_nonneg : 0 ≤ valueBound
  slopeBound_nonneg : 0 ≤ slopeBound
  errorBound_nonneg : 0 ≤ errorBound
  value : ∀ x q, Unit x → qabs (F x q) ≤ valueBound
  slope : ∀ x q, Unit x → qabs (D x q) ≤ slopeBound
  local_error : ∀ a b, Unit a → Unit b → a<b →
    ∃ N, ∀ q, N≤q → qabs (F b q-F a q-(b-a)*D a q) ≤ errorBound*(b-a)*(b-a)

theorem mul_abs_bound {a b A B : Rat} (hA : 0≤A)
    (ha : qabs a≤A) (hb : qabs b≤B) : qabs (a*b)≤A*B := by
  rw [qabs_mul]
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ha (qabs_nonneg b))
    (Rat.mul_le_mul_of_nonneg_left hb hA)

private theorem increment_bound {a b d h D E : Rat}
    (hh : 0≤h) (hh1 : h≤1) (hD : 0≤D) (hE : 0≤E)
    (hd : qabs d≤D) (he : qabs (b-a-h*d)≤E*h*h) :
    qabs (b-a)≤h*(D+E) := by
  have hi : (b-a-h*d)+h*d=b-a := by grind
  have ht:=qabs_add_le (b-a-h*d) (h*d)
  rw [hi] at ht
  have hmul:=mul_abs_bound hh (show qabs h≤h by rw [qabs_eq_self_of_nonneg hh]; exact Rat.le_refl) hd
  have hsq:=Rat.mul_le_mul_of_nonneg_left hh1 hh
  have hsqE:=Rat.mul_le_mul_of_nonneg_left hsq hE
  grind only

private theorem product_error {a₀ a₁ b₀ b₁ da db h A B DA DB EA EB : Rat}
    (hh : 0≤h) (hh1 : h≤1) (hA : 0≤A) (hB : 0≤B)
    (hDA : 0≤DA) (hDB : 0≤DB) (hEA : 0≤EA) (hEB : 0≤EB)
    (ha : qabs a₀≤A) (hb : qabs b₀≤B)
    (hda : qabs da≤DA) (hdb : qabs db≤DB)
    (heA : qabs (a₁-a₀-h*da)≤EA*h*h)
    (heB : qabs (b₁-b₀-h*db)≤EB*h*h) :
    qabs (a₁*b₁-a₀*b₀-h*(da*b₀+a₀*db)) ≤
      (EA*B+A*EB+(DA+EA)*(DB+EB))*h*h := by
  have ha':=increment_bound hh hh1 hDA hEA hda heA
  have hb':=increment_bound hh hh1 hDB hEB hdb heB
  have hs1:=mul_abs_bound (Rat.mul_nonneg (Rat.mul_nonneg hEA hh) hh) heA hb
  have hs2:=mul_abs_bound hA ha heB
  have hs3:=mul_abs_bound (Rat.mul_nonneg hh (Rat.add_nonneg hDA hEA)) ha' hb'
  have ht1:=qabs_add_le ((a₁-a₀-h*da)*b₀) (a₀*(b₁-b₀-h*db))
  have ht2:=qabs_add_le (((a₁-a₀-h*da)*b₀)+(a₀*(b₁-b₀-h*db))) ((a₁-a₀)*(b₁-b₀))
  have hi : ((a₁-a₀-h*da)*b₀)+(a₀*(b₁-b₀-h*db))+(a₁-a₀)*(b₁-b₀)=
      a₁*b₁-a₀*b₀-h*(da*b₀+a₀*db) := by grind
  rw [hi] at ht2
  grind only

namespace Model

def constant (v : Nat → Rat) (K : Rat) (hK : 0≤K)
    (hv : ∀ q, qabs (v q)≤K) : Model (fun _ q => v q) (fun _ _ => 0) where
  valueBound := K
  slopeBound := 0
  errorBound := 0
  valueBound_nonneg := hK
  slopeBound_nonneg := by decide
  errorBound_nonneg := by decide
  value := fun _ q _ => hv q
  slope := fun _ _ _ => by decide +kernel
  local_error := by
    intro a b ha hb hab
    refine ⟨0,fun q hq => ?_⟩
    have he : v q-v q-(b-a)*0=0 := by grind
    rw [he,qabs_eq_self_of_nonneg (by decide),Rat.zero_mul,Rat.zero_mul]
    exact Rat.le_refl

def const (v : Rat) : Model (fun _ _ => v) (fun _ _ => 0) :=
  constant (fun _ => v) (qabs v) (qabs_nonneg v) (fun _ => Rat.le_refl)

def identity : Model (fun x _ => x) (fun _ _ => 1) where
  valueBound := 1
  slopeBound := 1
  errorBound := 0
  valueBound_nonneg := by decide
  slopeBound_nonneg := by decide
  errorBound_nonneg := by decide
  value := fun x _ hx => by rw [qabs_eq_self_of_nonneg hx.1]; exact hx.2
  slope := fun _ _ _ => by decide +kernel
  local_error := by
    intro a b ha hb hab
    refine ⟨0,fun q hq => ?_⟩
    have he : b-a-(b-a)*1=0 := by grind
    rw [he,qabs_eq_self_of_nonneg (by decide),Rat.zero_mul,Rat.zero_mul]
    exact Rat.le_refl

def add {F D G E : SampleFunction} (f : Model F D) (g : Model G E) :
    Model (fun x q => F x q+G x q) (fun x q => D x q+E x q) where
  valueBound := f.valueBound+g.valueBound
  slopeBound := f.slopeBound+g.slopeBound
  errorBound := f.errorBound+g.errorBound
  valueBound_nonneg := Rat.add_nonneg f.valueBound_nonneg g.valueBound_nonneg
  slopeBound_nonneg := Rat.add_nonneg f.slopeBound_nonneg g.slopeBound_nonneg
  errorBound_nonneg := Rat.add_nonneg f.errorBound_nonneg g.errorBound_nonneg
  value := by
    intro x q hx
    have hf:=f.value x q hx; have hg:=g.value x q hx; have h:=qabs_add_le (F x q) (G x q)
    grind only
  slope := by
    intro x q hx
    have hf:=f.slope x q hx; have hg:=g.slope x q hx; have h:=qabs_add_le (D x q) (E x q)
    grind only
  local_error := by
    intro a b ha hb hab
    obtain ⟨N,hN⟩:=f.local_error a b ha hb hab
    obtain ⟨M,hM⟩:=g.local_error a b ha hb hab
    refine ⟨max N M,fun q hq => ?_⟩
    have hf:=hN q (by omega);have hg:=hM q (by omega)
    have h:=qabs_add_le (F b q-F a q-(b-a)*D a q) (G b q-G a q-(b-a)*E a q)
    have he : (F b q-F a q-(b-a)*D a q)+(G b q-G a q-(b-a)*E a q)=
        (F b q+G b q)-(F a q+G a q)-(b-a)*(D a q+E a q) := by grind
    rw [he] at h
    grind only

def neg {F D : SampleFunction} (f : Model F D) :
    Model (fun x q => -F x q) (fun x q => -D x q) where
  valueBound := f.valueBound
  slopeBound := f.slopeBound
  errorBound := f.errorBound
  valueBound_nonneg := f.valueBound_nonneg
  slopeBound_nonneg := f.slopeBound_nonneg
  errorBound_nonneg := f.errorBound_nonneg
  value := fun x q hx => by rw [qabs_neg]; exact f.value x q hx
  slope := fun x q hx => by rw [qabs_neg]; exact f.slope x q hx
  local_error := by
    intro a b ha hb hab
    obtain ⟨N,hN⟩:=f.local_error a b ha hb hab
    refine ⟨N,fun q hq => ?_⟩
    have he : -F b q- -F a q-(b-a)*(-D a q)= -(F b q-F a q-(b-a)*D a q) := by grind
    rw [he,qabs_neg]
    exact hN q hq

def sub {F D G E : SampleFunction} (f : Model F D) (g : Model G E) :
    Model (fun x q => F x q-G x q) (fun x q => D x q-E x q) := by
  simpa only [Rat.sub_eq_add_neg] using f.add g.neg

def mul {F D G E : SampleFunction} (f : Model F D) (g : Model G E) :
    Model (fun x q => F x q*G x q) (fun x q => D x q*G x q+F x q*E x q) where
  valueBound := f.valueBound*g.valueBound
  slopeBound := f.slopeBound*g.valueBound+f.valueBound*g.slopeBound
  errorBound := f.errorBound*g.valueBound+f.valueBound*g.errorBound+
    (f.slopeBound+f.errorBound)*(g.slopeBound+g.errorBound)
  valueBound_nonneg := Rat.mul_nonneg f.valueBound_nonneg g.valueBound_nonneg
  slopeBound_nonneg := Rat.add_nonneg (Rat.mul_nonneg f.slopeBound_nonneg g.valueBound_nonneg)
    (Rat.mul_nonneg f.valueBound_nonneg g.slopeBound_nonneg)
  errorBound_nonneg := Rat.add_nonneg
    (Rat.add_nonneg (Rat.mul_nonneg f.errorBound_nonneg g.valueBound_nonneg)
      (Rat.mul_nonneg f.valueBound_nonneg g.errorBound_nonneg))
    (Rat.mul_nonneg (Rat.add_nonneg f.slopeBound_nonneg f.errorBound_nonneg)
      (Rat.add_nonneg g.slopeBound_nonneg g.errorBound_nonneg))
  value := fun x q hx => mul_abs_bound f.valueBound_nonneg (f.value x q hx) (g.value x q hx)
  slope := by
    intro x q hx
    have h1:=mul_abs_bound f.slopeBound_nonneg (f.slope x q hx) (g.value x q hx)
    have h2:=mul_abs_bound f.valueBound_nonneg (f.value x q hx) (g.slope x q hx)
    have h:=qabs_add_le (D x q*G x q) (F x q*E x q)
    grind only
  local_error := by
    intro a b ha hb hab
    obtain ⟨N,hN⟩:=f.local_error a b ha hb hab
    obtain ⟨M,hM⟩:=g.local_error a b ha hb hab
    refine ⟨max N M,fun q hq => ?_⟩
    have hh : 0≤b-a := by grind
    have hh1 : b-a≤1 := by have a0:=ha.1; have b1:=hb.2; grind
    exact product_error hh hh1 f.valueBound_nonneg g.valueBound_nonneg
      f.slopeBound_nonneg g.slopeBound_nonneg f.errorBound_nonneg g.errorBound_nonneg
      (f.value a q ha) (g.value a q ha) (f.slope a q ha) (g.slope a q ha)
      (hN q (by omega)) (hM q (by omega))

theorem increment_eventual {F D : SampleFunction} (f : Model F D)
    (a b : Rat) (ha : Unit a) (hb : Unit b) (hab : a<b) :
    ∃ N, ∀ q, N≤q → qabs (F b q-F a q) ≤ (b-a)*(f.slopeBound+f.errorBound) := by
  obtain ⟨N,hN⟩:=f.local_error a b ha hb hab
  refine ⟨N,fun q hq => ?_⟩
  have hh : 0≤b-a := by grind
  have hh1 : b-a≤1 := by have h0:=ha.1;have h1:=hb.2;grind
  exact increment_bound hh hh1 f.slopeBound_nonneg f.errorBound_nonneg
    (f.slope a q ha) (hN q hq)

/-- Finite algebra can rewrite a model without changing its bounds or theorem. -/
def congr {F D G E : SampleFunction} (f : Model F D)
    (hF : ∀ x q, F x q=G x q) (hD : ∀ x q, D x q=E x q) : Model G E := by
  have heF : F=G := funext (fun x => funext (hF x))
  have heD : D=E := funext (fun x => funext (hD x))
  rw [←heF,←heD]
  exact f

end Model

/-- The finite telescoping estimate underlying the sample FTC. A fixed mesh
has finitely many cells, so a common evaluation stage exists. -/
theorem finite_telescope {F D : SampleFunction} (f : Model F D)
    (d : Nat) {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a<b) :
    ∃ N, ∀ q, N≤q →
      qabs (F b q-F a q-(b-a)*left (fun x => D x q) a b d) ≤
        f.errorBound*(b-a)*(b-a)*meshRadius d := by
  induction d generalizing a b with
  | zero =>
    obtain ⟨N,hN⟩:=f.local_error a b ha hb hab
    refine ⟨N,fun q hq => ?_⟩
    rw [show meshRadius 0=(1:Rat) by decide +kernel,Rat.mul_one]
    exact hN q hq
  | succ d ih =>
    let m : Rat := (a+b)/2
    have hm : Unit m := midpoint_unit ha hb
    have ham : a<m := by dsimp [m]; simp only [Rat.div_def]; grind
    have hmb : m<b := by dsimp [m]; simp only [Rat.div_def]; grind
    obtain ⟨N,hN⟩:=ih ha hm ham
    obtain ⟨M,hM⟩:=ih hm hb hmb
    refine ⟨max N M,fun q hq => ?_⟩
    have h1:=hN q (by omega);have h2:=hM q (by omega)
    have h:=qabs_add_le (F m q-F a q-(m-a)*left (fun x=>D x q) a m d)
      (F b q-F m q-(b-m)*left (fun x=>D x q) m b d)
    have he : (F m q-F a q-(m-a)*left (fun x=>D x q) a m d)+
        (F b q-F m q-(b-m)*left (fun x=>D x q) m b d)=
        F b q-F a q-(b-a)*left (fun x=>D x q) a b (d+1) := by
      simp only [left]; dsimp [m]; simp only [Rat.div_def]; grind only
    rw [he] at h
    have hr : meshRadius (d+1)=meshRadius d/2 := by
      simp only [meshRadius,Rat.pow_succ,Rat.div_def,Rat.one_mul,Rat.inv_mul_rev]
      exact Rat.mul_comm _ _
    rw [hr]
    dsimp [m] at h1 h2
    simp only [Rat.div_def] at h1 h2 ⊢
    grind only

/-- The reusable FTC for a chosen numerical quadrature. The last hypothesis
is a mesh-comparison estimate for that computation, not an endpoint identity. -/
theorem chosen_samples_FTC {F D : SampleFunction} (f : Model F D)
    (I : Nat → Rat) (B : Rat) (hB : 0≤B)
    (mesh_error : ∀ d q, d≤q →
      qabs (I q-left (fun x=>D x q) 0 1 d) ≤ B*meshRadius d) :
    Close I (fun q => F 1 q-F 0 q) := by
  have hs : Small (fun d => (f.errorBound+B)*meshRadius d) :=
    small_of_geometric_bound (f.errorBound+B) (Rat.add_nonneg f.errorBound_nonneg hB)
      (fun d => by
        rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg (Rat.add_nonneg f.errorBound_nonneg hB)
          (Rat.le_of_lt (meshRadius_pos d)))]; exact Rat.le_refl)
  intro eps
  obtain ⟨d,hd⟩:=hs eps
  obtain ⟨N,hN⟩:=finite_telescope f d (a:=0) (b:=1)
    ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ (by decide)
  refine ⟨max N d,fun q hq => ?_⟩
  have h1:=hN q (by omega)
  have h2:=mesh_error d q (by omega)
  have h3:=hd d (Nat.le_refl d)
  have he : (1:Rat)-0=1 := by decide +kernel
  rw [he,Rat.mul_one,Rat.mul_one,Rat.one_mul] at h1
  have ht:=qabs_sub_le (I q-left (fun x=>D x q) 0 1 d)
    (F 1 q-F 0 q-left (fun x=>D x q) 0 1 d)
  have hsub : (I q-left (fun x=>D x q) 0 1 d)-(F 1 q-F 0 q-left (fun x=>D x q) 0 1 d)=
    I q-(F 1 q-F 0 q) := by grind
  rw [hsub] at ht
  have hp:=self_le_qabs ((f.errorBound+B)*meshRadius d)
  grind only

end ComputableAnalysis.FiniteSampleCalculus
