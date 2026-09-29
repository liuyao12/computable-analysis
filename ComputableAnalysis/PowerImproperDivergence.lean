import ComputableAnalysis.PowerDivergence
import ComputableAnalysis.HarmonicImproperBounds

/-! Divergence of reciprocal-power improper integrals, certified by finite
harmonic rectangles and independently constructed compact integrals. -/
namespace ComputableAnalysis
open Integral FormalPowerSeries ZetaReal BinomialPower BinomialPower.Global

namespace BinomialPower.Global

def uniformBound (p : Real) (rho : Rat) (h0 : 0 ≤ rho) (h1 : rho < 1) : Rat :=
  let A := chart p rho h0 h1
  polynomialBound (coefficient (A.parameter p 0)) (A.cutoff 0)+2

theorem uniformBound_nonneg (p : Real) (rho : Rat) (h0 : 0 ≤ rho) (h1 : rho < 1) :
    0 ≤ uniformBound p rho h0 h1 := by
  have h := polynomialBound_nonneg (coefficient ((chart p rho h0 h1).parameter p 0)) ((chart p rho h0 h1).cutoff 0)
  unfold uniformBound
  grind only

theorem canonical_uniform_upper (p : Real) {rho x : Rat} (h0 : 0 ≤ rho) (h1 : rho < 1)
    (hx : 0 ≤ x) (hxr : x ≤ rho) (n : Nat) :
    ((canonicalValue p x).compute n).lo ≤ uniformBound p rho h0 h1 := by
  let A := chart p rho h0 h1
  have hp := chart_bounds p rho h0 h1
  have hv := A.value_valid hp hx hxr
  have h := (GeometricSequence.raw_within hv 0).congr_left
    (canonicalValue_valid p hx (by grind)) hv (canonicalValue_agrees A hp hx hxr) n 0
  have hb := polynomial_unit_bound (coefficient (A.parameter p 0)) (A.cutoff 0) hx (by grind : x ≤ 1)
  rw [← polynomial_prefix] at hb
  change qabs (powerPolynomial (A.parameter p 0) (A.cutoff 0) x) ≤ polynomialBound (coefficient (A.parameter p 0)) (A.cutoff 0) at hb
  have hself := self_le_qabs (powerPolynomial (A.parameter p 0) (A.cutoff 0) x)
  change ((canonicalValue p x).compute n).lo ≤ powerPolynomial (A.parameter p 0) (A.cutoff 0) x+2*((1 : Rat)/2)^0 ∧ _ at h
  rw [Rat.pow_zero,Rat.mul_one] at h
  change _ ≤ polynomialBound (coefficient (A.parameter p 0)) (A.cutoff 0)+2
  exact Rat.le_trans h.1 (by grind only)
end BinomialPower.Global

namespace Integral
theorem harmonic_rectangles_lower {f : Rat → RealRaw} {a : Rat} (ha : 0 < a)
    (N : Nat) (hN : 0 < N) {hf : ∀ x, a ≤ x ∧ x ≤ a*IntegerPowerIntegral.dyadic N → (f x).Valid}
    {I : RealRaw} (hI : HasIntegral (onInterval f a (a*IntegerPowerIntegral.dyadic N) hf) I)
    (hc : ∀ x, a ≤ x → x ≤ a*IntegerPowerIntegral.dyadic N → (RealRaw.ofRat x⁻¹).Le (f x))
    {C : Rat} (hupper : ∀ x, a ≤ x → x ≤ a*IntegerPowerIntegral.dyadic N → ∀ n, ((f x).compute n).lo ≤ C) :
    (RealRaw.ofRat ((N : Rat)/2)).Le I := by
  let H := IntegerPowerIntegral.harmonicBounds a ha N hN
  let B : Bounds (onInterval f a (a*IntegerPowerIntegral.dyadic N) hf) :=
    { partition := H.partition
      lower := H.lower
      upper := fun _ => C
      lower_le := by
        intro k hk x hx n
        have h := H.lower_le k hk x hx 0
        have hdom := (H.partition.cell k hk).contains_inDomain hx
        exact Rat.le_trans h (hc x hdom.1 hdom.2 0 n)
      upper_ge := by
        intro k hk x hx n
        have hdom := (H.partition.cell k hk).contains_inDomain hx
        exact hupper x hdom.1 hdom.2 n }
  intro i j
  have h := (hI.bounds B j).1
  change H.lowerSum ≤ (I.compute j).hi at h
  rw [(IntegerPowerIntegral.harmonic_bounds_sums a ha N hN).1] at h
  exact h
end Integral

namespace PowerIntegral
open IntegerPowerIntegral (dyadic dyadic_pos dyadic_mono harmonic_zero_endpoint)

def zeroDyadicEndpoint (n : Nat) : Rat := (dyadic (2*n+1))⁻¹

theorem zeroDyadicEndpoint_bounds (n : Nat) : 0 < zeroDyadicEndpoint n ∧ zeroDyadicEndpoint n ≤ 1 := by
  have h := dyadic_mono (Nat.zero_le (2*n+1))
  change 1 ≤ dyadic (2*n+1) at h
  exact inverse_unit_bounds h

def zeroDyadicExhaustion (p : Real) (n : Nat) : FunctionOnInterval :=
  function p (zeroDyadicEndpoint n) 1 (zeroDyadicEndpoint_bounds n).1 (Rat.le_refl)

theorem zeroDyadic_compact (p : Real) (n : Nat) :
    HasIntegral (zeroDyadicExhaustion p n)
      (compact p (zeroDyadicEndpoint n) 1 (zeroDyadicEndpoint_bounds n).1 (zeroDyadicEndpoint_bounds n).2 (Rat.le_refl)) :=
  compact_hasIntegral p (zeroDyadicEndpoint_bounds n).1 (zeroDyadicEndpoint_bounds n).2 (Rat.le_refl)

theorem zeroDyadic_lower (p : Real) (hp : (RealRaw.ofRat 1).Le p.preferred) (n : Nat) {I : RealRaw}
    (hI : HasIntegral (zeroDyadicExhaustion p n) I) : (RealRaw.ofRat (n : Rat)).Le I := by
  let a := zeroDyadicEndpoint n
  have ha := zeroDyadicEndpoint_bounds n
  have he : a*dyadic (2*n+1)=1 := harmonic_zero_endpoint _
  have h0 : 0 ≤ 1-a := by dsimp [a]; grind
  have h1 : 1-a < 1 := by dsimp [a]; grind
  have hr : ∀ x, a ≤ x → x ≤ a*dyadic (2*n+1) → (RealRaw.ofRat x⁻¹).Le (value p x) := by
    intro x hx hx1
    rw [he] at hx1
    exact zero_ge_reciprocal p hp (by dsimp [a] at hx; grind) hx1
  have hu : ∀ x, a ≤ x → x ≤ a*dyadic (2*n+1) → ∀ k,
      ((value p x).compute k).lo ≤ uniformBound (parameter p) (1-a) h0 h1 := by
    intro x hx hx1 k
    rw [he] at hx1
    exact canonical_uniform_upper (parameter p) h0 h1 (by grind) (by grind) k
  have hh : HasIntegral (onInterval (value p) a (a*dyadic (2*n+1)) (fun x hx =>
      value_valid p (by dsimp [a] at hx; grind) (by rw [he] at hx; exact hx.2))) I := by
    simpa only [he,zeroDyadicExhaustion,function] using hI
  have h := harmonic_rectangles_lower ha.1 (2*n+1) (by omega) hh hr hu
  intro i j
  have hx := h i j
  change (((2*n+1 : Nat) : Rat)/2) ≤ (I.compute j).hi at hx
  change (n : Rat) ≤ (I.compute j).hi
  simp only [Rat.natCast_add,Rat.natCast_mul,show ((1 : Nat) : Rat)=1 by decide,show ((2 : Nat) : Rat)=2 by decide] at hx
  grind only

theorem zero_diverges (p : Real) (hp : (RealRaw.ofRat 1).Le p.preferred) (I : RealRaw) :
    ¬ HasIntegralLimit (zeroDyadicExhaustion p) I :=
  no_limit_of_growing_lower_bounds (fun n _ h => zeroDyadic_lower p hp n h) I

def infinityDyadicExhaustion (p : Real) (n : Nat) : FunctionOnInterval :=
  infinityFunction p 1 (1*dyadic (2*n+1)) (Rat.le_refl)

theorem infinityDyadic_compact (p : Real) (n : Nat) :
    HasIntegral (infinityDyadicExhaustion p n)
      (infinityCompact p 1 (1*dyadic (2*n+1)) (Rat.le_refl) (by
        have h := dyadic_mono (Nat.zero_le (2*n+1)); change 1 ≤ dyadic (2*n+1) at h; grind)) :=
  infinityCompact_hasIntegral p (Rat.le_refl) (by
    have h := dyadic_mono (Nat.zero_le (2*n+1)); change 1 ≤ dyadic (2*n+1) at h; grind)

theorem infinityDyadic_lower (p : Real) (hp : p.preferred.Le (RealRaw.ofRat 1)) (n : Nat) {I : RealRaw}
    (hI : HasIntegral (infinityDyadicExhaustion p n) I) : (RealRaw.ofRat (n : Rat)).Le I := by
  let b := 1*dyadic (2*n+1)
  have hb : 1 ≤ b := by have h := dyadic_mono (Nat.zero_le (2*n+1)); change 1 ≤ dyadic (2*n+1) at h; dsimp [b]; grind
  have hbi := inverse_unit_bounds hb
  have h0 : 0 ≤ 1-b⁻¹ := by grind
  have h1 : 1-b⁻¹ < 1 := by grind
  let C := uniformBound p (1-b⁻¹) h0 h1
  have hC := uniformBound_nonneg p (1-b⁻¹) h0 h1
  have hu : ∀ x, 1 ≤ x → x ≤ b → ∀ k, ((infinityValue p x).compute k).lo ≤ C := by
    intro x hx hxb k
    have hxi := inverse_unit_bounds hx
    have hg := inverse_gap hx hxb
    have h := canonical_uniform_upper p h0 h1 (show 0 ≤ 1-x⁻¹ by grind) (show 1-x⁻¹ ≤ 1-b⁻¹ by grind) k
    have hr := Rat.mul_nonneg (Rat.le_of_lt hxi.1) (Rat.le_of_lt hxi.1)
    have hs := Rat.mul_le_mul_of_nonneg_left hxi.2 (Rat.le_of_lt hxi.1)
    have hm := Rat.mul_le_mul_of_nonneg_left h hr
    have hh := Rat.mul_le_mul_of_nonneg_right (show x⁻¹*x⁻¹ ≤ 1 by grind) hC
    simp only [infinityValue,RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos hr]
    change x⁻¹*x⁻¹*((canonicalValue p (1-x⁻¹)).compute k).lo ≤ C
    change x⁻¹*x⁻¹*C ≤ 1*C at hh
    change x⁻¹*x⁻¹*((canonicalValue p (1-x⁻¹)).compute k).lo ≤ x⁻¹*x⁻¹*C at hm
    grind only
  have h := harmonic_rectangles_lower (by decide : (0 : Rat) < 1) (2*n+1) (by omega) hI
    (fun x hx _ => infinity_ge_reciprocal p hp hx) hu
  intro i j
  have hx := h i j
  change (((2*n+1 : Nat) : Rat)/2) ≤ (I.compute j).hi at hx
  change (n : Rat) ≤ (I.compute j).hi
  simp only [Rat.natCast_add,Rat.natCast_mul,show ((1 : Nat) : Rat)=1 by decide,show ((2 : Nat) : Rat)=2 by decide] at hx
  grind only

theorem infinity_diverges (p : Real) (hp : p.preferred.Le (RealRaw.ofRat 1)) (I : RealRaw) :
    ¬ HasIntegralLimit (infinityDyadicExhaustion p) I :=
  no_limit_of_growing_lower_bounds (fun n _ h => infinityDyadic_lower p hp n h) I

end PowerIntegral
end ComputableAnalysis
