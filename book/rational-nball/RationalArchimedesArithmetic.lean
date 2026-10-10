import RationalArchimedesShellGeometry
import ComputableAnalysis.FiniteBallShellRecurrence

namespace ComputableAnalysis.RationalPolytopeVolume
set_option maxHeartbeats 2000000

/-- Finite rational grid square brackets, with a literal finite maximization
witness. This theorem uses no completed square root. -/
theorem rational_square_brackets (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (M : Nat) (hM : 0 < M) :
    ∃ l u : ℚ,0 ≤ l ∧ 0 < u ∧ l^2 ≤ q ∧ q ≤ u^2 ∧
      q-3/(M:ℚ) ≤ l^2 ∧ u^2 ≤ q+3/(M:ℚ) := by
  let candidates := (Finset.range (M+1)).filter (fun k : Nat => ((k:ℚ)/(M:ℚ))^2 ≤ q)
  have hc : candidates.Nonempty := ⟨0,by simp [candidates,hq0]⟩
  let k := candidates.max' hc
  have hk := candidates.max'_mem hc
  have hkM : k ≤ M := by
    have ht := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    omega
  have hlq : ((k:ℚ)/(M:ℚ))^2 ≤ q := (Finset.mem_filter.mp hk).2
  have hMq : 0 < (M:ℚ) := by exact_mod_cast hM
  let l : ℚ := (k:ℚ)/(M:ℚ)
  let h : ℚ := 1/(M:ℚ)
  have hl0 : 0 ≤ l := div_nonneg (Nat.cast_nonneg _) hMq.le
  have hl1 : l ≤ 1 := by
    apply (div_le_one hMq).mpr
    exact_mod_cast hkM
  have hh0 : 0 < h := div_pos (by decide) hMq
  have hh1 : h ≤ 1 := by
    apply (div_le_one hMq).mpr
    exact_mod_cast (show 1 ≤ M by omega)
  have hupper : q ≤ (l+h)^2 := by
    by_cases hkEq : k=M
    · have hl : l=1 := by simp [l,hkEq,ne_of_gt hMq]
      rw [hl]
      nlinarith
    · have hkn : k+1 ≤ M := by omega
      by_contra hn
      have ht : ((k+1:Nat):ℚ)/(M:ℚ)=l+h := by simp [l,h,Nat.cast_add,add_div]
      have hmem : k+1 ∈ candidates := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by omega),?_⟩
        rw [ht]
        exact le_of_not_ge hn
      have hm := candidates.le_max' (k+1) hmem
      change k+1 ≤ k at hm
      omega
  have hgap : (l+h)^2-l^2 ≤ 3*h := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl1) hh0.le,mul_nonneg (sub_nonneg.mpr hh1) hh0.le]
  refine ⟨l,l+h,hl0,add_pos_of_nonneg_of_pos hl0 hh0,hlq,hupper,?_,?_⟩
  · change q-3/(M:ℚ) ≤ l^2
    have he : 3/(M:ℚ)=3*h := by simp [h,div_eq_mul_inv]
    rw [he]
    linarith
  · have he : 3/(M:ℚ)=3*h := by simp [h,div_eq_mul_inv]
    rw [he]
    linarith

def radialLower (N : Nat) (i : Fin N) : ℚ := (i:ℚ)/(N:ℚ)
def radialUpper (N : Nat) (i : Fin N) : ℚ := ((i:ℚ)+1)/(N:ℚ)

theorem radial_partition_bounds (N : Nat) (hN : 0 < N) :
    (∀ i,0 ≤ radialLower N i) ∧ (∀ i,0 < radialUpper N i) ∧
    (∀ i,radialLower N i ≤ radialUpper N i) ∧ (∀ i,radialUpper N i ≤ 1) ∧
    (∀ i j : Fin N,i<j → radialUpper N i ≤ radialLower N j) := by
  have hNq : 0 < (N:ℚ) := by exact_mod_cast hN
  refine ⟨fun i => div_nonneg (by positivity) hNq.le,fun i => div_pos (by positivity) hNq,?_,?_,?_⟩
  · intro i; apply (div_le_div_iff_of_pos_right hNq).mpr; linarith
  · intro i; apply (div_le_one hNq).mpr
    exact_mod_cast (show i.val+1 ≤ N by omega)
  · intro i j hij
    apply (div_le_div_iff_of_pos_right hNq).mpr
    exact_mod_cast (show i.val+1 ≤ j.val by exact hij)

/-- The squared bands cover every positive rational squared radius ≤1.
The least endpoint is found among natural indices, without taking a root. -/
theorem radial_partition_covers (N : Nat) (hN : 0 < N) (q : ℚ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ i : Fin N,(radialLower N i)^2 < q ∧ q ≤ (radialUpper N i)^2 := by
  have hNq : (N:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hex : ∃ k : Nat,q ≤ ((k:ℚ)/(N:ℚ))^2 := ⟨N,by simpa [hNq] using hq1⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hkN : k ≤ N := Nat.find_min' hex (by simpa [hNq] using hq1)
  have hk0 : 0 < k := by
    by_contra h
    have he : k=0 := by omega
    change q ≤ ((k:ℚ)/(N:ℚ))^2 at hk
    simp only [he,Nat.cast_zero,zero_div,zero_pow (by decide : 2 ≠ 0)] at hk
    linarith
  refine ⟨⟨k-1,by omega⟩,?_,?_⟩
  · have hm := Nat.find_min hex (show k-1 < k by omega)
    change (((k-1:Nat):ℚ)/(N:ℚ))^2 < q
    exact lt_of_not_ge hm
  · have he : ((k-1:Nat):ℚ)+1=(k:ℚ) := by exact_mod_cast (show k-1+1=k by omega)
    simpa [radialUpper,he] using hk

/-- Finite shell coefficients agree with the independently proved native
rational power sums. -/
theorem shellLower_sum (n N : Nat) (a h : ℚ) :
    RationalBall.shellLower n (a::RationalBall.equalPartition a h N)=
      ∑ i : Fin N,(1-(a+((i:ℚ)+1)*h)^2)*((a+((i:ℚ)+1)*h)^n-(a+(i:ℚ)*h)^n) := by
  induction N generalizing a with
  | zero => simp [RationalBall.equalPartition,RationalBall.shellLower]
  | succ N ih =>
    rw [RationalBall.equalPartition,RationalBall.shellLower,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.cast_zero,zero_add,zero_mul,add_zero,Fin.val_succ,Nat.cast_add,Nat.cast_one]
    have he (i : Fin N) : a+((i:ℚ)+1+1)*h=(a+h)+((i:ℚ)+1)*h := by ring
    have he' (i : Fin N) : a+((i:ℚ)+1)*h=(a+h)+(i:ℚ)*h := by ring
    simp_rw [he,he']
    congr 1
    ring

theorem shellUpper_sum (n N : Nat) (a h : ℚ) :
    RationalBall.shellUpper n (a::RationalBall.equalPartition a h N)=
      ∑ i : Fin N,(1-(a+(i:ℚ)*h)^2)*((a+((i:ℚ)+1)*h)^n-(a+(i:ℚ)*h)^n) := by
  induction N generalizing a with
  | zero => simp [RationalBall.equalPartition,RationalBall.shellUpper]
  | succ N ih =>
    rw [RationalBall.equalPartition,RationalBall.shellUpper,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.cast_zero,zero_add,zero_mul,add_zero,Fin.val_succ,Nat.cast_add,Nat.cast_one]
    have he (i : Fin N) : a+((i:ℚ)+1+1)*h=(a+h)+((i:ℚ)+1)*h := by ring
    have he' (i : Fin N) : a+((i:ℚ)+1)*h=(a+h)+(i:ℚ)*h := by ring
    simp_rw [he,he']
    congr 1
    ring

theorem radial_shell_coefficients (n N : Nat) (hn : 0 < n) (hN : 0 < N) :
    2/((n+2:Nat):ℚ)-2/(N:ℚ) ≤
      (∑ i : Fin N,(1-(radialUpper N i)^2)*((radialUpper N i)^n-(radialLower N i)^n)) ∧
    (∑ i : Fin N,(1-(radialLower N i)^2)*((radialUpper N i)^n-(radialLower N i)^n)) ≤
      2/((n+2:Nat):ℚ)+3/(N:ℚ) := by
  have he := RationalBall.uniform_shells_recurrence_estimate n N hn hN
  dsimp only at he
  rw [shellLower_sum,shellUpper_sum] at he
  simpa [radialLower,radialUpper,div_eq_mul_inv] using And.intro he.1 he.2.2.2

theorem radial_weight_sum (n N : Nat) (hn : 0 < n) (hN : 0 < N) :
    (∑ i : Fin N,((radialUpper N i)^n-(radialLower N i)^n))=1 := by
  have he := Finset.sum_range_sub (fun k : Nat => ((k:ℚ)/(N:ℚ))^n) N
  have hc := Fin.sum_univ_eq_sum_range
    (fun k : Nat => (((k+1:Nat):ℚ)/(N:ℚ))^n-((k:ℚ)/(N:ℚ))^n) N
  rw [he] at hc
  have hNq : (N:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simpa [radialUpper,radialLower,Nat.cast_add,hNq,ne_of_gt hn] using hc

/-- Finite lower and upper disk-radius choices at each rational radial cell. -/
theorem radial_disk_radii (N : Nat) (hN : 0 < N) :
    ∃ l u : Fin N → ℚ,
      (∀ i,0 ≤ l i) ∧ (∀ i,0 < u i) ∧
      (∀ i,(l i)^2 ≤ 1-(radialUpper N i)^2) ∧
      (∀ i,1-(radialUpper N i)^2-1/(N:ℚ) ≤ (l i)^2) ∧
      (∀ i,1-(radialLower N i)^2 ≤ (u i)^2) ∧
      (∀ i,(u i)^2 ≤ 1-(radialLower N i)^2+1/(N:ℚ)) := by
  have hb := radial_partition_bounds N hN
  have hqL (i : Fin N) : 0 ≤ 1-(radialUpper N i)^2 ∧ 1-(radialUpper N i)^2 ≤ 1 := by
    constructor <;> nlinarith [(hb.2.1 i).le,hb.2.2.2.1 i,sq_nonneg (radialUpper N i)]
  have hqU (i : Fin N) : 0 ≤ 1-(radialLower N i)^2 ∧ 1-(radialLower N i)^2 ≤ 1 := by
    have hl1 := le_trans (hb.2.2.1 i) (hb.2.2.2.1 i)
    constructor <;> nlinarith [hb.1 i,hl1,sq_nonneg (radialLower N i)]
  have hM : 0 < 3*N := by omega
  choose l l' hl0 hl'0 hll hlu hle1 hle2 using
    fun i => rational_square_brackets _ (hqL i).1 (hqL i).2 (3*N) hM
  choose u' u hu'0 hu0 hul huu hue1 hue2 using
    fun i => rational_square_brackets _ (hqU i).1 (hqU i).2 (3*N) hM
  have he : (3:ℚ)/((3*N:Nat):ℚ)=1/(N:ℚ) := by
    have hNq : (N:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  refine ⟨l,u,hl0,hu0,hll,?_,huu,?_⟩
  · intro i; simpa only [he] using hle1 i
  · intro i; simpa only [he] using hue2 i

/-- Rational radius approximation adds only the stated finite error to the
shell coefficients. The n-dimensional bracket gap is accounted for explicitly. -/
theorem weighted_radial_shell_bounds (n N : Nat) (hn : 0 < n) (hN : 0 < N)
    (L U δ : ℚ) (hL : 0 ≤ L) (hLU : L ≤ U) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (l u : Fin N → ℚ)
    (hlow : ∀ i,(l i)^2 ≤ 1-(radialUpper N i)^2)
    (hlow' : ∀ i,1-(radialUpper N i)^2-δ ≤ (l i)^2)
    (hup : ∀ i,(u i)^2 ≤ 1-(radialLower N i)^2+δ) :
    (2/((n+2:Nat):ℚ)-2/(N:ℚ))*L-δ*L-(N:ℚ)*(U-L) ≤
      (∑ i : Fin N,((radialUpper N i)^n*L-(radialLower N i)^n*U)*(l i)^2) ∧
    (∑ i : Fin N,((radialUpper N i)^n*U-(radialLower N i)^n*L)*(u i)^2) ≤
      (2/((n+2:Nat):ℚ)+3/(N:ℚ))*U+δ*U+2*(N:ℚ)*(U-L) := by
  have hb := radial_partition_bounds N hN
  have hU := le_trans hL hLU
  have hgap : 0 ≤ U-L := sub_nonneg.mpr hLU
  have hp (i : Fin N) : 0 ≤ (radialLower N i)^n ∧ (radialLower N i)^n ≤ 1 ∧
      0 ≤ (radialUpper N i)^n-(radialLower N i)^n := by
    have hl1 := le_trans (hb.2.2.1 i) (hb.2.2.2.1 i)
    have hpow1 := pow_le_pow_left₀ (hb.1 i) hl1 n
    have hpow := pow_le_pow_left₀ (hb.1 i) (hb.2.2.1 i) n
    refine ⟨pow_nonneg (hb.1 i) _,?_,sub_nonneg.mpr hpow⟩
    simpa using hpow1
  have hloLocal (i : Fin N) :
      ((radialUpper N i)^n*L-(radialLower N i)^n*U)*(l i)^2 ≥
        ((1-(radialUpper N i)^2)*((radialUpper N i)^n-(radialLower N i)^n))*L-
          δ*((radialUpper N i)^n-(radialLower N i)^n)*L-(U-L) := by
    have hMulL := mul_nonneg (hp i).2.2 hL
    have hr := mul_le_mul_of_nonneg_right (hlow' i) hMulL
    have hl1 : (l i)^2 ≤ 1 := by nlinarith [hlow i,sq_nonneg (radialUpper N i)]
    have hA := mul_le_mul_of_nonneg_right (hp i).2.1 (sq_nonneg (l i))
    have herr : (radialLower N i)^n*(l i)^2*(U-L) ≤ U-L := by
      have hcoeff : (radialLower N i)^n*(l i)^2 ≤ 1 := by nlinarith
      simpa using mul_le_mul_of_nonneg_right hcoeff hgap
    nlinarith
  have hupLocal (i : Fin N) :
      ((radialUpper N i)^n*U-(radialLower N i)^n*L)*(u i)^2 ≤
        ((1-(radialLower N i)^2)*((radialUpper N i)^n-(radialLower N i)^n))*U+
          δ*((radialUpper N i)^n-(radialLower N i)^n)*U+2*(U-L) := by
    have hMulU := mul_nonneg (hp i).2.2 hU
    have hr := mul_le_mul_of_nonneg_right (hup i) hMulU
    have hu2 : (u i)^2 ≤ 2 := by nlinarith [hup i,sq_nonneg (radialLower N i)]
    have hA := mul_le_mul_of_nonneg_right (hp i).2.1 (sq_nonneg (u i))
    have herr : (radialLower N i)^n*(u i)^2*(U-L) ≤ 2*(U-L) := by
      have hcoeff : (radialLower N i)^n*(u i)^2 ≤ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hcoeff hgap
    nlinarith
  have hlo := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hloLocal i)
  have hup' := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hupLocal i)
  have hw := radial_weight_sum n N hn hN
  have hc := radial_shell_coefficients n N hn hN
  have hloC := mul_le_mul_of_nonneg_right hc.1 hL
  have hupC := mul_le_mul_of_nonneg_right hc.2 hU
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hlo hup'
  simp_rw [← Finset.sum_mul,← Finset.mul_sum,hw,mul_one] at hlo hup'
  constructor <;> nlinarith

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.rational_square_brackets
#print axioms ComputableAnalysis.RationalPolytopeVolume.radial_partition_bounds
#print axioms ComputableAnalysis.RationalPolytopeVolume.radial_partition_covers
#print axioms ComputableAnalysis.RationalPolytopeVolume.shellLower_sum
#print axioms ComputableAnalysis.RationalPolytopeVolume.shellUpper_sum
#print axioms ComputableAnalysis.RationalPolytopeVolume.radial_shell_coefficients
#print axioms ComputableAnalysis.RationalPolytopeVolume.radial_weight_sum
#print axioms ComputableAnalysis.RationalPolytopeVolume.radial_disk_radii
#print axioms ComputableAnalysis.RationalPolytopeVolume.weighted_radial_shell_bounds

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.rational_square_brackets,
    `ComputableAnalysis.RationalPolytopeVolume.radial_partition_bounds,
    `ComputableAnalysis.RationalPolytopeVolume.radial_partition_covers,
    `ComputableAnalysis.RationalPolytopeVolume.shellLower_sum,
    `ComputableAnalysis.RationalPolytopeVolume.shellUpper_sum,
    `ComputableAnalysis.RationalPolytopeVolume.radial_shell_coefficients,
    `ComputableAnalysis.RationalPolytopeVolume.radial_weight_sum,
    `ComputableAnalysis.RationalPolytopeVolume.radial_disk_radii,
    `ComputableAnalysis.RationalPolytopeVolume.weighted_radial_shell_bounds]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
