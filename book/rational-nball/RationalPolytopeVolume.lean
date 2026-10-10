import RationalConvexBodies
import RationalSimplexLinearAlgebra
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Rat.Floor

/-! Volume axioms on finite rational convex hulls only. The cube subdivision
below is proved from actual hull coverage and lower-dimensional overlaps;
there is no volume function on arbitrary sets or surfaces. -/
namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
abbrev Point (n : Nat) := Fin n → ℚ
abbrev Polytope (n : Nat) := Finset (Point n)
def body {n : Nat} (P : Polytope n) : Set (Point n) := convexHull ℚ (P : Set (Point n))
noncomputable def box {n : Nat} (l u : Point n) : Polytope n := by
  classical
  exact Fintype.piFinset (fun i => {l i,u i})
noncomputable def cube (n : Nat) (r : ℚ) : Polytope n := box (fun _ => 0) (fun _ => r)
noncomputable def translated {n : Nat} (P : Polytope n) (b : Point n) : Polytope n := by
  classical
  exact P.image (fun x i => x i+b i)
noncomputable def transformed {n : Nat} (P : Polytope n)
    (A : Matrix (Fin n) (Fin n) ℚ) : Polytope n := by
  classical
  exact P.image A.mulVec

/-- A set lies in a proper rational affine hyperplane. -/
def Flat {n : Nat} (S : Set (Point n)) : Prop :=
  ∃ a : Point n, ∃ c : ℚ, a ≠ 0 ∧ ∀ x ∈ S, dot a x = c

/-- A finite geometric dissection: exact coverage and only flat overlaps. -/
def Dissection {n : Nat} {ι : Type} [Fintype ι]
    (P : Polytope n) (pieces : ι → Polytope n) : Prop :=
  (∀ x, x ∈ body P ↔ ∃ j, x ∈ body (pieces j)) ∧
  ∀ j k, j ≠ k → Flat (body (pieces j) ∩ body (pieces k))

/-- These are the finite geometric volume axioms. The codomain and all
polytope coordinates are rational. An ambient positively oriented body is
used here; an explicit orientation sign is added when presenting simplices.
No determinant transformation law or cube dilation law is assumed. -/
structure Axioms (n : Nat) where
  volume : Polytope n → ℚ
  extensional : ∀ P Q, body P = body Q → volume P = volume Q
  translation : ∀ P b, volume (translated P b) = volume P
  determinant_one : ∀ P A, A.det = 1 → volume (transformed P A) = volume P
  dissection : ∀ {ι : Type} [Fintype ι] (P : Polytope n) (pieces : ι → Polytope n),
    Dissection P pieces → volume P = ∑ j, volume (pieces j)
  unit_cube : volume (cube n 1) = 1

 theorem mem_body_box {n : Nat} (l u : Point n) (h : ∀ i, l i ≤ u i) (x : Point n) :
    x ∈ body (box l u) ↔ ∀ i, l i ≤ x i ∧ x i ≤ u i := by
  classical
  simp only [body, box, Fintype.coe_piFinset, convexHull_pi, Set.mem_univ_pi]
  simp only [Finset.coe_pair, convexHull_pair, segment_eq_Icc (h _), Set.mem_Icc]

 theorem mem_body_cube (n : Nat) (r : ℚ) (hr : 0 ≤ r) (x : Point n) :
    x ∈ body (cube n r) ↔ ∀ i, 0 ≤ x i ∧ x i ≤ r :=
  mem_body_box _ _ (fun _ => hr) x

 theorem translated_cube_eq_box {n : Nat} (r : ℚ) (b : Point n) :
    translated (cube n r) b = box b (fun i => b i+r) := by
  classical
  ext x
  simp only [translated, cube, box, Finset.mem_image, Fintype.mem_piFinset,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨y,hy,rfl⟩ i
    rcases hy i with hi | hi
    · left; simp [hi]
    · right; simp [hi,add_comm]
  · intro hx
    refine ⟨fun i => x i-b i, ?_, ?_⟩
    · intro i
      rcases hx i with hi | hi
      · left; simp [hi]
      · right; simp [hi]
    · funext i; simp

noncomputable def gridCell {n m : Nat} (r : ℚ) (j : Fin n → Fin m) : Polytope n :=
  box (fun i => (r/(m:ℚ))*(j i:ℚ))
    (fun i => (r/(m:ℚ))*((j i:ℚ)+1))

 theorem gridCell_translation {n m : Nat} (r : ℚ) (j : Fin n → Fin m) :
    gridCell r j = translated (cube n (r/(m:ℚ)))
      (fun i => (r/(m:ℚ))*(j i:ℚ)) := by
  simp only [gridCell, translated_cube_eq_box]
  congr 1
  funext i; ring

/-- A rational interval is covered by its equal subdivisions, including its
right endpoint. The index selector uses rational floor, not compactness. -/
 theorem interval_grid_cover (r : ℚ) (hr : 0 < r) (m : Nat) (hm : 0 < m)
    (x : ℚ) (hx : 0 ≤ x ∧ x ≤ r) :
    ∃ j : Fin m, (r/(m:ℚ))*(j:ℚ) ≤ x ∧ x ≤ (r/(m:ℚ))*((j:ℚ)+1) := by
  have hmQ : (0:ℚ) < m := by exact_mod_cast hm
  have hm0 : (m:ℚ) ≠ 0 := ne_of_gt hmQ
  have hscale : 0 < r/(m:ℚ) := div_pos hr hmQ
  by_cases he : x = r
  · have hcast : ((m-1:Nat):ℚ)+1 = (m:ℚ) := by
      have hnat : m-1+1=m := by omega
      exact_mod_cast hnat
    refine ⟨⟨m-1,by omega⟩, ?_, ?_⟩
    · change r/(m:ℚ)*((m-1:Nat):ℚ) ≤ x
      rw [he]; nlinarith [div_mul_cancel₀ r hm0]
    · change x ≤ r/(m:ℚ)*(((m-1:Nat):ℚ)+1)
      rw [hcast, he, div_mul_cancel₀ r hm0]
  · have hxr : x < r := lt_of_le_of_ne hx.2 he
    have hy0 : 0 ≤ x/(r/(m:ℚ)) := div_nonneg hx.1 hscale.le
    have hym : x/(r/(m:ℚ)) < (m:ℚ) := by
      apply (div_lt_iff₀ hscale).mpr
      simpa [mul_div_cancel₀ _ hm0] using hxr
    let j : Fin m := ⟨Nat.floor (x/(r/(m:ℚ))), (Nat.floor_lt hy0).mpr hym⟩
    refine ⟨j, ?_, ?_⟩
    · have hfloor := Nat.floor_le hy0
      change (r/(m:ℚ))*((Nat.floor (x/(r/(m:ℚ)))) : ℚ) ≤ x
      simpa [mul_comm] using (le_div_iff₀ hscale).mp hfloor
    · have hfloor := (Nat.lt_floor_add_one (x/(r/(m:ℚ)))).le
      change x ≤ (r/(m:ℚ))*((Nat.floor (x/(r/(m:ℚ))) : ℚ)+1)
      simpa [mul_comm] using (div_le_iff₀ hscale).mp hfloor



/-- Equal rational grid cubes really form a finite polytope dissection. -/
theorem cube_grid_dissection (n : Nat) (r : ℚ) (hr : 0 < r)
    (m : Nat) (hm : 0 < m) :
    Dissection (cube n r) (gridCell r : (Fin n → Fin m) → Polytope n) := by
  classical
  have hmQ : (0:ℚ) < m := by exact_mod_cast hm
  have hm0 : (m:ℚ) ≠ 0 := ne_of_gt hmQ
  have hc : 0 < r/(m:ℚ) := div_pos hr hmQ
  have hbounds (j : Fin n → Fin m) :
      ∀ i, r/(m:ℚ)*(j i:ℚ) ≤ r/(m:ℚ)*((j i:ℚ)+1) := by
    intro i; nlinarith
  constructor
  · intro x
    rw [mem_body_cube n r hr.le]
    constructor
    · intro hx
      choose j hj using fun i => interval_grid_cover r hr m hm (x i) (hx i)
      exact ⟨j,(mem_body_box _ _ (hbounds j) x).mpr hj⟩
    · rintro ⟨j,hj⟩
      have hx := (mem_body_box _ _ (hbounds j) x).mp hj
      intro i
      have hj0 : (0:ℚ) ≤ (j i:ℚ) := by positivity
      have hjm : (j i:ℚ)+1 ≤ m := by
        have ht := (j i).isLt
        exact_mod_cast (show (j i).val+1 ≤ m by omega)
      have hlo := mul_nonneg hc.le hj0
      have hhi := mul_le_mul_of_nonneg_left hjm hc.le
      rw [div_mul_cancel₀ r hm0] at hhi
      exact ⟨le_trans hlo (hx i).1, le_trans (hx i).2 hhi⟩
  · intro j k hjk
    obtain ⟨i,hi⟩ : ∃ i, j i ≠ k i := by
      by_contra h; apply hjk; funext i; simpa using not_exists.mp h i
    have hv : (j i).val ≠ (k i).val := by
      intro h; exact hi (Fin.ext h)
    have coordinate_overlap : ∀ (a b : Fin n → Fin m), (a i).val < (b i).val →
        ∀ x ∈ body (gridCell r a) ∩ body (gridCell r b),
          x i = r/(m:ℚ)*((a i:ℚ)+1) := by
      intro a b hab x hx
      have ha := (mem_body_box _ _ (hbounds a) x).mp hx.1
      have hb := (mem_body_box _ _ (hbounds b) x).mp hx.2
      have habQ : (a i:ℚ)+1 ≤ (b i:ℚ) := by
        exact_mod_cast (show (a i).val+1 ≤ (b i).val by omega)
      have hmul := mul_le_mul_of_nonneg_left habQ hc.le
      exact le_antisymm (ha i).2 (le_trans hmul (hb i).1)
    have hn : axis i ≠ (0 : Point n) := by
      intro h; have he := congrFun h i; simp [axis] at he
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · refine ⟨axis i, r/(m:ℚ)*((j i:ℚ)+1),hn,?_⟩
      intro x hx; rw [dot_axis]; exact coordinate_overlap j k hlt x hx
    · refine ⟨axis i, r/(m:ℚ)*((k i:ℚ)+1),hn,?_⟩
      intro x hx; rw [dot_axis]; exact coordinate_overlap k j hgt x ⟨hx.2,hx.1⟩

/-- Cube scaling by integer subdivision, derived from the geometric volume
axioms; the number of grid cells is the n-th power of the subdivision count. -/
theorem cube_subdivision (n : Nat) (V : Axioms n) (r : ℚ) (hr : 0 < r)
    (m : Nat) (hm : 0 < m) :
    V.volume (cube n r) = (m:ℚ)^n * V.volume (cube n (r/(m:ℚ))) := by
  classical
  rw [V.dissection _ _ (cube_grid_dissection n r hr m hm)]
  simp only [gridCell_translation, V.translation, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  norm_cast



/-- A positive integer-sided cube has the expected rational volume. -/
theorem cube_integer (n : Nat) (V : Axioms n) (a : Nat) (ha : 0 < a) :
    V.volume (cube n (a:ℚ)) = (a:ℚ)^n := by
  have haQ : (0:ℚ) < a := by exact_mod_cast ha
  have ha0 : (a:ℚ) ≠ 0 := ne_of_gt haQ
  simpa [div_self ha0,V.unit_cube] using cube_subdivision n V (a:ℚ) haQ a ha

/-- A reciprocal integer-sided cube is obtained by dissecting the unit cube. -/
theorem cube_reciprocal (n : Nat) (V : Axioms n) (b : Nat) (hb : 0 < b) :
    V.volume (cube n (1/(b:ℚ))) = 1/(b:ℚ)^n := by
  have hbQ : (0:ℚ) < b := by exact_mod_cast hb
  have hn0 : (b:ℚ)^n ≠ 0 := pow_ne_zero n (ne_of_gt hbQ)
  have h := cube_subdivision n V 1 (by norm_num) b hb
  rw [V.unit_cube] at h
  apply (eq_div_iff hn0).mpr
  simpa [mul_comm] using h.symm

/-- No dilation law is assumed: positive rational cube volume follows from
normalization, translation invariance, and actual finite grid dissections. -/
theorem cube_ratio (n : Nat) (V : Axioms n) (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) :
    V.volume (cube n ((a:ℚ)/(b:ℚ))) = ((a:ℚ)/(b:ℚ))^n := by
  have haQ : (0:ℚ) < a := by exact_mod_cast ha
  have hbQ : (0:ℚ) < b := by exact_mod_cast hb
  have ha0 : (a:ℚ) ≠ 0 := ne_of_gt haQ
  have hdiv : ((a:ℚ)/(b:ℚ))/(a:ℚ) = 1/(b:ℚ) := by field_simp
  have h := cube_subdivision n V ((a:ℚ)/(b:ℚ)) (div_pos haQ hbQ) a ha
  rw [hdiv,cube_reciprocal n V b hb] at h
  simpa [div_pow, div_eq_mul_inv, mul_pow] using h

/-- Every positive rational cube side is a ratio of positive integers. -/
theorem cube_positive (n : Nat) (V : Axioms n) (k : ℚ) (hk : 0 < k) :
    V.volume (cube n k) = k^n := by
  have hnum : 0 < k.num := Rat.num_pos.mpr hk
  have hnum0 : 0 ≤ k.num := le_of_lt hnum
  have ha : 0 < k.num.toNat := by omega
  have he : (k.num.toNat:ℚ)/(k.den:ℚ) = k := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hnum0,Rat.num_div_den]
  simpa [he] using cube_ratio n V k.num.toNat k.den ha k.pos

/-- In particular, expanding all coordinates of a positive rational cube by
k multiplies its volume by k^n. -/
theorem cube_dilation (n : Nat) (V : Axioms n) (r k : ℚ)
    (hr : 0 < r) (hk : 0 < k) :
    V.volume (cube n (k*r)) = k^n * V.volume (cube n r) := by
  rw [cube_positive n V (k*r) (mul_pos hk hr),cube_positive n V r hr,mul_pow]

theorem cube_doubling (n : Nat) (V : Axioms n) (r : ℚ) (hr : 0 < r) :
    V.volume (cube n (2*r)) = (2:ℚ)^n * V.volume (cube n r) :=
  cube_dilation n V r 2 hr (by norm_num)


/-- Lower-dimensional volume vanishes by dissection additivity itself. -/
theorem volume_flat (n : Nat) (V : Axioms n) (P : Polytope n) (hflat : Flat (body P)) :
    V.volume P = 0 := by
  have hd : Dissection P (fun _ : Fin 2 => P) := by
    constructor
    · intro x; constructor
      · intro hx; exact ⟨0,hx⟩
      · rintro ⟨_,hx⟩; exact hx
    · intro _ _ _
      simpa only [Set.inter_self] using hflat
  have h := V.dissection P (fun _ : Fin 2 => P) hd
  simp only [Fin.sum_univ_two] at h
  linarith

theorem cube_zero_positive_dimension (n : Nat) (hn : 0 < n) (V : Axioms n) :
    V.volume (cube n 0) = 0 := by
  apply volume_flat
  let i : Fin n := ⟨0,hn⟩
  refine ⟨axis i,0,?_,?_⟩
  · intro h; have hi := congrFun h i; simp [axis] at hi
  · intro x hx
    rw [dot_axis]
    have hi := (mem_body_cube n 0 (by norm_num) x).mp hx i
    linarith

theorem cube_zero_dimension (V : Axioms 0) (r : ℚ) :
    V.volume (cube 0 r) = 1 := by
  classical
  have he : cube 0 r = cube 0 1 := by
    ext x; simp [cube,box,Fintype.mem_piFinset]
  rw [he,V.unit_cube]

/-- Negative dilation carries its induced orientation; the geometric body
still has a nonnegative side length. -/
noncomputable def orientedCubeVolume (n : Nat) (V : Axioms n) (k : ℚ) : ℚ :=
  if k < 0 then (-1:ℚ)^n * V.volume (cube n (-k)) else V.volume (cube n k)

theorem orientedCubeVolume_eq_power (n : Nat) (V : Axioms n) (k : ℚ) :
    orientedCubeVolume n V k = k^n := by
  by_cases hneg : k < 0
  · rw [orientedCubeVolume,if_pos hneg,cube_positive n V (-k) (neg_pos.mpr hneg),
      ← mul_pow]
    simp
  · rw [orientedCubeVolume,if_neg hneg]
    by_cases hz : k = 0
    · subst k
      cases n with
      | zero => simp [cube_zero_dimension]
      | succ n => simp [cube_zero_positive_dimension (n+1) (by omega) V]
    · exact cube_positive n V k (lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hz))

/-- The induced orientation makes the dilation law valid for every rational
factor, including negative and zero factors. -/
theorem orientedCubeVolume_dilation (n : Nat) (V : Axioms n) (r k : ℚ) :
    orientedCubeVolume n V (k*r) = k^n * orientedCubeVolume n V r := by
  simp only [orientedCubeVolume_eq_power,mul_pow]

#print axioms cube_grid_dissection
#print axioms cube_subdivision
#print axioms cube_positive
#print axioms orientedCubeVolume_dilation
end ComputableAnalysis.RationalPolytopeVolume
