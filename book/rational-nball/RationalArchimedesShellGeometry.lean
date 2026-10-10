import RationalArchimedesPieces

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

theorem normSq_unit_ne_zero {n : Nat} (q : Point n) (hq : normSq q=1) : q ≠ 0 := by
  intro hz; subst q; simpa [normSq] using hq

theorem product_flat_left {n m : Nat} (C E : Polytope n) (D F : Polytope m)
    (hflat : Flat (body C ∩ body E)) :
    Flat (body (productPoly C D) ∩ body (productPoly E F)) := by
  obtain ⟨a,c,ha,hac⟩ := hflat
  refine ⟨Fin.append a 0,c,?_,?_⟩
  · intro hz; apply ha; ext i
    have h := congrFun hz (i.castAdd m); simpa using h
  · intro x hx
    rw [body_productPoly,body_productPoly] at hx
    have h := hac (leftCoords x) ⟨hx.1.1,hx.2.1⟩
    simpa [dot,Fin.sum_univ_add,leftCoords] using h

theorem list_polytope_pairwise_flat {n : Nat} (L : List (Polytope n))
    (hL : L.Pairwise (fun C D => Flat (body C ∩ body D)))
    (i j : Fin L.length) (hij : i ≠ j) : Flat (body (L.get i) ∩ body (L.get j)) := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact List.pairwise_iff_getElem.mp hL i.val j.val i.isLt j.isLt hlt
  · obtain ⟨a,c,ha,hac⟩ := List.pairwise_iff_getElem.mp hL j.val i.val j.isLt i.isLt hgt
    exact ⟨a,c,ha,fun x hx => hac x ⟨hx.2,hx.1⟩⟩

theorem sum_list_polytope_volumes {n : Nat} (V : Axioms n) (L : List (Polytope n)) :
    (∑ i : Fin L.length,V.volume (L.get i))=(L.map V.volume).sum := by
  rw [← List.sum_ofFn]
  congr 1
  change List.ofFn (V.volume ∘ L.get)=L.map V.volume
  rw [← List.map_ofFn,List.ofFn_get]

/-- Every retained lower-shell body is bounded by the scaled outer polytope;
its rational volume is therefore bounded by a^n times the outer volume. -/
theorem innerShell_retained_volume_le {n : Nat} (hn : 0 < n) (V : Axioms n)
    (P : Polytope n) (S : Finset (Point n)) (haxes : ∀ i,axis i ∈ S)
    (hP : ∀ x ∈ body P,∀ i,0 ≤ x i) (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    V.volume (retainedAfterCuts (dilated P b) (S.toList.map (fun q => (q,a)))) ≤
      a^n*V.volume (orthantOuterPoly S) := by
  let T := retainedAfterCuts (dilated P b) (S.toList.map (fun q => (q,a)))
  have ht : ∀ x ∈ body T,(∀ i,0 ≤ x i) ∧ (∀ q ∈ S,dot q x ≤ a) := by
    intro x hx
    rw [mem_body_retained] at hx
    have hp := hx.1
    rw [body_dilated] at hp
    obtain ⟨p,hp,rfl⟩ := hp
    constructor
    · intro i; exact mul_nonneg hb (hP p hp i)
    · intro q hq
      exact hx.2 (q,a) (List.mem_map.mpr ⟨q,Finset.mem_toList.mpr hq,rfl⟩)
  rcases ha.eq_or_lt with rfl | ha
  · have hf : Flat (body T) := by
      let i : Fin n := ⟨0,hn⟩
      refine ⟨axis i,0,?_,?_⟩
      · intro hz; have h := congrFun hz i; simp [axis] at h
      · intro x hx
        have he := (ht x hx).2 (axis i) (haxes i)
        rw [dot_axis] at he ⊢
        exact le_antisymm he ((ht x hx).1 i)
    rw [volume_flat n V _ hf,zero_pow (by omega),zero_mul]
  · rw [← dilated_volume V (orthantOuterPoly S) a ha]
    apply volume_mono
    intro x hx
    obtain ⟨hpos,hcut⟩ := ht x hx
    rw [body_dilated]
    refine ⟨a⁻¹ • x,?_,?_⟩
    · rw [body_orthantOuterPoly S haxes]
      constructor
      · intro i; exact mul_nonneg (inv_nonneg.mpr ha.le) (hpos i)
      · intro q hq
        rw [dot_smul_right]
        have he := mul_le_mul_of_nonneg_left (hcut q hq) (inv_nonneg.mpr ha.le)
        simpa [inv_mul_cancel₀ (ne_of_gt ha)] using he
    · change a • (a⁻¹ • x)=x
      rw [smul_smul,mul_inv_cancel₀ (ne_of_gt ha),one_smul]

/-- A lower shell's total cap volume has the needed rational difference
bound, even if that difference is negative. -/
theorem innerShellCaps_volume_lower {n : Nat} (hn : 0 < n) (V : Axioms n)
    (P : Polytope n) (S : Finset (Point n)) (haxes : ∀ i,axis i ∈ S)
    (hS : ∀ q ∈ S,normSq q=1) (hP : ∀ x ∈ body P,∀ i,0 ≤ x i)
    (a b : ℚ) (ha : 0 ≤ a) (hb : 0 < b) :
    b^n*V.volume P-a^n*V.volume (orthantOuterPoly S) ≤
      ((innerShellCaps P S a b).map V.volume).sum := by
  have hnormal : ∀ ac ∈ S.toList.map (fun q => (q,a)),ac.1 ≠ 0 := by
    intro ac hac
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hac
    exact normSq_unit_ne_zero q (hS q (Finset.mem_toList.mp hq))
  have he := sequential_clip_volume V (S.toList.map (fun q => (q,a))) hnormal (dilated P b)
  rw [dilated_volume V P b hb] at he
  have hl := innerShell_retained_volume_le hn V P S haxes hP a b ha hb.le
  change _ ≤ ((removedCaps (dilated P b) (S.toList.map (fun q => (q,a)))).map V.volume).sum
  linarith

/-- Distinct radial lower shells have flat overlaps: a later tangent cap
can meet an earlier shell only in its own tangent plane. -/
theorem innerShellCaps_between_flat {n : Nat} (P : Polytope n) (S : Finset (Point n))
    (hP : ∀ x ∈ body P,normSq x ≤ 1) (hS : ∀ q ∈ S,normSq q=1)
    (a b c d : ℚ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 ≤ b) (hbc : b ≤ c)
    (C D : Polytope n) (hC : C ∈ innerShellCaps P S a b) (hD : D ∈ innerShellCaps P S c d) :
    Flat (body C ∩ body D) := by
  obtain ⟨⟨q,t⟩,hqt,hcut⟩ := removedCaps_cut (dilated P d) _ D hD
  obtain ⟨q',hq',he⟩ := List.mem_map.mp hqt
  have hEq : q'=q ∧ c=t := by simpa using Prod.mk.inj he
  rcases hEq with ⟨heq,het⟩
  subst q
  subst t
  have hunit := hS q' (Finset.mem_toList.mp hq')
  refine ⟨q',c,normSq_unit_ne_zero q' hunit,?_⟩
  intro x hx
  have hn := (innerShellCaps_norm_bounds P S hP hS a b ha C hC x hx.1).2
  have hnorm : normSq x ≤ c^2 := by nlinarith
  exact le_antisymm (tangent_radius_upper q' x hunit c hc hnorm) (hcut x hx.2)

/-- Genuine finite lower-shell comparison for any rational partition and
rational disk radii satisfying the explicit squared-radius constraints. -/
theorem finite_inner_shell_comparison {n : Nat} (hn : 0 < n) {ι : Type} [Fintype ι]
    [LinearOrder ι] (V : Axioms n) (W : Axioms 2) (Z : Axioms (n+2))
    (P : Polytope n) (S : Finset (Point n)) (D : Polytope 2) (Y : Polytope (n+2))
    (haxes : ∀ i,axis i ∈ S) (hS : ∀ q ∈ S,normSq q=1)
    (hP : ∀ x ∈ body P,normSq x ≤ 1 ∧ ∀ i,0 ≤ x i)
    (hD : ∀ x ∈ body D,normSq x ≤ 1 ∧ ∀ i,0 ≤ x i)
    (hY : ∀ x,normSq x ≤ 1 → (∀ i,0 ≤ x i) → x ∈ body Y)
    (a b r : ι → ℚ) (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 < b i) (hr : ∀ i,0 ≤ r i)
    (hradius : ∀ i,(r i)^2 ≤ 1-(b i)^2) (hordered : ∀ i j,i<j → b i ≤ a j) :
    (∑ i,((b i)^n*V.volume P-(a i)^n*V.volume (orthantOuterPoly S))*(r i)^2*W.volume D) ≤
      Z.volume Y := by
  classical
  let caps (i : ι) := innerShellCaps P S (a i) (b i)
  let pieces (j : Σ i,Fin (caps i).length) := productPoly ((caps j.1).get j.2) (dilated D (r j.1))
  have hnormal (i : ι) : ∀ ac ∈ S.toList.map (fun q => (q,a i)),ac.1 ≠ 0 := by
    intro ac hac
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hac
    exact normSq_unit_ne_zero q (hS q (Finset.mem_toList.mp hq))
  have hcontain : ∀ j,body (pieces j) ⊆ body Y := by
    intro j z hz
    have hcap := List.get_mem (caps j.1) j.2
    have hnorm := innerShell_product_in_unitBall ((caps j.1).get j.2) D (b j.1) (r j.1)
      (fun x hx => (innerShellCaps_norm_bounds P S (fun x hx => (hP x hx).1) hS
        (a j.1) (b j.1) (ha j.1) _ hcap x hx).2)
      (fun x hx => (hD x hx).1) (hradius j.1) z hz
    apply hY z hnorm
    have hz' := hz
    rw [body_productPoly] at hz'
    have hp := removedCaps_subset (dilated P (b j.1)) _ _ hcap hz'.1
    rw [body_dilated] at hp
    obtain ⟨p,hp,hpx⟩ := hp
    obtain ⟨q,hq,hqy⟩ := body_dilated D (r j.1) ▸ hz'.2
    intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · have he := congrFun hpx i
      change 0 ≤ leftCoords z i
      rw [← he]
      exact mul_nonneg (hb j.1).le ((hP p hp).2 i)
    · have he := congrFun hqy i
      change 0 ≤ rightCoords z i
      rw [← he]
      exact mul_nonneg (hr j.1) ((hD q hq).2 i)
  have hflat : ∀ i j,i ≠ j → Flat (body (pieces i) ∩ body (pieces j)) := by
    rintro ⟨i,k⟩ ⟨j,l⟩ hne
    apply product_flat_left
    by_cases hij : i=j
    · subst j
      have hkl : k ≠ l := by intro he; subst l; exact hne rfl
      exact list_polytope_pairwise_flat (caps i) (removedCaps_pairwise _ _ (hnormal i)) k l hkl
    · rcases lt_or_gt_of_ne hij with hij | hji
      · exact innerShellCaps_between_flat P S (fun x hx => (hP x hx).1) hS
          (a i) (b i) (a j) (b j) (ha i) (ha j) (hb i).le (hordered i j hij)
          _ _ (List.get_mem _ _) (List.get_mem _ _)
      · obtain ⟨a',c',ha',hac⟩ := innerShellCaps_between_flat P S (fun x hx => (hP x hx).1) hS
          (a j) (b j) (a i) (b i) (ha j) (ha i) (hb j).le (hordered j i hji)
          _ _ (List.get_mem _ _) (List.get_mem _ _)
        exact ⟨a',c',ha',fun x hx => hac x ⟨hx.2,hx.1⟩⟩
  have hcmp := finite_disjoint_volume_le (by omega : 0 < n+2) Z Y pieces hcontain hflat
  have hpiece (i : ι) :
      (∑ k : Fin (caps i).length,Z.volume (pieces ⟨i,k⟩))=
        ((caps i).map V.volume).sum*(r i)^2*W.volume D := by
    simp only [pieces,productPoly_volume V W Z,
      dilated_volume_nonneg_dimension (by decide : 0 < 2) W D (r i) (hr i)]
    rw [← Finset.sum_mul,sum_list_polytope_volumes]
    ring
  rw [Fintype.sum_sigma] at hcmp
  simp_rw [hpiece] at hcmp
  apply le_trans _ hcmp
  apply Finset.sum_le_sum
  intro i hi
  have hc := innerShellCaps_volume_lower hn V P S haxes hS (fun x hx => (hP x hx).2)
    (a i) (b i) (ha i) (hb i)
  have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg (r i)) (volume_nonneg W D))
  simpa [mul_assoc] using hm

noncomputable def hullCuts {n : Nat} (hn : 0 < n) (P : Polytope n) : List (Point n × ℚ) :=
  (Classical.choose (pointHull_nonzero_halfspaces n hn P)).toList

theorem hullCuts_normal {n : Nat} (hn : 0 < n) (P : Polytope n) :
    ∀ ac ∈ hullCuts hn P,ac.1 ≠ 0 := by
  intro ac hac
  exact (Classical.choose_spec (pointHull_nonzero_halfspaces n hn P)).1 ac (Finset.mem_toList.mp hac)

theorem hullCuts_body {n : Nat} (hn : 0 < n) (P : Polytope n) (x : Point n) :
    x ∈ body P ↔ ∀ ac ∈ hullCuts hn P,dot ac.1 x ≤ ac.2 := by
  have h := (Classical.choose_spec (pointHull_nonzero_halfspaces n hn P)).2 x
  simpa [hullCuts,Finset.mem_toList] using h

noncomputable def outerShellCaps {n : Nat} (hn : 0 < n) (P Q : Polytope n) (a b : ℚ) :
    List (Polytope n) := removedCaps (dilated Q b) (hullCuts hn (dilated P a))

theorem radius_ball_in_dilated_outer {n : Nat} (Q : Polytope n)
    (hQ : ∀ x,normSq x ≤ 1 → (∀ i,0 ≤ x i) → x ∈ body Q)
    (b : ℚ) (hb : 0 < b) (x : Point n) (hnorm : normSq x ≤ b^2) (hpos : ∀ i,0 ≤ x i) :
    x ∈ body (dilated Q b) := by
  rw [body_dilated]
  refine ⟨b⁻¹ • x,?_,?_⟩
  · apply hQ
    · rw [normSq_smul]
      have hbound := mul_le_mul_of_nonneg_left hnorm (sq_nonneg b⁻¹)
      have he : (b⁻¹)^2*b^2=1 := by field_simp
      rw [he] at hbound
      exact hbound
    · intro i; exact mul_nonneg (inv_nonneg.mpr hb.le) (hpos i)
  · change b • (b⁻¹ • x)=x
    rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hb),one_smul]

theorem dilated_inner_subset_outer {n : Nat} (P Q : Polytope n)
    (hP : ∀ x ∈ body P,normSq x ≤ 1 ∧ ∀ i,0 ≤ x i)
    (hQ : ∀ x,normSq x ≤ 1 → (∀ i,0 ≤ x i) → x ∈ body Q)
    (a b : ℚ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    body (dilated P a) ⊆ body (dilated Q b) := by
  intro x hx
  rw [body_dilated] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  apply radius_ball_in_dilated_outer Q hQ b hb
  · rw [normSq_smul]
    nlinarith [(hP p hp).1,sq_nonneg a]
  · intro i; exact mul_nonneg ha ((hP p hp).2 i)

/-- Upper shell caps have exactly the outer-shell difference volume. -/
theorem outerShellCaps_volume {n : Nat} (hn : 0 < n) (V : Axioms n) (P Q : Polytope n)
    (hP : ∀ x ∈ body P,normSq x ≤ 1 ∧ ∀ i,0 ≤ x i)
    (hQ : ∀ x,normSq x ≤ 1 → (∀ i,0 ≤ x i) → x ∈ body Q)
    (a b : ℚ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    ((outerShellCaps hn P Q a b).map V.volume).sum=b^n*V.volume Q-a^n*V.volume P := by
  have hbodies : body (retainedAfterCuts (dilated Q b) (hullCuts hn (dilated P a)))=
      body (dilated P a) := by
    ext x
    rw [mem_body_retained,← hullCuts_body]
    exact and_iff_right_of_imp (fun hx => dilated_inner_subset_outer P Q hP hQ a b ha hb hab hx)
  have he := sequential_clip_volume V (hullCuts hn (dilated P a))
    (hullCuts_normal hn _) (dilated Q b)
  rw [V.extensional _ _ hbodies,dilated_volume V Q b hb,
    dilated_volume_nonneg_dimension hn V P a ha] at he
  change ((removedCaps (dilated Q b) (hullCuts hn (dilated P a))).map V.volume).sum = _
  linarith

/-- Every point in a strict-lower, closed-upper radial band is covered by an
actual upper shell cap. No curved shell is assigned a volume. -/
theorem outerShellCaps_cover_band {n : Nat} (hn : 0 < n) (P Q : Polytope n)
    (hP : ∀ x ∈ body P,normSq x ≤ 1 ∧ ∀ i,0 ≤ x i)
    (hQ : ∀ x,normSq x ≤ 1 → (∀ i,0 ≤ x i) → x ∈ body Q)
    (a b : ℚ) (ha : 0 ≤ a) (hb : 0 < b) (x : Point n) (hpos : ∀ i,0 ≤ x i)
    (hlow : a^2 < normSq x) (hhigh : normSq x ≤ b^2) :
    ∃ C ∈ outerShellCaps hn P Q a b,x ∈ body C := by
  have hout : x ∉ body (dilated P a) := by
    intro hx
    rw [body_dilated] at hx
    obtain ⟨p,hp,rfl⟩ := hx
    rw [normSq_smul] at hlow
    nlinarith [(hP p hp).1,sq_nonneg a]
  have hret : x ∉ body (retainedAfterCuts (dilated Q b) (hullCuts hn (dilated P a))) := by
    intro hx
    rw [mem_body_retained] at hx
    exact hout ((hullCuts_body hn _ x).mpr hx.2)
  exact removedCaps_cover_outside _ _ x (radius_ball_in_dilated_outer Q hQ b hb x hhigh hpos) hret

theorem normSq_zero_eq_zero {n : Nat} (x : Point n) (hx : normSq x=0) : x=0 := by
  ext i
  have he : x i^2 ≤ normSq x := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  simp only [Pi.zero_apply]
  nlinarith [sq_nonneg (x i)]

/-- Genuine finite upper-shell cover, for any finite rational partition whose
squared radial bands cover (0,1]. The zero-prefix slice is a flat product. -/
theorem finite_outer_shell_comparison {n : Nat} (hn : 0 < n) {ι : Type} [Fintype ι]
    (V : Axioms n) (W : Axioms 2) (Z : Axioms (n+2))
    (P Q : Polytope n) (E : Polytope 2) (X : Polytope (n+2))
    (hP : ∀ x ∈ body P,normSq x ≤ 1 ∧ ∀ i,0 ≤ x i)
    (hQ : ∀ x,normSq x ≤ 1 → (∀ i,0 ≤ x i) → x ∈ body Q)
    (hE : ∀ y,normSq y ≤ 1 → (∀ i,0 ≤ y i) → y ∈ body E)
    (hX : ∀ z ∈ body X,normSq z ≤ 1 ∧ ∀ i,0 ≤ z i)
    (a b r : ι → ℚ) (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 < b i) (hr : ∀ i,0 < r i)
    (hab : ∀ i,a i ≤ b i) (hradius : ∀ i,1-(a i)^2 ≤ (r i)^2)
    (hcover : ∀ q : ℚ,0 < q → q ≤ 1 → ∃ i,(a i)^2 < q ∧ q ≤ (b i)^2) :
    Z.volume X ≤ ∑ i,((b i)^n*V.volume Q-(a i)^n*V.volume P)*(r i)^2*W.volume E := by
  classical
  let caps (i : ι) := outerShellCaps hn P Q (a i) (b i)
  let pieces (j : Option (Σ i,Fin (caps i).length)) : Polytope (n+2) :=
    j.elim (productPoly {0} E) (fun k => productPoly ((caps k.1).get k.2) (dilated E (r k.1)))
  have hcoverPieces : ∀ z ∈ body X,∃ j,z ∈ body (pieces j) := by
    intro z hz
    obtain ⟨hball,hpositive⟩ := hX z hz
    let x : Point n := leftCoords z
    let y : Point 2 := rightCoords z
    have hzEq : z=Fin.append x y := by
      ext i; refine Fin.addCases (fun j => by simp [x,leftCoords]) (fun j => by simp [y,rightCoords]) i
    have hsum : normSq x+normSq y ≤ 1 := by rw [hzEq,normSq_append] at hball; exact hball
    have hxpos : ∀ i,0 ≤ x i := fun i => hpositive (i.castAdd 2)
    have hypos : ∀ i,0 ≤ y i := fun i => hpositive (i.natAdd n)
    have hx1 : normSq x ≤ 1 := by linarith [normSq_nonneg y]
    by_cases hxzero : normSq x=0
    · have he : x=0 := normSq_zero_eq_zero x hxzero
      refine ⟨none,?_⟩
      change z ∈ body (productPoly {0} E)
      rw [body_productPoly]
      constructor
      · simpa [body,convexHull_singleton] using he
      · exact hE y (by linarith [normSq_nonneg x]) hypos
    · have hx0 : 0 < normSq x := lt_of_le_of_ne (normSq_nonneg x) (Ne.symm hxzero)
      obtain ⟨i,hlow,hhigh⟩ := hcover (normSq x) hx0 hx1
      obtain ⟨C,hC,hxC⟩ := outerShellCaps_cover_band hn P Q hP hQ (a i) (b i) (ha i) (hb i) x hxpos hlow hhigh
      obtain ⟨k,hk⟩ := List.mem_iff_get.mp hC
      refine ⟨some ⟨i,k⟩,?_⟩
      change z ∈ body (productPoly ((caps i).get k) (dilated E (r i)))
      rw [body_productPoly]
      constructor
      · change x ∈ body ((outerShellCaps hn P Q (a i) (b i)).get k)
        rw [hk]
        exact hxC
      · apply radius_ball_in_dilated_outer E hE (r i) (hr i) y
          (by linarith [hradius i]) hypos
  have hcmp := finite_cover_volume_le (by omega : 0 < n+2) Z X pieces hcoverPieces
  have hzero : V.volume ({0} : Polytope n)=0 := by
    apply volume_flat
    let i : Fin n := ⟨0,hn⟩
    refine ⟨axis i,0,?_,?_⟩
    · intro he; have h := congrFun he i; simp [axis] at h
    · intro x hx; have he : x=0 := by simpa [body,convexHull_singleton] using hx
      subst x; simp [dot]
  have hpiece (i : ι) :
      (∑ k : Fin (caps i).length,Z.volume (pieces (some ⟨i,k⟩)))=
        ((b i)^n*V.volume Q-(a i)^n*V.volume P)*(r i)^2*W.volume E := by
    simp only [pieces,Option.elim_some,productPoly_volume V W Z,dilated_volume W E (r i) (hr i)]
    rw [← Finset.sum_mul,sum_list_polytope_volumes,outerShellCaps_volume hn V P Q hP hQ _ _ (ha i) (hb i) (hab i)]
    ring
  rw [Fintype.sum_option,Fintype.sum_sigma] at hcmp
  have he0 : Z.volume (pieces none)=0 := by
    change Z.volume (productPoly {0} E)=0
    rw [productPoly_volume V W Z,hzero,zero_mul]
  rw [he0,zero_add] at hcmp
  simpa only [hpiece] using hcmp

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.normSq_unit_ne_zero
#print axioms ComputableAnalysis.RationalPolytopeVolume.product_flat_left
#print axioms ComputableAnalysis.RationalPolytopeVolume.list_polytope_pairwise_flat
#print axioms ComputableAnalysis.RationalPolytopeVolume.sum_list_polytope_volumes
#print axioms ComputableAnalysis.RationalPolytopeVolume.innerShell_retained_volume_le
#print axioms ComputableAnalysis.RationalPolytopeVolume.innerShellCaps_volume_lower
#print axioms ComputableAnalysis.RationalPolytopeVolume.innerShellCaps_between_flat
#print axioms ComputableAnalysis.RationalPolytopeVolume.finite_inner_shell_comparison
#print axioms ComputableAnalysis.RationalPolytopeVolume.hullCuts_normal
#print axioms ComputableAnalysis.RationalPolytopeVolume.hullCuts_body
#print axioms ComputableAnalysis.RationalPolytopeVolume.radius_ball_in_dilated_outer
#print axioms ComputableAnalysis.RationalPolytopeVolume.dilated_inner_subset_outer
#print axioms ComputableAnalysis.RationalPolytopeVolume.outerShellCaps_volume
#print axioms ComputableAnalysis.RationalPolytopeVolume.outerShellCaps_cover_band
#print axioms ComputableAnalysis.RationalPolytopeVolume.normSq_zero_eq_zero
#print axioms ComputableAnalysis.RationalPolytopeVolume.finite_outer_shell_comparison

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.normSq_unit_ne_zero,
    `ComputableAnalysis.RationalPolytopeVolume.product_flat_left,
    `ComputableAnalysis.RationalPolytopeVolume.list_polytope_pairwise_flat,
    `ComputableAnalysis.RationalPolytopeVolume.sum_list_polytope_volumes,
    `ComputableAnalysis.RationalPolytopeVolume.innerShell_retained_volume_le,
    `ComputableAnalysis.RationalPolytopeVolume.innerShellCaps_volume_lower,
    `ComputableAnalysis.RationalPolytopeVolume.innerShellCaps_between_flat,
    `ComputableAnalysis.RationalPolytopeVolume.finite_inner_shell_comparison,
    `ComputableAnalysis.RationalPolytopeVolume.hullCuts_normal,
    `ComputableAnalysis.RationalPolytopeVolume.hullCuts_body,
    `ComputableAnalysis.RationalPolytopeVolume.radius_ball_in_dilated_outer,
    `ComputableAnalysis.RationalPolytopeVolume.dilated_inner_subset_outer,
    `ComputableAnalysis.RationalPolytopeVolume.outerShellCaps_volume,
    `ComputableAnalysis.RationalPolytopeVolume.outerShellCaps_cover_band,
    `ComputableAnalysis.RationalPolytopeVolume.normSq_zero_eq_zero,
    `ComputableAnalysis.RationalPolytopeVolume.finite_outer_shell_comparison]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
