import topology.subset_properties

open topological_space

variables (X : Type) 
variables [decidable_eq X] [topological_space X]

@[derive decidable_eq]
inductive compactification : Type
| infinity : compactification
| of : X → compactification

local notation `∞` := compactification.infinity
local postfix (name := compactification) `*`:1900 := compactification

variables {X}

noncomputable instance : ∀ (U : set X*), decidable $ ∞ ∈ U := λ _, classical.dec _

def compactification.open (U : set X*) : Prop :=
if (∞ ∉ U) 
then (∃ (V : set X), is_open V ∧ U = compactification.of '' V)
else (∃ (C : set X), is_compact C ∧ is_closed C ∧ U = (compactification.of '' C)ᶜ)

lemma compactification.open_of_infinity_not_mem {U : set X*} (h : ∞ ∉ U) :
  compactification.open U ↔ 
  (∃ (V : set X), is_open V ∧ U = compactification.of '' V) :=
⟨λ H, by rwa [compactification.open, if_pos h] at H, λ H, by rwa [compactification.open, if_pos h]⟩

lemma compactification.open_of_infinity_mem {U : set X*} (h : ∞ ∈ U) :
  compactification.open U ↔ 
  (∃ (C : set X), is_compact C ∧ is_closed C ∧ U = (compactification.of '' C)ᶜ ) :=
⟨λ H, by rwa [compactification.open, if_neg (show ¬¬ ∞ ∈ U, by rwa not_not)] at H, 
 λ H, by rwa [compactification.open, if_neg (show ¬¬ ∞ ∈ U, by rwa not_not)]⟩


lemma compactification.open_empty : compactification.open (∅ : set X*) :=
begin 
  rw compactification.open_of_infinity_not_mem (set.not_mem_empty ∞),
  exact ⟨∅, is_open_empty, eq.symm $ set.image_empty _⟩,
end

lemma compactification.open_univ : compactification.open (set.univ : set X*) :=
begin 
  rw compactification.open_of_infinity_mem (set.mem_univ _),
  refine ⟨∅, is_compact_empty, is_closed_empty, _⟩,
  simp only [set.image_empty, set.compl_empty],
  -- sorry,
end

lemma compactification.open_inter (s t : set X*) 
  (hs : compactification.open s) (ht : compactification.open t) :
  compactification.open (s ∩ t) :=
begin
  by_cases h1 : ∞ ∈ s;
  by_cases h2 : ∞ ∈ t,
  { rw compactification.open_of_infinity_mem h1 at hs,
    rw compactification.open_of_infinity_mem h2 at ht,
    obtain ⟨⟨a, ha1, ha2, rfl⟩, ⟨b, hb1, hb2, rfl⟩⟩ := ⟨hs, ht⟩,
    rw compactification.open_of_infinity_mem,
    work_on_goal 2 { exact ⟨h1, h2⟩ },
    rw [← set.compl_union, ← set.image_union],
    exact ⟨_, ha1.union hb1, ha2.union hb2, rfl⟩, },
  { rw compactification.open_of_infinity_mem h1 at hs,
    rw compactification.open_of_infinity_not_mem h2 at ht,
    obtain ⟨⟨a, ha1, ha2, rfl⟩, ⟨b, hb, rfl⟩⟩ := ⟨hs, ht⟩,
    rw [compactification.open_of_infinity_not_mem],
    work_on_goal 2 { rw [set.mem_inter_iff, not_and_distrib], tauto, },
    refine ⟨aᶜ ∩ b, is_open.inter _ hb, _⟩,
    { simpa only [is_open_compl_iff] },
    ext1 ⟨x⟩,
    { simp only [set.mem_inter_iff, set.mem_image, and_false, exists_false], },
    { simp only [set.mem_inter_iff, set.mem_compl_iff, set.mem_image, exists_eq_right], } },
  { rw compactification.open_of_infinity_mem h2 at ht,
    rw compactification.open_of_infinity_not_mem h1 at hs,
    obtain ⟨⟨a, ha1, ha2, rfl⟩, ⟨b, hb, rfl⟩⟩ := ⟨ht, hs⟩,
    rw [compactification.open_of_infinity_not_mem],
    work_on_goal 2 { rw [set.mem_inter_iff, not_and_distrib], tauto, },
    refine ⟨b ∩ aᶜ, hb.inter _, _⟩,
    { simpa only [is_open_compl_iff] },
    ext1 ⟨x⟩,
    { simp only [set.mem_inter_iff, set.mem_image, and_false, exists_false, false_and], },
    { simp only [set.mem_inter_iff, set.mem_image, exists_eq_right, set.mem_compl_iff], }, },
  { rw compactification.open_of_infinity_not_mem at ht hs ⊢,
    work_on_goal 2 { rw [set.mem_inter_iff], tauto, },
    work_on_goal 2 { tauto, },
    work_on_goal 2 { tauto, },
    obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩ := ⟨hs, ht⟩,
    rw ← set.image_inter,
    work_on_goal 2 { rintros x y h, exact compactification.of.inj h, },
    exact ⟨_, ha.inter hb, rfl⟩ },
end

lemma compactification.open_union (s t : set X*) 
  (hs : compactification.open s) (ht : compactification.open t) :
  compactification.open (s ∪ t) :=
begin
  by_cases h1 : ∞ ∈ s;
  by_cases h2 : ∞ ∈ t,
  { rw compactification.open_of_infinity_mem h1 at hs,
    rw compactification.open_of_infinity_mem h2 at ht,
    obtain ⟨⟨a, ha1, ha2, rfl⟩, ⟨b, hb1, hb2, rfl⟩⟩ := ⟨hs, ht⟩,
    rw compactification.open_of_infinity_mem,
    work_on_goal 2 { rw [set.mem_union], tauto, },
    rw [← set.compl_inter, ← set.image_inter],
    work_on_goal 2 { rintros x _ ⟨⟩, refl, },
    exact ⟨_, ha1.inter_right  hb2, ha2.inter hb2, rfl⟩, },
  { rw compactification.open_of_infinity_mem h1 at hs,
    rw compactification.open_of_infinity_not_mem h2 at ht,
    obtain ⟨⟨a, ha1, ha2, rfl⟩, ⟨b, hb, rfl⟩⟩ := ⟨hs, ht⟩,
    rw [compactification.open_of_infinity_mem],
    work_on_goal 2 { rw [set.mem_union], tauto, },
    refine ⟨bᶜ ∩ a, ha1.inter_left _, is_closed.inter _ ha2, _⟩,
    { simpa only [is_closed_compl_iff] },
    { simpa only [is_closed_compl_iff] },
    ext1 ⟨x⟩,
    { simp only [set.mem_union, set.mem_compl_iff, set.mem_image, and_false, exists_false, 
        or_false], },
    { simp only [set.mem_union, set.mem_compl_iff, set.mem_image, exists_eq_right, 
        set.mem_inter_iff, not_and],
      tauto!, } },
  { rw compactification.open_of_infinity_mem h2 at ht,
    rw compactification.open_of_infinity_not_mem h1 at hs,
    obtain ⟨⟨a, ha1, ha2, rfl⟩, ⟨b, hb, rfl⟩⟩ := ⟨ht, hs⟩,
    rw [compactification.open_of_infinity_mem],
    work_on_goal 2 { rw [set.mem_union], tauto, },
    refine ⟨bᶜ ∩ a, ha1.inter_left _, is_closed.inter _ ha2, _⟩,
    { simpa only [is_closed_compl_iff], },
    { simpa only [is_closed_compl_iff], },
    ext1 ⟨x⟩,
    { simp only [set.mem_union, set.mem_image, and_false, exists_false, 
        set.mem_compl_iff, false_or], },
    { simp only [set.mem_union, set.mem_image, exists_eq_right, set.mem_compl_iff, 
        set.mem_inter_iff, not_and], }, },
  { rw compactification.open_of_infinity_not_mem at ht hs ⊢,
    work_on_goal 2 { rw [set.mem_inter_iff], tauto, },
    work_on_goal 2 { tauto, },
    work_on_goal 2 { tauto, },
    obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩ := ⟨hs, ht⟩,
    rw ← set.image_inter,
    work_on_goal 2 { rintros x y h, exact compactification.of.inj h, },
    exact ⟨_, ha.inter hb, rfl⟩ },
end

lemma compactification.open_sUnion (s : set $ set X*) 
  (hs : ∀ i, i ∈ s → compactification.open i) :
  compactification.open (⋃₀ s) :=
begin 
  set s1 := {i | i ∈ s ∧ ∞ ∈ i} with s1_eq,
  set s2 := {i | i ∈ s ∧ ∞ ∉ i} with s2_eq,
  have hs1 : ∀ i, i ∈ s1 → ∃ (C : set X), is_compact C ∧ is_closed C ∧ 
    i = (compactification.of '' C)ᶜ,
  { intros i hi, 
    specialize hs _ hi.1,
    rwa compactification.open_of_infinity_mem hi.2 at hs, }, 
  have hs2 : ∀ i, i ∈ s2 → ∃ (V : set X), is_open V ∧ i = compactification.of '' V,
  { intros i hi, 
    specialize hs _ hi.1,
    rwa compactification.open_of_infinity_not_mem hi.2 at hs, }, 
  choose x hx1 hx2 hx3 using hs1,
  choose y hy1 hy2 using hs2,
  
  rw [show s = s1 ∪ s2, begin 
    ext1,
    simp only [set.mem_union, set.mem_set_of_eq],
    tauto,
  end, set.sUnion_union, show ⋃₀ s1 = ⋃ (i : s1), (compactification.of '' x _ i.2)ᶜ, 
  begin 
    rw [set.sUnion_eq_Union],
    exact set.Union_congr (λ ⟨i, hi⟩, hx3 _ hi),
  end, ←set.compl_Inter, show ⋃₀ s2 = ⋃ (i : s2), compactification.of '' y _ i.2,
  begin 
    rw [set.sUnion_eq_Union],
    exact set.Union_congr (λ ⟨i, hi⟩, hy2 _ hi),    
  end, ← set.image_Union],
  refine compactification.open_union _ _ _ _,
  { by_cases H : s1.nonempty,
    { rw show (⋂ (i : s1), compactification.of '' x i.1 i.2) = 
        (compactification.of '' ⋂ (i : s1), x i.1 i.2), 
      begin 
        ext t,
        rcases t with ⟨t⟩,
        { simp only [set.mem_set_of_eq, set.Inter_coe_set, set.mem_Inter, set.mem_image, and_false, 
            exists_false, iff_false, not_forall, not_false_iff, exists_prop, and_true],
          rcases H with ⟨t, h⟩,
          exact ⟨t, h.1, h.2⟩, },
        { simp only [set.mem_Inter, set.mem_image, exists_eq_right], }
      end,
      rw compactification.open_of_infinity_mem,
      work_on_goal 2 
      { simp only [set.mem_set_of_eq, set.Inter_coe_set, set.compl_Inter, set.mem_Union, 
          set.mem_compl_iff, set.mem_image, and_false, exists_false, not_false_iff, exists_prop, 
          and_true], },
      refine ⟨_, _, _, rfl⟩,
      work_on_goal 2 
      { refine is_closed_Inter (λ i, hx2 _ i.2), },
      cases H with t ht,
      refine is_compact_of_is_closed_subset (hx1 _ ht) (is_closed_Inter (λ i, hx2 _ i.2)) _,
      refine set.Inter_subset _ (⟨t, ht⟩ : s1), },
    { rw set.not_nonempty_iff_eq_empty at H,
      haveI : is_empty s1,
      { exact set.is_empty_coe_sort.mpr H, },
      rw [set.Inter_of_empty, set.compl_univ],
      exact compactification.open_empty, } },
  
  { rw [compactification.open_of_infinity_not_mem],
    work_on_goal 2 
    { simp only [set.mem_Union, set.mem_image, and_false, exists_false, not_false_iff], },
    refine ⟨_, is_open_Union _, rfl⟩,
    rintros ⟨i, hi⟩,
    exact hy1 _ hi, } 
end

instance  : topological_space X* :=
{ is_open := compactification.open,
  is_open_univ := compactification.open_univ,
  is_open_inter := compactification.open_inter,
  is_open_sUnion := compactification.open_sUnion }

lemma compactification.is_open_iff (s : set X*) :
  is_open s ↔ compactification.open s := 
iff.rfl

instance : compact_space X* :=
{ is_compact_univ := begin 
  -- have := is_compact.elim_finite_subcover,
  rw is_compact_iff_finite_subcover,
  intros ι U hU1 hU2,
  haveI : decidable_eq ι := classical.dec_eq _,

  set ι1 := { i : ι | ∞ ∈ U i } with ι1_eq,
  set ι2 := { i : ι | ∞ ∉ U i } with ι2_eq,
  have hι1 : ∀ (i : ι1), ∃ (C : set X), is_compact C ∧ is_closed C ∧ 
    U i = (compactification.of '' C)ᶜ,
  { intros i,
    specialize hU1 i,
    rwa [compactification.is_open_iff, compactification.open_of_infinity_mem] at hU1,
    exact i.2, },
  have hι2 : ∀ (i : ι2), ∃ (V : set X), is_open V ∧ U i = compactification.of '' V,
  { intros i,
    specialize hU1 i,
    rwa [compactification.is_open_iff, compactification.open_of_infinity_not_mem] at hU1,
    exact i.2, },
  choose ℭ hℭ1 hℭ2 hℭ3 using hι1,
  choose 𝔙 h𝔙1 h𝔙2 using hι2,
  have H : ∃ (i : ι), ∞ ∈ U i,
  { rw ← set.mem_Union,
    exact hU2 ⟨⟩, },
  rcases H with ⟨i, hi⟩,
  
  have subset1 : ℭ ⟨i, hi⟩ ⊆ ⋃ (a : {j : ι1 // (j : ι) ≠ i} ⊕ ι2), 
    sum.rec_on a (λ j, (ℭ (j : ι1))ᶜ) 𝔙,
  { intros x hx,
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hU2 (set.mem_univ _ : compactification.of x ∈ set.univ),
    by_cases mem1 : j ∈ ι1,
    { specialize hℭ3 ⟨j, mem1⟩,
      simp only [subtype.coe_mk] at hℭ3,
      dsimp only at hj,
      rw hℭ3 at hj,
      refine ⟨_, ⟨sum.inl ⟨⟨j, mem1⟩, λ r, _⟩, rfl⟩, _⟩,
      { rw subtype.coe_mk at r,
        subst r,
        have hx' : compactification.of x ∈ compactification.of '' ℭ ⟨j, mem1⟩ := ⟨_, hx, rfl⟩,
        exact hj hx', },
      dsimp only [subtype.coe_mk, set.mem_compl_iff],
      contrapose! hj,
      simpa only [set.mem_compl_iff, set.mem_image, exists_eq_right, set.not_not_mem], },
    { replace mem1 : j ∈ ι2,
      { simpa only using mem1, },
      refine ⟨_, ⟨sum.inr ⟨j, mem1⟩, rfl⟩, _⟩,
      simp only at hj ⊢,
      specialize h𝔙2 ⟨j, mem1⟩,
      rw [subtype.coe_mk] at h𝔙2,
      rw h𝔙2 at hj,
      obtain ⟨y, hy1, hy2⟩ := hj,
      rwa compactification.of.inj hy2 at *, }, },
  have hcompact := hℭ1 ⟨i, hi⟩,
  rw is_compact_iff_finite_subcover at hcompact,
  specialize hcompact _ _ subset1,
  { rintros (⟨⟨⟨k, hk1⟩, (hk2 : k ≠ i)⟩⟩|⟨k, hk⟩),
    { simpa only [subtype.coe_mk, is_open_compl_iff] using hℭ2 ⟨k, hk1⟩, },
    { simpa only using h𝔙1 ⟨k, hk⟩, }, },
  obtain ⟨S, hS⟩ := hcompact,
  set emb : ({j : ι2 // ↑j ≠ i} ⊕ ι2) → ι := λ x, sum.rec_on x (λ y, y.val.val) subtype.val,
  set S' : finset ι := finset.image (λ y, sum.rec_on y (subtype.val ∘ subtype.val) subtype.val) S 
    with S'_eq,
  refine ⟨insert i S', _⟩, 
  rintros ⟨x⟩ ⟨⟩,
  { refine ⟨U i, ⟨i, _⟩, hi⟩,
    simp only [finset.mem_insert, eq_self_iff_true, true_or, set.Union_true], },
  by_cases hx : x ∈ ℭ ⟨i, hi⟩,
  { specialize hS hx,
    simp only [set.mem_Union] at hS ⊢,
    rcases hS with ⟨(⟨⟨j, hj0⟩, hj1⟩|⟨j, hj1⟩), ⟨hj2, hj3⟩⟩;
    simp only [subtype.coe_mk] at hj2 hj3,
    { refine ⟨j, _, _⟩,
      { rw [finset.mem_insert, S'_eq, finset.mem_image],
        right, 
        exact ⟨sum.inl ⟨⟨j, hj0⟩, hj1⟩, hj2, rfl⟩, },
      specialize hℭ3 ⟨j, hj0⟩,
      rw [subtype.coe_mk] at hℭ3,
      rw [hℭ3],
      contrapose! hj3,
      simpa only [set.mem_compl_iff, set.not_not_mem, set.mem_image, exists_eq_right] using hj3, },
    { refine ⟨j, _, _⟩,
      { rw [finset.mem_insert, S'_eq, finset.mem_image],
        right, 
        exact ⟨sum.inr ⟨j, hj1⟩, hj2, rfl⟩, },
      specialize h𝔙2 ⟨j, hj1⟩,
      rw [subtype.coe_mk] at h𝔙2,
      rw h𝔙2,
      exact ⟨_, hj3, rfl⟩, }, },
  { simp only [set.mem_Union],
    refine ⟨i, finset.mem_insert_self _ _, _⟩,
    specialize hℭ3 ⟨i, hi⟩,
    rw [subtype.coe_mk] at hℭ3,
    simpa only [hℭ3, set.mem_compl_iff, set.mem_image, exists_eq_right], },
end }
