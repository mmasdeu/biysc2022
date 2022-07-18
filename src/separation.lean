import basic
open IncidencePlane

noncomputable theory
open_locale classical

variables {Ω : Type} [IncidencePlane Ω]
variables {A B C P Q R : Ω}
variables {ℓ r s t : Line Ω}

lemma distinct_lines_of_point_in_difference
(A : Ω) (h1 : A ∈ r) (h2 : A ∉ s) : r ≠ s := by finish

lemma not_between_of_between : (A * B * C) → ¬ B * A * C :=
begin
  intro h,
  have h' := between_of_collinear (collinear_of_between h),
  unfold xor3 at h',
  tauto,
end

lemma distinct_lines_of_points_in_difference (A : Ω) (h1 : A ∈ r) (h1 : A ∉ s) : r ≠ s:= by finish

lemma same_side_symmetric' : same_side ℓ A B → same_side ℓ B A :=
begin
  unfold same_side,
  intro h,
  rw segments_are_symmetric,
  exact h, 
end

lemma same_side_symmetric : same_side ℓ A B ↔ same_side ℓ B A :=
begin
  split;
  exact same_side_symmetric',
end

lemma different_side_symmetric : ¬ same_side ℓ A B ↔ ¬ same_side ℓ B A :=
begin
  exact iff.not same_side_symmetric,
end

lemma collinear_iff_on_line_through (h : A ≠ B) : collinear ({A, B, C} : set Ω) ↔ C ∈ line_through A B :=
begin
split,
{
  intro h1,
  rcases h1 with ⟨ℓ, hℓ⟩,
  simp at hℓ,
  rw ←(incidence h hℓ.1 hℓ.2.1),
  exact hℓ.2.2,
},
{
  intro h1,
  use line_through A B,
  simp [h1],
}
end

lemma not_in_line_of_same_side_left (h : same_side ℓ A B) : A ∉ ℓ :=
begin
  by_contradiction h1,
  unfold same_side at h,
  simp at h,
  have h2 : A ∈ pts(A⬝B) ∩ ℓ,
  {
    split;
    simp [h1],
  },
  finish,
end

lemma not_in_line_of_same_side_right (h : same_side ℓ A B) : B ∉ ℓ :=
begin
  by_contradiction h1,
  unfold same_side at h,
  simp at h,
  have h2 : B ∈ pts(A⬝B) ∩ ℓ,
  {
    split;
    simp [h1],
  },
  finish,
end

lemma ne_of_not_share_point  (hPr : P ∈ r)(hPs : P ∉ s): r ≠ s:=
begin
intro h,
apply hPs,
rw ← h,
exact hPr,
end

lemma line_through_from_and (P Q : Ω) (ℓ : Line Ω) (h1 : P ≠ Q)
(h2 : P ∈ ℓ ∧ Q ∈ ℓ) : ℓ = line_through P Q :=
begin
cases h2 with hP hQ,
exact incidence h1 hP hQ,
end

lemma collinear_of_between'' {A B C : Ω} : (A * B * C) → collinear ({A, B, C} : set Ω) :=
begin
intro h,
cases collinear_of_between h with r hr,
use r,
simp,
exact hr,
end

lemma point_in_line_not_point {P Q: Ω} {r : Line Ω} (hP : P ∈ r) (hQ : Q ∉ r): P ≠ Q :=
begin
  intro h1,
  apply hQ,
  rw ← h1,
  exact hP,
end

lemma exists_point_not_in_line (ℓ : Line Ω) : ∃ (P : Ω), P ∉ ℓ :=
begin
rcases (existence Ω) with ⟨A : Ω, B, C, ⟨h1, h2, h3, h4⟩⟩,
by_cases h: line_through A B = ℓ,
{ use C,
  rw ← h,
  exact h4 },
{ by_cases a: A ∈ ℓ, { use B,
    intro p,
    apply h,
    rw incidence h1 a p },
  { use A }, },
end

lemma same_side_trans_of_noncollinear (hCol : ¬ collinear ({A, C, B} : set Ω)):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  have hAC : A ≠ C,
  {
    intro h,
    apply hCol,
    rw h,
    use line_through B C,
    simp, 
  },
-- Suppose l meets A·C (proving by contradiction)
-- By Pasch l meets A·B or l meets B·C
    -- If l meeets A·B then A, B on different sides
    -- IF l meets B·C then B, C on different sides 
  intros p q,
  by_contradiction,
  unfold same_side at h,
  have h' : ∃ D , D ∈ pts (A⬝C) ∧ D ∈ ℓ,
  {
    simp,
    by_contra h',
    push_neg at h',
    apply h,
    ext,
    split,
    {
      intro h'',
      simp,
      specialize h' x,
      have h''' : A*x*C,
      {
        finish,
      },
      apply h',
      {
        tauto,
      },
      {
        finish,
      },  
    },
    {
      tauto,
    },
},

cases h' with P r,
have c : A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ,
{
  repeat {split},
  apply not_in_line_of_same_side_left p,
  apply not_in_line_of_same_side_right p,
  apply not_in_line_of_same_side_right q,
},
simp at r,
have x : A*P*C,
{
  have hPA : P ≠ A,
  {
    intro hc,
    apply c.1,
    rw hc at r,
    exact r.2,
  },
  have hPA : P ≠ C,
  {
    intro hcon,
    apply c.2.2,
    rw hcon at r,
    exact r.2,
  },
  tauto,
},
have a1 : B ∉ line_through A C,
{
  rw ← collinear_iff_on_line_through hAC,
  exact hCol,
},

have fact := pasch a1 c.1 c.2.2 c.2.1 r.2 x,
cases fact,
{
unfold same_side at p,
cases fact.1 with E,
simp [set.eq_empty_iff_forall_not_mem] at p,
replace p := p.2.2 E h_1.2,
apply p,
exact h_1.1,
},
unfold same_side at q,
cases fact.1 with F,
simp [set.eq_empty_iff_forall_not_mem] at q,
rw between_symmetric at h_1,
replace q := q.2.2 F h_1.2,
apply q,
exact h_1.1,
end

lemma auxiliary_point (ℓ : Line Ω) (h : collinear ({A, B, C} : set Ω)) (hA : A ∉ ℓ) (hB : B ∉ ℓ)
  (hC : C ∉ ℓ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)  :
  ∃ (D E : Ω), D ∈ ℓ ∧ ¬ E ∈ ℓ ∧ same_side ℓ A E ∧ (D * A * E) ∧
  ¬ collinear ({A, B, E} : set Ω) ∧
  ¬ collinear ({E, C, B} : set Ω) ∧
  ¬ collinear ({A, C, E} : set Ω)  :=
begin
    -- define what a b c line is, m
    set m := line_through A B with hm,
    
    have hAM: A ∈ m,
    exact line_through_left A B,

    have hBM: B ∈ m,
    exact line_through_right A B,

    have hCM:= (collinear_iff_on_line_through hAB).1 h,

    --l is not m
    have lm := ne_of_not_share_point hAM hA,
    --there is point in l, not in m, D
    have hD := point_in_line_difference (ne.symm lm),
    rcases hD with ⟨D, ⟨hD1, hD2⟩⟩,

    have hDA:= point_in_line_not_point hD1 hA,
    rcases (point_on_ray hDA) with ⟨E, hE⟩,
    use D,
    use E,
    split,
    exact hD1,
    have hDnotE := different_of_between hE,
    repeat {split},
    {
      by_contradiction hEL,
      have hDAE := incidence hDnotE.2.1 hD1 hEL,
      have hDAE2 := collinear_of_between hE,
      cases hDAE2 with n,
      have hhh := incidence hDnotE.2.1 hDAE2_h.1 hDAE2_h.2.2,
      rw ← hhh at hDAE,
      rw ← hDAE at hDAE2_h,
      exact hA hDAE2_h.2.1,
    },
    {
      unfold same_side,
      simp [set.eq_empty_iff_forall_not_mem],
      repeat {split},
      {
        exact hA,
      },
      by_contradiction hEL,
      {
        have hDAE := incidence hDnotE.2.1 hD1 hEL,
        have hDAE2 := collinear_of_between hE,
        cases hDAE2 with n,
        have hhh := incidence hDnotE.2.1 hDAE2_h.1 hDAE2_h.2.2,
        rw ← hhh at hDAE,
        rw ← hDAE at hDAE2_h,
        exact hA hDAE2_h.2.1,
      },
      {
        intros P hP hPL,
        rcases (collinear_of_between hP) with ⟨r, hAr, hPr, hEr⟩,
        rcases (collinear_of_between hE) with ⟨s, hDs, hAs, hEs⟩,
        have hAE : A ≠ E := (different_of_between hE).2.2,
        have hrs := equal_lines_of_contain_two_points hAE hAr hAs hEr hEs,
        subst hrs,
        clear hAs hEs,
        have hPD : P ≠ D,
        {
          intro hc,
          subst hc,
          exact not_between_of_between hE hP,
        },
        have hℓr := equal_lines_of_contain_two_points hPD hPL hPr hD1 hDs,
        rw ←hℓr at hAr,
        contradiction,
      },
    }, 
    {
      exact hE,
    },
    {
      cases hDnotE with hDnotE1 hDnotE2,
      cases hDnotE2 with hDnotE2 hDnotE3,
      intro o1,
      have j1 : line_through A B = line_through A C,
      {
        exact equal_lines_of_contain_two_points hAC (line_through_left A B) (line_through_left A C) hCM (line_through_right A C),
      },
      have oo4 := (collinear_iff_on_line_through hAB).1 o1,
      have j2 : line_through E A = line_through A B,
      {
        exact equal_lines_of_contain_two_points hDnotE3 (line_through_right E A) (line_through_left A B) (line_through_left E A) oo4,
      },
      rw ← hm at oo4,
      have j3 := collinear_of_between hE,
      cases j3 with j31 j32,
      cases j32 with j32 j33,
      cases j33 with j33 j34,
      have j4 : j31 = m,
      {
        have y1:= equal_lines_of_contain_two_points hDnotE3 j33 (line_through_right E A) j34 (line_through_left E A),
        rw j2 at y1,
        rw ← hm at y1,
        exact y1,
      },
      rw j4 at j32,
      apply hD2,
      exact j32,
    },
    {
      cases hDnotE with hDnotE1 hDnotE2,
      cases hDnotE2 with hDnotE2 hDnotE3,
      intro o1,
      set r := line_through D E with hDEs,
      
      have j1 : line_through A B = line_through A C,
      {
        exact equal_lines_of_contain_two_points hAC (line_through_left A B) (line_through_left A C) hCM (line_through_right A C),
      },
      have g1 : E ≠ C,
      {
        intro g2,
        rw ← hm at hCM,
        have k1 := collinear_of_between hE,
        cases k1 with k1 k2,
        cases k2 with k2 k3,
        cases k3 with k3 k4,
        have km : k1 = m,
        {
          rw g2 at k4,
          exact equal_lines_of_contain_two_points hAC k3 hAM k4 hCM,
        },
        rw km at k2,
        apply hD2,
        exact k2,
      },
      have oo4 := (collinear_iff_on_line_through g1).1 o1,
      have j2 : line_through E C = line_through B C,
      {
        exact equal_lines_of_contain_two_points hBC oo4 (line_through_left B C) (line_through_right E C) (line_through_right B C),
      },
      rw ← hm at hCM,
      have p3 : line_through B C = m,
      {
        exact equal_lines_of_contain_two_points hBC (line_through_left B C) hBM (line_through_right B C) hCM,
      },
      rw j1 at hm,
      rw j2 at oo4,
      have j3 := collinear_of_between hE,
      cases j3 with j31 j32,
      cases j32 with j32 j33,
      cases j33 with j33 j34,
      have hEm : E ∈ m,
      {
        rw ← p3,
        rw ←  collinear_iff_on_line_through hBC,
        rw collinear_of_equal ({B, C, E} : set Ω) ({E, C, B} : set Ω),
        exact o1,
      },
      have j4 : j31 = m,
      {
        have y1:= equal_lines_of_contain_two_points hDnotE3 j33 (line_through_right E A) j34 (line_through_left E A),
        rw ← j2 at oo4,
        rw y1,
        apply equal_lines_of_contain_two_points hDnotE3,
        {
          simp,
        },
        {
          exact hAM,
        },
        {
          simp,
        },
        {
          exact hEm,
        }, 
      },
      rw j4 at j32,
      apply hD2,
      exact j32,
    },
    {
      cases hDnotE with hDnotE1 hDnotE2,
      cases hDnotE2 with hDnotE2 hDnotE3,
      intro o1,
      have j1 : line_through A B = line_through A C,
      {
        exact equal_lines_of_contain_two_points hAC (line_through_left A B) (line_through_left A C) hCM (line_through_right A C),
      },
      have oo4 := (collinear_iff_on_line_through hAC).1 o1,
      have j2 : line_through E A = line_through A C,
      {
        exact equal_lines_of_contain_two_points hDnotE3 (line_through_right E A) (line_through_left A C) (line_through_left E A) oo4,
      },
      rw j1 at hm,
      rw ← hm at oo4,

      have j3 := collinear_of_between hE,
      cases j3 with j31 j32,
      cases j32 with j32 j33,
      cases j33 with j33 j34,

      have j4 : j31 = m,
      {
        have y1:= equal_lines_of_contain_two_points hDnotE3 j33 (line_through_right E A) j34 (line_through_left E A),
        rw j2 at y1,
        rw ← hm at y1,
        exact y1,
      },
      rw j4 at j32,
      apply hD2,
      exact j32,

    },
end


lemma same_side_trans_of_collinear (h : collinear ({A, C, B} : set Ω)):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  intros h1 h2,
  -- Create hypotheses to satisfy parameters of lemma auxiliary_point
  have hA : A ∉ ℓ,
  {
    exact not_in_line_of_same_side_left h1,
  },
  have hB : B ∉ ℓ,
  {
    exact not_in_line_of_same_side_left h2,
  },
  have hC : C ∉ ℓ,
  {
    exact not_in_line_of_same_side_right h2,
  },
  by_cases hAC: A = C,
  {
    rw hAC,
    unfold same_side,
    simp,
    exact hC,
  },
  by_cases hAB: A = B,
  {
    rw hAB,
    exact h2,
  },
  by_cases hCB: C = B,
  {
    rw hCB,
    exact h1,
  },
  -- With lemma auxiliary_point: ∃ E , same_side ℓ A E
  -- ACE , EBC , ABE non collinear
  have h3 := auxiliary_point ℓ h hA hC hB hAC hAB hCB,
  rcases h3 with ⟨D, E, ⟨hDL, hEL, hAE, hDAE, hACE, hEBC, hABE⟩⟩, 
  -- Rewrite hyptoheses to satisfy parameters of lemma same_side_trans_of_noncollinear
  rw collinear_of_equal ({A, B, E} :set Ω)({E, B, A} :set Ω) at hABE,
  rename hABE hEBA,
  have hEA : same_side ℓ E A := same_side_symmetric.mp hAE,
  -- With lemma same_side_trans_of_noncollinear: same_side ℓ E B
  have hEB := same_side_trans_of_noncollinear hEBA hEA h1,
  -- Rewrite hyptoheses to satisfy parameters of lemma same_side_trans_of_noncollinear
  rw collinear_of_equal ({E, B, C} :set Ω)({E, C, B} :set Ω) at hEBC,
  rename hEBC hECB,
  -- With lemma same_side_trans_of_noncollinear: same_side ℓ E C
  have hEC := same_side_trans_of_noncollinear hECB hEB h2,
  -- With lemma same_side_trans_of_noncollinear, same_side ℓ A C
  exact same_side_trans_of_noncollinear hACE hAE hEC, 
end

lemma same_side_trans_general : same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  by_cases h : collinear ({A, C, B} : set Ω),
  {
    apply same_side_trans_of_collinear h,
  },
  {
    apply same_side_trans_of_noncollinear h,
  }  
end

lemma at_least_two_classes (ℓ : Line Ω):
      ∃ A B : Ω, (A ∉ ℓ) ∧ (B ∉ ℓ) ∧ (¬ same_side ℓ A B) :=
begin
  cases (exists_point_on_line ℓ) with Q hQ,
  cases (exists_point_not_on_line ℓ) with P hP,
  have hPQ:P ≠ Q,
  {
    intro hQQQQ,
    apply hP,
    rw hQQQQ,
    exact hQ,
  },
  cases (point_on_ray hPQ) with R hPQR,
  have hRRQQ: Q ≠ R,
    {
    have fact:=different_of_between hPQR,
    exact fact.2.2,
    },
  have hR: R ∉ ℓ,
  {
    have hPP: P ∈ line_through Q R,
    {
      rw between_symmetric at hPQR,
      have htmp : line_through Q R = line_through R Q,
      {
        apply equal_lines_of_contain_two_points hRRQQ;
        simp,
      },
      rw htmp,
      exact between_points_share_line_v2 (line_through_left R Q) (line_through_right R Q) hPQR,
    },
    intro hr,
    apply hP,
    rw incidence hRRQQ hQ hr,
    exact hPP,
  },
  use P,
  use R,
  split,
  exact hP,
  split,
  exact hR,
  have hhQ: Q ∈ P⬝R,
  {
    simp,
    right,
    right,
    exact hPQR,
  }, 
  intro h,
  unfold same_side at h,
  have hQQ:Q ∈ pts (P⬝R) ∩ ℓ,
  {
    split,
    exact hhQ,
    exact hQ,
  },
  exact set.eq_empty_iff_forall_not_mem.mp h Q hQQ,
end

lemma not_on_line_iff_not_collinear  (h2 : A≠ B)(h1: ¬ collinear({A,B,C} : set Ω ))
:  C ∉ line_through A B:=
begin
  exact ( iff.not (collinear_iff_on_line_through h2)).mp h1,
end 

lemma at_most_two_classes_of_noncollinear (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
    (h : ¬ collinear ({A, B, C} : set Ω)) : same_side ℓ B C :=
begin
  --Step 1: First, prove that A is not equal to B and A is not equal to C
  have HAB: A≠B,{
  unfold same_side at hAB,
    intro H,
    rw H at hAB,
    simp at hAB,
    apply hB,
    exact hAB,
  },
  have HAC: A≠C,{
    unfold same_side at hAC,
    intro H,
    rw H at hAC,
    simp at hAC,
    apply hC,
    exact hAC,
  },
--Step 1: Done
--Step 2: Prove that there exists a point D that is both on line ℓ and on line AB such that A*D*B
  have HADB: ∃ (D : Ω), D ∈ ℓ ∧ D ∈ line_through A B ∧ A*D*B,
  {
    unfold same_side at hAB,
    simp at hAB,
    by_contra hc,
    apply hAB,
    push_neg at hc,
    ext,
    split,
    {
      intro H,
      exfalso,
      have h1: x ∈ line_through A B,
      {
        cases H with H hxl,
        simp  at H,
        cases H,
          rw H,
          exact line_through_left A B,
        cases H,
          rw H,
          exact line_through_right A B,
        rw ← collinear_iff_on_line_through HAB,
        have H1:= collinear_of_between H,
        cases H1 with r hr,
        use r,
        simp,
        tauto,
      },
      specialize hc x H.2,
      finish,
    },
    tauto,
    },
    -- D POINT CREATED
  -- Repeat the same process for another point E that should lie on line ℓ and line AC
  have HAEC: ∃ (E : Ω), E ∈ ℓ ∧ E ∈ line_through A C ∧ A*E*C,
  {
    unfold same_side at hAC,
    simp at hAC,
    by_contra hc,
    apply hAC,
    push_neg at hc,
    ext,
    split,
    {
      intro H,
      exfalso,
      have h1: x ∈ line_through A C,
      {
        cases H with H hxl,
        simp  at H,
        cases H,
          rw H,
          exact line_through_left A C,
        cases H,
          rw H,
          exact line_through_right A C,
        rw ← collinear_iff_on_line_through HAC,
        have H1:= collinear_of_between H,
        cases H1 with r hr,
        use r,
        simp,
        tauto,
      },
      specialize hc x H.2,
      finish,
    },
    tauto,
    },

  --BOTH E AND D POINTS HAVE BEEN PROVED

  -- WE NEDE TO SHOW THAT C IS NOT IN BETWEEN A and B
  -- USE LEMMA (not_on_line_iff_not_collinear) STATING THAT IF POINTS A B C ARE NOT COLLINEAR AND A≠B,  THEY CANNOT BE IN THE SAME LINE
  cases HADB with D r,
  {
    cases r with l1 r1,
    {
      cases r1 with l2 r2,
      {
        --PASCH AXIOM
        --MAKE PASCH A HYPOTHESIS AND THEN SOLVE THE TWO CASES
        have w := pasch (not_on_line_iff_not_collinear HAB h) hA hB hC l1 r2,
        unfold same_side,
        cases w,
        {
        --FIRST PASCH CASE 
          cases w,
          {
              simp,
              ext,
              split,
              {
                intro H,
                exfalso,
                have x1: x∈ line_through B C,
                {
                    cases H with H hxl,
                    simp at H,
                    cases H,
                      rw H,
                      exact line_through_left B C,
                    cases H,
                      rw H,
                      exact line_through_right B C,
                    rw ← collinear_iff_on_line_through hBneqC,
                    have H1:= collinear_of_between H,
                    cases H1 with r0 hr,
                    use r0,
                    simp,
                    tauto,
                },
                simp at H,
                cases H,
                finish,
              },
              {
                intro H,
                exfalso,
                
                simp at H,
                cases H,
              },
          }, 
        },
        {
          --SECOND PASCH CASE
          simp,
              ext,
              split,
              {
                intro H,
                exfalso,
                have x1: x∈ line_through B C,
                {
                    cases H with H hxl,
                    simp at H,
                    cases H,
                      rw H,
                      exact line_through_left B C,
                    cases H,
                      rw H,
                      exact line_through_right B C,
                    rw ← collinear_iff_on_line_through hBneqC,
                    have H1:= collinear_of_between H,
                    cases H1 with r0 hr,
                    use r0,
                    simp,
                    tauto,
                },
                simp at H,
                cases H,
                finish,
                
                
              },
              {
                intro H,
                exfalso,
                
                simp at H,
                cases H,
              },
          },
        },
      },
    },
  -- BOTH PASCH CASES SOLVED AND PROOF COMPLETED
end


lemma at_most_two_classes_of_collinear (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
    (h : collinear ({A, B, C} : set Ω)) : same_side ℓ B C :=
begin
  -- Create and prove hypotheses to satisfy parameters of lemma auxiliary_point
  by_cases hBneqA: B = A,
  {
    exfalso,
    apply hAB,
    rw hBneqA,
    unfold same_side,
    simp,
    exact hA,
  },
  by_cases hCneqA: C = A,
  {
    exfalso,
    apply hAC,
    rw hCneqA,
    unfold same_side,
    simp,
    exact hA,
  },
  rw collinear_of_equal ({A, B, C} :set Ω)({B, C, A} :set Ω) at h,
  -- Use lemma auxiliary_point
  -- ∃ E , same_side ℓ B E , BCE,EAC,BAE non collinear
  have h1 := auxiliary_point ℓ h hB hC hA hBneqC hBneqA hCneqA,
  rcases h1 with ⟨D, E, ⟨hD, hE, hBE, hDBE, hBCE, hEAC, hBAE⟩⟩,
  -- Create and prove hyptoheses to satisfy parameters of lemma same_side_trans_of_noncollinear
  -- Use lemma same_side_trans_of_noncollinear to prove that ¬ same_side ℓ E A by contradiction
  have hEA : ¬ same_side ℓ E A,
  {
    by_contradiction hEA,
    rw collinear_of_equal ({B, A, E} :set Ω)({A, B, E} :set Ω) at hBAE,
    rename hBAE hABE,
    have hAE : same_side ℓ A E := same_side_symmetric.mp hEA,
    have hEB : same_side ℓ E B := same_side_symmetric.mp hBE,
    have hAB := same_side_trans_of_noncollinear hABE hAE hEB,
    finish,
  },
  have hAE : ¬ same_side ℓ A E := different_side_symmetric.mp hEA,
  have hEneqC: E ≠ C,
  {
    intro hEeqC,
    rw hEeqC at hBCE,
    apply hBCE,
    use line_through B C,
    simp,
  },
  rw collinear_of_equal ({E, A, C} :set Ω)({A, E, C} :set Ω) at hEAC,
  rename hEAC hAEC,
  -- Use lemma at_most_two_classes_of_noncollinear to prove that same_side ℓ E C
  have hEC := at_most_two_classes_of_noncollinear hA hE hC hEneqC hAE hAC hAEC,
  -- Use lemma same_side_trans_of_noncollinear to prove that same_side ℓ B C
  exact same_side_trans_of_noncollinear hBCE hBE hEC,  
end

lemma at_most_two_classes_general (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C): same_side ℓ B C :=
begin
  by_cases h : collinear ({A, B, C} : set Ω),
  {
    apply at_most_two_classes_of_collinear hA hB hC hBneqC hAB hAC h,
  },
  {
    apply at_most_two_classes_of_noncollinear hA hB hC hBneqC hAB hAC h,
  }
end
