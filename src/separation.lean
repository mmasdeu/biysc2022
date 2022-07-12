import basic
open IncidencePlane

noncomputable theory
open_locale classical

variables {Ω : Type} [IncidencePlane Ω]
variables {A B C P Q R : Ω}
variables {ℓ r s t : Line Ω}

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

lemma same_side_trans_of_noncollinear (h : ¬ collinear ({A, C, B} : set Ω)):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  sorry
end

lemma auxiliary_point (ℓ : Line Ω) (h : collinear ({A, B, C} : set Ω)) (hA : A ∉ ℓ) (hB : B ∉ ℓ)
  (hC : C ∉ ℓ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)  :
  ∃ (D E : Ω), D ∈ ℓ ∧ ¬ E ∈ ℓ ∧ same_side ℓ A E ∧ (D * A * E) ∧
  ¬ collinear ({A, B, E} : set Ω) ∧
  ¬ collinear ({E, C, B} : set Ω) ∧
  ¬ collinear ({A, C, E} : set Ω)  :=
begin
  sorry
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
