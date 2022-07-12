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

lemma at_most_two_classes_of_noncollinear (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
    (h : ¬ collinear ({A, B, C} : set Ω)) : same_side ℓ B C :=
begin
  sorry
end

lemma at_most_two_classes_of_collinear (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
    (h : collinear ({A, B, C} : set Ω)) : same_side ℓ B C :=
begin
  sorry
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
