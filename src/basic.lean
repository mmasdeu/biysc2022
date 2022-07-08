import hilbertaxioms
open IncidencePlane

open_locale classical
noncomputable theory


variables {Ω : Type} [IncidencePlane Ω]
variables {A B C D P Q R S : Ω}
variables {ℓ r s t : Line Ω}

lemma line_unique : A ≠ B → A ∈ ℓ → B ∈ ℓ → ℓ = line_through A B :=
λ ab al bl, incidence ab al bl

lemma distinct_lines_have_at_most_one_common_point
	(hrs: r ≠ s)
	(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :
	A = B :=
begin
    by_contradiction hc,
    apply hrs,
    apply equal_lines_of_contain_two_points hc; assumption,
end

lemma segments_are_symmetric' : pts (A⬝B) ⊆ pts (B⬝A) :=
begin
    intros x hx,
    simp at *,
    rw between_symmetric,
    tauto,
end

lemma segments_are_symmetric : pts (A⬝B) = pts (B⬝A) :=
begin
    apply set.subset.antisymm; exact segments_are_symmetric',
end

@[simp] lemma no_point_between_a_point (A x : Ω) : (A * x * A) ↔ false :=
begin
    split,
    {
        intro h,
        have H := different_of_between h,
        tauto,
    },
    tauto,
end

@[simp] lemma point_is_segment (A : Ω) : pts (A⬝A) = {A} :=
begin
    unfold pts,
    simp,
end

lemma exists_point_on_line (ℓ : Line Ω): ∃ A : Ω, A ∈ ℓ :=
begin
	have I2 := line_contains_two_points ℓ,
	rcases I2 with ⟨ A, B, hAB, hAℓ, hBℓ⟩,
    use A,
    exact line_through_left A B,
end

lemma exists_point_not_on_line (ℓ : Line Ω): ∃ A : Ω, A ∉ ℓ :=
begin
    rcases (existence Ω) with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
    by_cases hA : A ∈ ℓ,
    {
        by_cases hB : B ∈ ℓ,
        {
            use C,
            rw (incidence hAB hA hB),
            assumption,
        },
        use B,
    },
    use A,
end


lemma point_in_line_difference (h : r ≠ s) :
	∃ A, A ∈ r ∧ A ∉ s :=
begin
	have AB : ∃ A B , A ≠ B ∧ r = line_through A B := line_contains_two_points r,
	rcases AB with ⟨ A, B, ⟨ hAB, hAr, hBr⟩⟩,
	have h1 : A ∉ s ∨ B ∉ s,
	{
		by_contradiction hcontra,
        push_neg at hcontra,
		apply hAB,
		apply distinct_lines_have_at_most_one_common_point h,
        {
            apply line_through_left,
        },
        {
            exact hcontra.1,
        },
        {
            apply line_through_right,
        },
        {
            exact hcontra.2,
        }
	},
	cases h1 with h_isA h_isB,
	work_on_goal 1 {use A},
	work_on_goal 2 {use B},
    all_goals {simp, tauto},
end

lemma between_points_share_line (hAr : A ∈ r) (hCr : C ∈ r) : 
	(A * B * C) → B ∈ r :=
begin
	sorry
end

lemma between_points_share_line_v2 (hAr : A ∈ r) (hBr : B ∈ r) : 
	(A * B * C) → C ∈ r :=
begin
	sorry
end

lemma collinear_of_collinear_collinear (hAB : A ≠ B) (hABC : collinear ({A, B, C} : set Ω))
(hABD : collinear ({A, B, D} : set Ω)) :
collinear ({A, C, D} : set Ω) :=
begin
	sorry
end

lemma collinear_subset (S T : set Ω) (hST : S ⊆ T) : collinear T → collinear S :=
begin
	intro h,
	obtain ⟨ℓ, hℓ⟩ := h,
	exact ⟨ℓ, λ P hP, hℓ (hST hP)⟩,
end

lemma collinear_union (S T : set Ω) {P Q : Ω} (h : P ≠ Q) (hS : collinear S) (hT : collinear T)
(hPS : P ∈ S) (hPT : P ∈ T) (hQS : Q ∈ S) (hQT : Q ∈ T) : collinear (S ∪ T) :=
begin
	obtain ⟨u, hu⟩ := hS,
	obtain ⟨v, hv⟩ := hT,
	have huv : u = v,
	{ apply equal_lines_of_contain_two_points h; tauto },
	subst huv,
	use u,
	finish,
end

meta def extfinish : tactic unit := `[ext, finish]

lemma collinear_of_equal {S T : set Ω} : S = T → (collinear S ↔ collinear T) :=
begin
	intro h,
	subst h,
end
