import HTPILib.Chap3
namespace HTPI.Exercises

/- Sections 3.1 and 3.2 -/
-- 1.
theorem Exercise_3_2_1a (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → R) : P → R := by
  assume h3 : P
  show R from h2 (h1 h3)
  done

-- 2.
theorem Exercise_3_2_1b (P Q R : Prop)
    (h1 : ¬R → (P → ¬Q)) : P → (Q → R) := by
  assume h2 : P
  contrapos
  assume h3 : ¬R
  show ¬Q from h1 h3 h2
  done

-- 3.
theorem Exercise_3_2_2a (P Q R : Prop)
    (h1 : P → Q) (h2 : R → ¬Q) : P → ¬R := by
  assume h3 : P
  contrapos at h2
  show ¬R from h2 (h1 h3)
  done

-- 4.
theorem Exercise_3_2_2b (P Q : Prop)
    (h1 : P) : Q → ¬(Q → ¬P) := by
  assume h2 : Q
  contradict h1 with h3
  show ¬P from h3 h2
  done

/- Section 3.3 -/
-- 1.
theorem Exercise_3_3_1
    (U : Type) (P Q : Pred U) (h1 : ∃ (x : U), P x → Q x) :
    (∀ (x : U), P x) → ∃ (x : U), Q x := by
  obtain (a : U) (h2 : P a → Q a) from h1
  assume h3 : ∀ (x : U), P x
  have h4 : P a := h3 a
  have h5 : Q a := h2 h4
  apply Exists.intro a
  show Q a from h5
  done

-- 2.
theorem Exercise_3_3_8 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  define
  fix a : U
  assume h2 : a ∈ A
  define
  apply Exists.intro A
  show A ∈ F ∧ a ∈ A from And.intro h1 h2
  done

-- 3.
theorem Exercise_3_3_9 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  define
  fix a : U
  assume h2 : a ∈ ⋂₀ F
  define at h2
  show a ∈ A := h2 A h1
  done

-- 4.
theorem Exercise_3_3_10 (U : Type) (B : Set U) (F : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → B ⊆ A) : B ⊆ ⋂₀ F := by
  define
  fix a : U
  assume h2 : a ∈ B
  define
  fix A : Set U
  assume h3 : A ∈ F
  have h4 : B ⊆ A := h1 A h3
  define at h4
  show a ∈ A := h4 h2
  done

-- 5.
theorem Exercise_3_3_13 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋂₀ G ⊆ ⋂₀ F := by
  assume h1 : F ⊆ G
  define; define at h1
  fix a : U
  assume h2 : a ∈ ⋂₀ G
  define
  fix A : Set U
  assume h3 : A ∈ F
  define at h2
  show a ∈ A := h2 A (h1 h3)
  done

/- Section 3.4 -/
-- 1.
theorem Exercise_3_4_2 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  fix x : U
  assume h3 : x ∈ A
  show x ∈ B ∩ C := And.intro (h1 h3) (h2 h3)
  done

-- 2.
theorem Exercise_3_4_4 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊈ C) : B ⊈ C := by
  define at h2; quant_neg at h2
  obtain (x : U) (h3) from h2
  conditional at h3
  have h4 := h1 h3.left
  have h5 := And.intro h4 h3.right
  conditional at h5
  define; quant_neg
  apply Exists.intro x h5
  done

-- 3.
theorem Exercise_3_3_16 (U : Type) (B : Set U)
    (F : Set (Set U)) : F ⊆ 𝒫 B → ⋃₀ F ⊆ B := by
  assume h1
  fix x : U
  assume h2
  obtain (A : Set U) (h3 : A ∈ F ∧ x ∈ A) from h2
  have h4 := h1 h3.left
  show x ∈ B := h4 h3.right
  done

-- 4.
theorem Exercise_3_3_17 (U : Type) (F G : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ⊆ B) :
    ⋃₀ F ⊆ ⋂₀ G := by
  fix x : U
  assume h2
  obtain (C : Set U) (h3 : C ∈ F ∧ x ∈ C) from h2
  fix D : Set U
  assume h4
  show x ∈ D := h1 C h3.left D h4 h3.right
  done

-- 5.
theorem Exercise_3_4_7 (U : Type) (A B : Set U) :
    𝒫 (A ∩ B) = 𝒫 A ∩ 𝒫 B := by
  apply Set.ext
  fix C : Set U
  apply Iff.intro

  · -- (→)
    assume h1
    apply And.intro

    · -- C ∈ 𝒫 A
      fix x : U
      assume h2
      show x ∈ A := And.left (h1 h2)
      done

    · -- C ∈ 𝒫 B
      fix x : U
      assume h2
      show x ∈ B := And.right (h1 h2)
      done

    done

  · -- (←)
    assume h1
    fix x : U
    assume h2
    show x ∈ A ∧ x ∈ B := And.intro (h1.left h2) (h1.right h2)
    done

  done

-- 6.
theorem Exercise_3_4_17 (U : Type) (A : Set U) : A = ⋃₀ (𝒫 A) := by
  apply Set.ext
  fix x : U
  apply Iff.intro

  · -- (→)
    assume h1
    apply Exists.intro A
    tauto
    done

  · -- (←)
    assume h1
    define at h1
    obtain (B : Set U) (h2 : B ∈ 𝒫 A ∧ x ∈ B) from h1
    show x ∈ A  := h2.left h2.right
    done

  done

-- 7.
theorem Exercise_3_4_18a (U : Type) (F G : Set (Set U)) :
    ⋃₀ (F ∩ G) ⊆ (⋃₀ F) ∩ (⋃₀ G) := by
  fix x : U
  assume h1
  define at h1
  obtain (A : Set U) (h2 : A ∈ F ∩ G ∧ x ∈ A) from h1
  have h3 := h2.left; have h4 := h2.right
  have h5 := h3.left; have h6 := h3.right
  apply And.intro
  tauto
  tauto
  done

-- 8.
theorem Exercise_3_4_19 (U : Type) (F G : Set (Set U)) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) ↔
      ∀ (A B : Set U), A ∈ F → B ∈ G → A ∩ B ⊆ ⋃₀ (F ∩ G) := by
  apply Iff.intro

  · -- (→)
    assume h1
    fix A : Set U; fix B: Set U
    assume h2
    assume h3
    fix x : U
    assume h4
    define at h1
    have h5 := h4.left; have h6 := h4.right
    have h7 : x ∈ ⋃₀ F := by tauto
    have h8 : x ∈ ⋃₀ G := by tauto
    tauto
    done

  · -- (←)
    assume h1
    fix x : U
    assume h2
    have h3 := h2.left; have h4 := h2.right
    obtain (A : Set U) (h5 : A ∈ F ∧ x ∈ A) from h3
    obtain (B : Set U) (h6 : B ∈ G ∧ x ∈ B) from h4
    have h7 := h1 A B h5.left h6.left
    tauto
    done

  done

/- Section 3.5 -/
-- 1.
theorem Exercise_3_5_2 (U : Type) (A B C : Set U) :
    (A ∪ B) \ C ⊆ A ∪ (B \ C) := sorry

-- 2.
theorem Exercise_3_5_5 (U : Type) (A B C : Set U)
    (h1 : A ∩ C ⊆ B ∩ C) (h2 : A ∪ C ⊆ B ∪ C) : A ⊆ B := sorry

-- 3.
theorem Exercise_3_5_7 (U : Type) (A B C : Set U) :
    A ∪ C ⊆ B ∪ C ↔ A \ C ⊆ B \ C := sorry

-- 4.
theorem Exercise_3_5_8 (U : Type) (A B : Set U) :
    𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) := sorry

-- 5.
theorem Exercise_3_5_17b (U : Type) (F : Set (Set U)) (B : Set U) :
    B ∪ (⋂₀ F) = {x : U | ∀ (A : Set U), A ∈ F → x ∈ B ∪ A} := sorry

-- 6.
theorem Exercise_3_5_18 (U : Type) (F G H : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ∪ B ∈ H) :
    ⋂₀ H ⊆ (⋂₀ F) ∪ (⋂₀ G) := sorry

-- 7.
theorem Exercise_3_5_24a (U : Type) (A B C : Set U) :
    (A ∪ B) ∆ C ⊆ (A ∆ C) ∪ (B ∆ C) := sorry

/- Section 3.6 -/
-- 1.
theorem Exercise_3_4_15 (U : Type) (B : Set U) (F : Set (Set U)) :
    ⋃₀ {X : Set U | ∃ (A : Set U), A ∈ F ∧ X = A \ B}
      ⊆ ⋃₀ (F \ 𝒫 B) := sorry

-- 2.
theorem Exercise_3_5_9 (U : Type) (A B : Set U)
    (h1 : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B) : A ⊆ B ∨ B ⊆ A := by
  --Hint:  Start like this:
  have h2 : A ∪ B ∈ 𝒫 (A ∪ B) := sorry
  sorry
  done

-- 3.
theorem Exercise_3_6_6b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∪ B = A := sorry

-- 4.
theorem Exercise_3_6_7b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∩ B = A := sorry

-- 5.
theorem Exercise_3_6_8a (U : Type) : ∀ (A : Set U),
    ∃! (B : Set U), ∀ (C : Set U), C \ A = C ∩ B := sorry

-- 6.
theorem Exercise_3_6_10 (U : Type) (A : Set U)
    (h1 : ∀ (F : Set (Set U)), ⋃₀ F = A → A ∈ F) :
    ∃! (x : U), x ∈ A := by
  --Hint:  Start like this:
  set F0 : Set (Set U) := {X : Set U | X ⊆ A ∧ ∃! (x : U), x ∈ X}
  --Now F0 is in the tactic state, with the definition above
  have h2 : ⋃₀ F0 = A := sorry
  sorry
  done

/- Section 3.7 -/
-- 1.
theorem Exercise_3_3_18a (a b c : Int)
    (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ (b + c) := sorry

-- 2.
theorem Exercise_3_4_6 (U : Type) (A B C : Set U) :
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  apply Set.ext
  fix x : U
  show x ∈ A \ (B ∩ C) ↔ x ∈ A \ B ∪ A \ C from
    calc x ∈ A \ (B ∩ C)
      _ ↔ x ∈ A ∧ ¬(x ∈ B ∧ x ∈ C) := sorry
      _ ↔ x ∈ A ∧ (x ∉ B ∨ x ∉ C) := sorry
      _ ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ A ∧ x ∉ C) := sorry
      _ ↔ x ∈ (A \ B) ∪ (A \ C) := sorry
  done

-- 3.
theorem Exercise_3_4_10 (x y : Int)
    (h1 : odd x) (h2 : odd y) : even (x - y) := sorry

-- 4.
theorem Exercise_3_4_27a :
    ∀ (n : Int), 15 ∣ n ↔ 3 ∣ n ∧ 5 ∣ n := sorry

-- 5.
theorem Like_Exercise_3_7_5 (U : Type) (F : Set (Set U))
    (h1 : 𝒫 (⋃₀ F) ⊆ ⋃₀ {𝒫 A | A ∈ F}) :
    ∃ (A : Set U), A ∈ F ∧ ∀ (B : Set U), B ∈ F → B ⊆ A := sorry
