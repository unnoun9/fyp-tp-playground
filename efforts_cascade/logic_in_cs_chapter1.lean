-- Exercise 1.2
-- Question 1 Prove the validity of the following sequents:
-- vdash for ⊢

-- variable (p q r s t : Prop)
variable {p q r s t : Prop}
-- Exercise 1.2(a): Prove (p ∧ q) ∧ r, s ∧ t ⊢ q ∧ s

-- method 1: using assumption names
theorem exercise_1_2_a (h1 : (p ∧ q) ∧ r) (h2 : s ∧ t) : q ∧ s := by
  constructor
  -- Prove q
  · have pq : p ∧ q := h1.left  -- Extract (p ∧ q) from ((p ∧ q) ∧ r)
    exact pq.right              -- Extract q from (p ∧ q)
  -- Prove s
  · exact h2.left              -- Extract s from (s ∧ t)

-- method 2: direct approach
theorem exercise_1_2_a_direct (h1 : (p ∧ q) ∧ r) (h2 : s ∧ t) : q ∧ s := by
  constructor
  · exact h1.left.right  -- q from ((p ∧ q) ∧ r)
  · exact h2.left        -- s from (s ∧ t)
-- method 3: One-liner using anonymous constructor
theorem exercise_1_2_a_short (h1 : (p ∧ q) ∧ r) (h2 : s ∧ t) : q ∧ s :=
  ⟨h1.left.right, h2.left⟩
-- (b) p ∧ q ⊢  q ∧ p
theorem exercise_1_2_b (h : (p ∧ q)) : q ∧ p := by
  constructor
  {exact h.right}
  {exact h.left}
theorem exercise_1_2_b_short (h: (p ∧ q)) : q ∧ p :=
  ⟨h.right, h.left⟩
-- c)* (p ∧ q) ∧ r ⊢ p ∧ (q ∧ r)
theorem exercise_1_2_c (h1 : (p ∧ q) ∧ r) : p ∧ (q ∧ r) := by

  constructor
  {exact h1.left.left}  -- proves p
  {constructor
   exact h1.left.right
   exact h1.right}

theorem exercise_1_2_c_short (h1 : (p ∧ q) ∧ r) : p ∧ (q ∧ r) := by
  constructor
  {exact h1.left.left}
  {exact ⟨h1.left.right, h1.right⟩}

-- (d) p → (p → q), p ⊢  q

theorem exercise_1_2_d (h1 : p → (p → q)) (h2 : p) : q := by
  -- modus ponens

  have h3 : p → q := h1 h2  -- applying h1 to h2 to get (p → q)
  exact h3 h2

theorem exercise_1_2_d_1 (h1 : p → (p → q)) (h2 : p) : q := by

   apply h1
   exact h2
   exact h2

theorem exercise_1_2_d_2 (h1 : p → (p → q)) (h2 : p) : q := by
  exact h1 h2 h2

-- * (e) q → (p → r), ¬r, q ⊢ ¬p

theorem exercise_1_2_e_1 (h1 : q → (p → r)) (h2 : ¬ r) (h3 : q) : ¬p := by

  have h4 : p → r := h1 h3
  -- false_or_by_contra
  intro h
  have h5 : r := h4 h
  exact h2 h5


theorem modus_tollens (h1 : p → q) (h2 : ¬ q) : ¬p := by

  intro h
  have h3 : q := h1 h
  exact h2 h3


theorem ex_1_2_e_1 (h1 : q → (p → r)) (h2 : ¬ r) (h3 : q) : ¬p := by

  have h4 : p → r := h1 h3
  have h5 : ¬p := modus_tollens h4 h2
  exact h5


theorem exercise_1_2_e_2 (h1 : q → (p → r)) (h2 : ¬ r) (h3 : q) : ¬p := by

  have h4 : p → r := h1 h3
  intro h
  apply h2
  exact h4 h

-- * (f) ⊢ (p ∧ q) → p

theorem exercise_1_2_f : (p ∧ q) → p := by
  intro h
  exact h.left


-- (g) p ⊢ q → (p ∧ q)

theorem exercise_1_2_g (h1 : p) : q → (p ∧ q) := by

   intro h2
   constructor
   exact h1
   exact h2
-- (h)* p ⊢  (p → q) → q

theorem exercise_1_2_h (h1 : p) : (p → q) → q := by
  intro h2
  apply h2
  exact h1
-- (i)* (p → r) ∧ (q → r) ⊢ p ∧ q → r

theorem exercise_1_2_i (h1 : (p → r) ∧ (q → r)) : p ∧ q → r := by

   intro h2
   have hp : p := h2.left -- p from ( p ∧ q)
   have pr : p → r := h1.left -- (p → r) from h1
   exact pr hp -- applying (p → r) to p to get r


-- * (j) q → r ⊢ (p → q) → (p → r)

theorem exercise_1_2_j (h1 : (q → r)) : (p → q) → (p → r) := by

  intro h2 -- h2 : p → q
  intro h3 -- h3 : p (we need to prove p → r, so assume p)
  have hq : q := h2 h3 -- applying h2 to h3 to get q
  exact h1 hq -- applying h1 to q to get r


-- (k) p → (q → r), p → q ⊢ p → r

theorem exercise_1_2_k (h1 : p → (q → r)) (h2 : p → q) : p → r := by

  intro h3  -- assuming p
  have h4 : q → r := h1 h3 -- taking q → r by applying h1 to h3
  have h5 : q := h2 h3 -- taking q by applying h2 to h3
  exact h4 h5 -- finally applying h4 to h5 to get r


-- (l)* p → q, r → s ⊢  p ∨ r → q ∨ s

theorem exercise_1_2_l (h1 : (p → q)) (h2 : (r → s)) : p ∨ r → q ∨ s :=by

  intro h3 -- p ∨ r
  rcases h3 with hp | hr -- either p is true or r is true
  {left; exact h1 hp} -- if p is true, then by h1 : p → q, we get q, so q ∨ s is true
  {right; exact h2 hr} -- if r is true, then by h2 : r → s we get s, so q ∨ is true


-- (m) p ∨ q ⊢  r → (p ∨ q) ∧ r

theorem exercise_1_2_m (h1 : p ∨ q) : r → (p ∨ q) ∧ r := by

  intro h2
  constructor -- splitting the goal into 2 parts; subgoal 1 is (p ∨ q) and subgoal 2 is r
  {exact h1}
  {exact h2}


-- *(n) (p ∨ (q → p)) ∧ q ⊢ p

theorem exercise_1_2_n (h1 : (p ∨ (q → p)) ∧ q ) : p := by

  have h2 : p ∨ (q → p) := h1.left -- we get p ∨ (q → p)
  have h3 : q := h1.right -- we get q
  rcases h2 with hp | hr -- p is true or (q → p) is true
  {exact hp} -- p is true
  {exact hr h3} -- q → p is true then by modus ponens we get p
  -- either way , we getting p, a tautology


-- (o)* p → q, r → s ⊢  p ∧ r → q ∧ s

theorem exercise_1_2_o (h1 : p → q) (h2 : r → s) : p ∧ r → q ∧ s := by


 intro h3
 constructor
 exact h1 h3.left  -- applying p → q to p to get q
 exact h2 h3.right -- applying r → s to r to get s


-- (p) p → q ⊢ ((p ∧ q) → p) ∧ (p → (p ∧ q))

theorem exercise_1_2_p (h1 : p → q) : ((p ∧ q) → p) ∧ (p → (p ∧ q)) := by

  constructor
  -- first subgoal (p ∧ q) → p
  intro h2
  exact h2.left

  -- second subgoal p → (p ∧ q)
  intro h3
  constructor
  exact h3
  exact h1 h3


-- (q) ⊢ q → (p → (p → (q → p)))

theorem exercise_1_2_q : q → (p → (p → (q → p))) := by

intro h1 -- p
intro h2  -- q
intro h3 -- p
intro h4 -- q

exact h2 -- to prove p, we can have it from h2


-- (r)* p → q ∧ r ⊢ (p → q) ∧ (p → r)

theorem exercise_1_2_r (h1 : p → (q ∧ r)) : (p → q) ∧ (p → r) := by

  constructor
  intro h2
  have h3 : q ∧ r := h1 h2
  exact h3.left

  intro h4
  have h5 : q ∧ r := h1 h4
  exact h5.right


-- (s) (p → q) ∧ (p → r) ⊢ p → q ∧ r
theorem exercise_1_2_s (h1 : (p → q) ∧ (p → r)) : p → q ∧ r := by

  intro h2
  constructor
  have h3 : p → q := h1.left
  exact h3 h2

  have h4 : p → r := h1.right
  exact h4 h2


-- (t) ⊢  (p → q) → ((r → s) → (p ∧ r → q ∧ s)); here you might be able to ‘recycle’ and augment a proof from a previous exercise.

theorem exercise_1_2_t : (p → q) → ((r → s) → (p ∧ r → q ∧ s)) := by


  intro h1
  intro h2
  intro h3
  constructor
  have h4 : p := h3.left
  exact h1 h4

  have h5 : r := h3.right
  exact h2 h5


-- (u) p → q ⊢  ¬q → ¬p

theorem exercise_1_2_u (h1 : p → q) : ¬q → ¬p := by

  intro h2 -- ¬q
  intro h3 -- p

  have h4 : q := h1 h3 -- applying (p → q) to p to get q
  exact h2 h4 -- contradiction: h2 says ¬q, h4 says q


-- (v)* p ∨ (p ∧ q) ⊢ p

theorem exercise_1_2_v (h1 : p ∨ (p ∧ q)) : p := by

  rcases h1 with h1a|h1b
  exact h1a

  exact h1b.left


-- (w) r, p → (r → q) ⊢ p → (q ∧ r)

theorem exercise_1_2_w (h1 : r) (h2 : p → (r → q)) : p → (q ∧ r)  := by

  intro h3
  constructor
  have h5 : r → q := h2 h3
  exact h5 h1

  exact h1


-- (x)* p → (q ∨ r), q → s, r → s ⊢ p → s

theorem exercise_1_2_x (h1 : p → (q ∨ r)) (h2 : q → s ) (h3 : r → s) : p → s := by

  intro h4
  rcases h1 h4 with hq | hr
  {exact h2 hq}
  {exact h3 hr}


-- (y)* (p ∧ q) ∨ (p ∧ r) ⊢ p ∧ (q ∨ r)
theorem exercise_1_2_y (h1 : (p ∧ q) ∨ (p ∧ r)) : p ∧ (q ∨ r) := by
  constructor
  -- First subgoal: prove p
  · cases h1 with
    | inl hpq => exact hpq.left   -- If (p ∧ q), extract p
    | inr hpr => exact hpr.left   -- If (p ∧ r), extract p
  -- Second subgoal: prove (q ∨ r)
  · cases h1 with
    | inl hpq => left; exact hpq.right   -- If (p ∧ q), we have q, so q ∨ r
    | inr hpr => right; exact hpr.right  -- If (p ∧ r), we have r, so q ∨ r
