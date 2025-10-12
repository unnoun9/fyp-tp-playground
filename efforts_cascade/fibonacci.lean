def fib (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n' + 2 => fib (n' + 1) + fib n'


#eval fib 0
#eval fib 2
#eval fib 1
#eval fib 5
#eval fib 10
#eval fib 20
#eval fib 9

def fib_sequence (n : Nat) : List Nat :=
 match n with
 | 0 => []
 | n' + 1 => fib_sequence n' ++ [fib n']

#eval fib_sequence 10



-- properties

theorem fib_zero : fib 0 = 0 := by rfl

theorem fib_one : fib 1 = 1 := by rfl

theorem fib_two : fib 2 = 1 := by simp [fib]

theorem fib_three : fib 3 = 2 := by rfl

theorem fib_three_have : fib 3 = 2 := by
 have h1 : fib 2 = 1 := by rfl
 have h2 : fib 1 = 1 := by rfl
 calc fib 3
    = fib 2 + fib 1 := by rfl
  _ = 1 + 1  := by rw [h1, h2]
  _ = 2   := by rfl


theorem fib_three_cal : fib 3 = 2 := by

  calc fib 3
     = fib 2 + fib 1    := by rfl
    _ = (fib 1 + fib 0) + fib 1 := by rfl
    _ =  (1 + 0) + 1 := by rfl
    _ = 2            := by rfl

-- holds for ALL n
theorem fib_succ_succ (n : Nat) : fib (n + 2) = fib (n + 1) + fib n := by
  rfl

-- fibonacci numbers are always non-negative
theorem fib_nonneg (n : Nat) : fib n ≥ 0 := by
  -- trivially true since Nat can't be negative
  exact Nat.zero_le (fib n)

-- optimized versions

def fib_tail (n : Nat) : Nat :=
 let rec aux (k : Nat) (a b : Nat) : Nat :=
   match k with
   | 0 => a
   | k' + 1 => aux k' b (a + b)
 aux n 0 1

#eval fib_tail 10
#eval fib_tail 20
