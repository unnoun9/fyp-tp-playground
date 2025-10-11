-- Gives a list of fibonaccis up to `n_max`
def fibs (n_max : Nat) : List Nat :=
  match n_max with
  | 0 => []
  | 1 => [0]
  | 2 => [0, 1]
  | n + 3 =>
    let prev_fibs := fibs (n + 2)
    match prev_fibs.reverse with
    | n_1 :: n_2 :: _ => prev_fibs ++ [n_1 + n_2]
    | _ => prev_fibs

#eval fibs 50

-- Pending: Prove properties about the Fibonacci series
def fibonaccis := fibs 200
-- theorem fib_recursive (n : Nat) (h : n ≥ 2) (h2 : n ≤ 200): fibonaccis[n] = fibonaccis[n - 1] + fibonaccis[n - 2] := sorry
