Lean is a proof assistant that checks Mathematics step-by-step like a computer. In this game we prove basic facts about natural numbers using Lean's tactics, some definitions, and already proven theorems. Particularly we learn about Peano arithmetic. Note the progress data of the entire game till of writing this in the `Lean Natural Number Game Progress (July 2025).json`

<div style="text-align: center;">
  <img src="./Attachments/Worlds.png" alt="image" height="600">
</div>

We first defined the natural numbers.
- $0$ is a natural number
- Successor of $0$ is also natural numbers, denoted by `succ 0` in Lean
- And successors of successors are natural numbers.

Then we defined addition.
- $n + 0 = n$ 
- $n + succ(m) = succ(n + m)$

Then we proved all sorts of addition facts that we know in arithmetic like commutativity and associativity. We then moved toward multiplication where it was defined to be via these two axioms.
- $a \times 0 = 0$
- $a \times succ(b) = a \times b + a$
And proved a lot of facts about multiplications as well in the relevant worlds.

Furthermore, we defined $\land$ (power), $\ne$, and $\le$ by
- $a ^ 0 = 1$ and $a^{succ(b)} = a ^ b \times a$ 
- $a \ne b$ is $(a = b) \implies False$ 
- $a \le b$ is notation for $\exists c \in \mathbb{N},\; b = a + c$ 

We then also proved a lot of facts about all these mathematical objects. The proofs were using Leans built-in *tactics*:

| Tactic     | Description                      | Abbreviation Explanation                 | What It Does                                                                                                                                            |
| ---------- | -------------------------------- | ---------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| apply      | Forward reasoning application    | "apply" a theorem or hypothesis          | Takes a theorem or hypothesis and applies it to the current goal, transforming the goal according to the theorem's conclusion                           |
| cases      | Case analysis                    | "cases" - split into different scenarios | Splits the proof into multiple cases based on a condition (like `n = 0` or `n = succ k`), allowing you to prove each case separately                    |
| contrapose | Contraposition                   | "contrapose" - logical contraposition    | Transforms a goal of the form `P → Q` into `¬Q → ¬P`, which is logically equivalent but sometimes easier to prove                                       |
| decide     | Decidable proposition resolution | "decide" on truth value                  | Automatically proves or disproves goals that are decidable (computable), particularly useful for equalities between concrete natural numbers            |
| exact      | Exact proof term                 | "exact" match with existing proof        | Provides the exact proof term that solves the current goal, typically used when you have a hypothesis that directly matches what you need to prove      |
| have       | Intermediate step introduction   | "have" an intermediate result            | Introduces an intermediate lemma or result that you can prove and then use in the main proof, helping break complex proofs into manageable steps        |
| induction  | Mathematical induction           | "induction" on natural numbers           | Proves statements about all natural numbers by proving the base case (usually `n = 0`) and the inductive step (if true for `k`, then true for `succ k`) |
| intro      | Introduction rule                | "intro"duce assumptions                  | Introduces assumptions or hypotheses into the context, typically used for implications (`→`) and universal quantifiers (`∀`)                            |
| left       | Left constructor choice          | "left" side of disjunction               | When the goal is a disjunction (`P ∨ Q`), chooses to prove the left side (`P`)                                                                          |
| rfl        | Reflexivity                      | "rfl" - reflexivity                      | Proves goals of the form `a = a` using the reflexivity property of equality                                                                             |
| right      | Right constructor choice         | "right" side of disjunction              | When the goal is a disjunction (`P ∨ Q`), chooses to prove the right side (`Q`)                                                                         |
| rw         | Rewrite                          | "rw" - rewrite using equality            | Rewrites the goal or hypotheses using equalities, substituting one expression for another based on proven equalities                                    |
| simp       | Simplification                   | "simp"lification                         | Automatically simplifies expressions using a database of simplification rules, often solving goals that involve basic arithmetic or logical operations  |
| simp_add   | Addition simplification          | "simp"lification for "add"ition          | Specialized simplification tactic for addition-related expressions, using rules specific to natural number addition                                     |
| symm       | Symmetry                         | "symm"etry of equality                   | Transforms an equality `a = b` into `b = a`, or applies the symmetric property of a relation                                                            |
| tauto      | Tautology solver                 | "tauto"logy                              | Automatically proves goals that are tautologies in propositional logic, handling complex logical combinations                                           |
| trivial    | Trivial proof                    | "trivial" - obviously true               | Proves goals that are trivially true, often used for simple logical statements or when the goal matches a hypothesis exactly                            |
| use        | Existential instantiation        | "use" a specific witness                 | Provides a specific witness (example) for an existential statement (`∃ x, P(x)`), allowing you to prove the existence by giving a concrete example      |
Below here is explanation to how some of the starting proofs were proven in the game. **Note that the rest of the proofs are in the progress file mentioned at the start**. To use that file, simply go to the natural numbers game's website and import the file, then visit any world's level of which's proof you may want to look at.
## Prove 2 = succ (succ 0)
We want to turn succ (succ 0) into 2 step by step.

Step 1: Turn succ 0 into 1
```lean
rw [← one_eq_succ_zero]
```
Now goal becomes: 2 = succ 1

Step 2: Turn succ 1 into 2
```lean
rw [← two_eq_succ_one]
```
Now goal becomes: 2 = 2

Step 3: Both sides are same
```lean
rfl
```

> **Note:** one_eq_succ_zero means 1 = succ 0, two_eq_succ_one means 2 = succ 1, rfl works because 2 = 2 is obviously true


## Addition Rules in Lean
We can't write 2 + 2 = 4 until we define how + works in Lean. Lean defines addition using two basic rules:
1. a + 0 = a
2. a + succ b = succ (a + b)

We start with the first rule: a + 0 = a. This is called add_zero, so add_zero x proves x + 0 = x. rw [add_zero] can be used to simplify any term like b + 0 into b.

Example goal: a + (b + 0) + (c + 0) = a + b + c
Plan: Use rw [add_zero] twice

```lean
rw [add_zero]
```
Goal becomes: a + b + (c + 0) = a + b + c

```lean
rw [add_zero]
```
Goal becomes: a + b + c = a + b + c

```lean
rfl
```


## Precision Rewriting
Sometimes rw [add_zero] just applies to the first match it sees. Like in a + (b + 0) + (c + 0), it rewrites b + 0 first. But if we want Lean to rewrite c + 0 first, we can guide it by giving an explicit input to add_zero.

For example: rw [add_zero c] tells Lean to only apply the theorem to c + 0. You can choose which part to rewrite by giving rw the right target. This gives you more control instead of relying on Lean's default choice.

Goal: a + (b + 0) + (c + 0) = a + b + c

Step 1: Rewrite c + 0 into c
```lean
rw [add_zero c]
```
Goal becomes: a + (b + 0) + c = a + b + c

Step 2: Now rewrite b + 0 into b
```lean
rw [add_zero b]
```
Goal becomes: a + b + c = a + b + c

Step 3: Both sides are equal
```lean
rfl
```

> **Note:** add_zero b means b + 0 = b, add_zero c means c + 0 = c. Giving input to a theorem like this is called precision rewriting.
## Adding with Successors
Every natural number in Lean is either zero, or the successor of another number (written as succ n). So we found one example on how to add 0 (like x + 0 = x), but how to add with successors?

Suppose: 37 + d = q, then: 37 + succ d = succ q because succ d is just one more than d.

This idea is captured in the lemma: add_succ x d : x + succ d = succ (x + d). Whenever your goal has something like x + succ d, you can use: rw [add_succ].

Goal: succ n = n + 1

Step 1: Unravel the 1 on the right-hand side. In Lean, 1 is defined as succ 0, so we rewrite
```lean
rw [one_eq_succ_zero]
```
Goal becomes: succ n = n + succ 0

Step 2: Apply the add_succ lemma
```lean
rw [add_succ]
```
Goal becomes: succ n = succ (n + 0)

Step 3: Simplify n + 0 using add_zero
```lean
rw [add_zero]
```
Goal becomes: succ n = succ n

Step 4: Both sides are equal
```lean
rfl
```

Used theorems:
- one_eq_succ_zero: 1 = succ 0
- add_succ: x + succ y = succ (x + y)
- add_zero: x + 0 = x



## Prove (2 : ℕ) + 2 = 4
We want to prove that 2 + 2 equals 4 using step-by-step rewrites. Since Lean only understands basic definitions like succ, we gradually reduce the expression to known equalities.

First, we convert the second 2 in the expression 2 + 2 to succ 1 using the equality two_eq_succ_one. Since there are two 2s in the expression, we use nth_rewrite 2 to specifically target the second one.

```lean
nth_rewrite 2 [two_eq_succ_one]
```
Now the goal becomes: 2 + succ 1 = 4

We use the add_succ rule to simplify 2 + succ 1 to succ (2 + 1).

```lean
rw [add_succ]
```
The goal is now: succ (2 + 1) = 4

Next, we simplify 2 to succ 1 again using two_eq_succ_one, and simplify 1 to succ 0 using one_eq_succ_zero.

```lean
rw [two_eq_succ_one, one_eq_succ_zero]
```
The goal becomes: succ (succ 1 + succ 0) = 4

We apply add_succ to succ 1 + succ 0, and then simplify with add_zero:

```lean
rw [add_succ, add_zero]
```
Now the left-hand side becomes: succ (succ (succ 1))

We want the right-hand side 4 to be written in terms of succ, so we rewrite it step by step using these equalities: three_eq_succ_two, four_eq_succ_three, and so on.

You can either write:
```lean
rw [four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
```

Or use the reverse direction with left arrows ← if you want to go from succ form to numeral form (which is cleaner and more efficient):
```lean
rw [← three_eq_succ_two, ← four_eq_succ_three]
```

Now both sides match exactly, so we finish with:
```lean
rfl
```



## Addition World Theorems
**Theorem:**  
`zero_add`: ∀ n : ℕ, 0 + n = n

**Proof:**  
```lean
induction n with d hd
-- base case: n = 0
rw [add_zero]
rfl

-- inductive step: assume 0 + d = d
rw [add_succ, hd]
rfl
```

| Step              | What it means                                                             |
| ----------------- | ------------------------------------------------------------------------- |
| `n`               | is the number we’re proving the property for                              |
| `d`               | is a smaller number (used in the inductive step)                          |
| `hd` (hypothesis) | is the assumption that `0 + d = d` (we'll use this to prove for `succ d`) |

the goal is to show that 0 + n equals n for all natural numbers n. start with induction on n. for the base case, the goal is 0 + 0 = 0. use `rw [add_zero]` to simplify the left-hand side, then `rfl` to finish.

for the inductive step, assume the statement holds for some `d`, i.e., `0 + d = d`. the new goal becomes `0 + succ d = succ d`. apply `rw [add_succ]` to get `succ (0 + d)`, then use `rw [hd]` to replace `0 + d` with `d`. both sides now match as `succ d`, so use `rfl` to complete the proof.


**Theorem:**  
`succ_add`: ∀ a b : ℕ, succ a + b = succ (a + b)

**Proof:**  
```lean
induction b with k hypo

-- base case: b = 0
repeat rw [add_zero]
rfl

-- inductive step: assume succ a + k = succ (a + k)
repeat rw [add_succ]
rw [hypo]
rfl
```

the goal is to show that adding b to succ a is the same as taking the successor of a + b. this is done using induction on b.

for the base case, the goal becomes `succ a + 0 = succ (a + 0)`. simplify both sides using `rw [add_zero]`, then use `rfl` since both sides reduce to `succ a`.

for the inductive step, assume the statement holds for some `k`, i.e., `succ a + k = succ (a + k)`. the new goal is `succ a + succ k = succ (a + succ k)`. simplify both sides using `repeat rw [add_succ]`. now the goal becomes `succ (succ a + k) = succ (succ (a + k))`. apply the assumption `rw [hypo]` to replace `succ a + k` with `succ (a + k)`. both sides now match, so use `rfl` to finish the proof.
