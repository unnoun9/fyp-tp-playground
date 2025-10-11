## 1.1 Evaluating Expressions
 
```lean
#eval String.append "Hello, " "Lean!"
#eval String.append "great" (String.append "oak" "tree")
#eval String.append "Hello" (String.append "world")
```

The first line works without parentheses because `"Hello, "` and `"Lean!"` are both string values being passed directly to `String.append` as two arguments, so it's just `String.append str1 str2`.

The second line uses parentheses because it's nesting one `String.append` inside another. `String.append "oak" "tree"` runs first and returns `"oaktree"`, which then becomes the second argument for `String.append "great" ___`.

So:  
`String.append "great" (String.append "oak" "tree")`  
means: `"great" ++ "oak" ++ "tree"`

The third line doesn't work because `"Hello"` and `"world"` are not separated by a comma or space, it just glues them together with no space. If the goal is to get `"Hello world"` (with space), need to include a space string.

This works:  
```lean
#eval String.append "Hello " "world"
```

Or with nesting, do this:  
```lean
#eval String.append "Hello" (String.append " " "world")
```

This builds `"Hello" ++ " " ++ "world"`  
and gives the expected output: `"Hello world"`

So, it's not about the number of arguments, it's about *when* parentheses are needed.

Lean uses function application by space, so this:

```lean
String.append "Hello, " "Lean!"
```

means: call `String.append` with `"Hello, "` and `"Lean!"`

But this:

```lean
String.append "great" (String.append "oak" "tree")
```

means: run `String.append "oak" "tree"` first → result is `"oaktree"`  
then use it as the second argument: `String.append "great" "oaktree"` → `"greatoaktree"`

Parentheses are only needed when passing the *result of a function* as an argument.

This fails:

```lean
String.append "Hello" String.append "world"
```

because Lean reads it like:  
→ first argument: `"Hello"`  
→ second argument: `String.append` (which is not a string)  
→ third thing: `"world"`, extra

So to fix it, wrap the inner call in `()`:

```lean
String.append "Hello" (String.append " " "world")
```

Now:  
→ second argument becomes `" world"`  
→ result: `"Hello world"`

**Code:**  
```lean
#eval String.append "it is " (if 1 > 2 then "yes" else "no")
```

**Evaluation steps:**  
```
String.append "it is " (if 1 > 2 then "yes" else "no")
→ String.append "it is " (if false then "yes" else "no")
→ String.append "it is " "no"
→ "it is no"
```

**Explanation:**  
In imperative languages like C or Python, there are *two* things, conditional statements (`if`) and conditional expressions (`?:` or inline `if`).  
Lean doesn’t do that — Lean is *expression-oriented*, meaning *everything returns a value*, so there's only conditional expressions.

In Lean, this works:  
```lean
if condition then value1 else value2
```

because it's an expression — it returns either `value1` or `value2` depending on the condition.

For example:  
`if 1 > 2 then "yes" else "no"`  
this is saying: if 1 is greater than 2, return `"yes"`, otherwise return `"no"`

Now look at this code:

```lean
#eval String.append "it is " (if 1 > 2 then "yes" else "no")
```

First step:  
`1 > 2` is false → replace with `false`  
now it becomes:  
`String.append "it is " (if false then "yes" else "no")`

Then:  
since the condition is false, it picks `"no"`  
→ `String.append "it is " "no"`  
→ `"it is no"`

So even though it feels weird at first, remember:  
`(if false then "yes" else "no")` is just a string expression that evaluates to `"no"`  
and then that result is passed into `String.append`.

**About output not showing up:**  
Make sure to use `#eval`, just typing an expression like  
```lean
String.append "it is " (if 1 > 2 then "yes" else "no")
```

won’t show anything, Lean needs `#eval` in front to evaluate and show output.

**Correct working version:**  
```lean
#eval String.append "it is " (if 1 > 2 then "yes" else "no")
-- output: "it is no"
```

_NOTE:_ Lean won’t show output unless `#eval` is used, expressions alone don’t auto-display.  
Add `#eval` before the expression to make Lean evaluate and print the result.

### 1.1 Exercises

```lean
#eval 42 + 19
-- 61

#eval String.append "A" (String.append "B" "C")
-- "ABC"

#eval String.append (String.append "A" "B") "C"
-- "ABC"

#eval if 3 == 3 then 5 else 7
-- 5

#eval if 3 == 4 then "equal" else "not equal"
-- "not equal"
```

**Fix notes:**

- This fails:  
  ```lean
  #eval String.append "it is" (if 3 == 3 then 5 else 7)
  ```  
  because `String.append` expects both arguments to be strings — but `if 3 == 3 then 5 else 7` is a number.

- To make it work, either use strings directly:
  ```lean
  #eval String.append "it is " (if 3 == 3 then "yes" else "no")
  -- "it is yes"
  ```

- Or don't use `String.append` when working with numbers:
  ```lean
  #eval if 3 == 3 then 5 else 7
  -- 5
  ```

## 1.2 Types

Types describe what kind of values a program can compute. Every expression in Lean must have a type. Types help the compiler figure out memory layout, catch bugs like adding a number to a string, and act as a lightweight spec for functions. Lean's type system is powerful enough to express logic and math proofs, but also works fine with basic stuff like `Nat` and `Int`.

Types are given using a colon inside parentheses:
```lean
#eval (1 + 2 : Nat)
-- 3
```

`Nat` means natural numbers — non-negative integers. Subtraction on `Nat` never gives negative results. If the answer would be negative, it just gives 0:
```lean
#eval (1 - 2 : Nat)
-- 0
```

To get actual negative numbers, use `Int`:
```lean
#eval (1 - 2 : Int)
-- -1
```

To check a type without evaluating:
```lean
#check (1 - 2 : Int)
-- 1 - 2 : Int
```

When a program doesn’t make sense type-wise, Lean shows a type mismatch:
```lean
#check String.append ["hello", " "] "world"
```

Error:  
`["hello", " "]` is a list of strings (`List String`)  
but `String.append` expects just a single `String` as the first argument  
so this fails.

**Summary notes:**

- `Nat` → only non-negative numbers  
- `Int` → can include negative numbers  
- `#eval` → run expression  
- `#check` → just show type, don’t run  
- Type errors happen when arguments are not what a function expects.

This works:
```lean
#eval String.append "great" (String.append "oak" "tree")
-- "greatoaktree"
```

because it's **not** a list. It's just a function inside a function.

`String.append "oak" "tree"` runs first → gives `"oaktree"`  
then `"great"` and `"oaktree"` are passed to `String.append`.

So it’s like:
```lean
String.append "great" "oaktree"
```

which is totally valid.

But this fails:
```lean
#eval String.append ["oak", "tree"] "great"
```

because `["oak", "tree"]` is a **list** of strings, `List String`.  
Lean doesn’t know how to take a list and treat it like a single string.

**Square brackets → list**  
**Parentheses → grouping / function call**

So, no square brackets = not a list.

## 1.3 Functions and Definitions

In Lean, new names are defined using `def` and `:=` (not `=`, which is used to prove equalities).

```lean
def hello := "Hello"
def lean : String := "Lean"
```

Can use them like:
```lean
#eval String.append hello (String.append " " lean)
-- "Hello Lean"
```

Defined names can only be used **after** they are defined.

**1.3.1 Defining Functions**

Functions are also defined with `def`, no special syntax needed.

```lean
def add1 (n : Nat) : Nat := n + 1
#eval add1 7
-- 8
```

Multi-argument function:
```lean
def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then k else n

#eval maximum (5 + 8) (2 * 7)
-- 14
```

String join with space:
```lean
def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)

#eval spaceBetween "Lean" "Rocks"
-- "Lean Rocks"
```

Functions are just values too.  
`Nat → Bool` means: takes a Nat, returns a Bool  
`Nat → Nat → Nat` means: takes two Nats, returns a Nat

```lean
#check add1
-- add1 (n : Nat) : Nat

#check (add1)
-- add1 : Nat → Nat

#check (maximum)
-- maximum : Nat → Nat → Nat
```

Functions in Lean are **curried**.  
It means: one arg at a time, like this:
```lean
#check maximum 3
-- maximum 3 : Nat → Nat

#check spaceBetween "Hello"
-- spaceBetween "Hello" : String → String
```

`Nat → Nat → Nat` = `Nat → (Nat → Nat)`  
Function returns another function.

### 1.3.1 Exercises

1. `joinStringsWith` function:

```lean
def joinStringsWith (sep : String) (a : String) (b : String) : String :=
  String.append a (String.append sep b)

#eval joinStringsWith ", " "one" "and another"
-- "one, and another"
```

2. Type of `joinStringsWith ": "`:

```lean
#check joinStringsWith ": "
-- joinStringsWith ": " : String → String → String
```

3. Volume function:

```lean
def volume (height : Nat) (width : Nat) (depth : Nat) : Nat :=
  height * width * depth

#eval volume 2 3 4
-- 24
```

**Understanding `#check joinStringsWith ": "`**

Definition:
```lean
def joinStringsWith (sep : String) (a : String) (b : String) : String
```
has type:
```
String → String → String → String
```

Calling:
```lean
#check joinStringsWith ": "
```
returns:
```
String → String → String
```

→ because only `sep` is filled in → it returns a function waiting for 2 more strings.

**This is called partial application**.  
You’re giving one input and getting back a function.

```lean
def colonJoin := joinStringsWith ": "
#eval colonJoin "label" "value"
-- "label: value"
```

## 1.3.2 Defining Types

Types are expressions in Lean — we can define aliases like:

```lean
def Str : Type := String
def aStr : Str := "This is a string."
```

But this fails:
```lean
def NaturalNumber : Type := Nat
def thirtyEight : NaturalNumber := 38
-- error: failed to synthesize OfNat
```

because number literals are **polymorphic**, Lean tries to find a number conversion for `NaturalNumber`, but can't.

**Fix 1**: use explicit Nat cast on the right-hand side.

```lean
def thirtyEight : NaturalNumber := (38 : Nat)
```

**Fix 2**: use `abbrev` instead of `def`.

```lean
abbrev N : Type := Nat
def thirtyNine : N := 39
-- works fine
```

Abbrev definitions are *reducible*, Lean will auto-unfold them during overload resolution.

**Key notes:**
- `def` → defines values or types, not always unfoldable
- `abbrev` → defines aliases, always unfoldable
- Number overload resolution works better with `abbrev` than `def`


