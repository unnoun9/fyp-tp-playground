set_option linter.unusedVariables false
/-
//////////////////////// 1.1. Evaluating Expressions ////////////////////////
-/
#eval String.append "hello " "Lean!"
#eval String.append "foo" (String.append "bar" "baz")
#eval String.append "hello" (String.append " " "world")
#eval String.append "it is " (if 1 > 2 then "yes" else "no")
-- This fails: #eval String.append "it is" (if 3 == 3 then 5 else 7)
-- Fix: #eval String.append "it is " (if 3 == 3 then "5" else "7")

-- Exercises:
#eval 42 + 19
#eval String.append "A" (String.append "B" "C")
#eval String.append (String.append "A" "B") "C"
#eval if 3 == 3 then 5 else 7
#eval if 3 == 4 then "equal" else "not equal"

/-
//////////////////////// 1.2. Types ////////////////////////
-/
#eval (1 + 2 : Nat)
#eval (1 - 2 : Nat)
#eval (1 - 2 : Int)
#check (1 - 2 : Int)
#eval String.append "great" (String.append "oak" "tree")
-- This fails: #check String.append ["hello", " "] "world"
-- This fails: #eval String.append ["oak", "tree"] "great"

/-
//////////////////////// 1.3. Definitions ////////////////////////
-/
-- Defining values
def π := 3.14159
#eval 2 * π
def hello := "Hello"
def lean : String := "Lean"
#eval String.append hello (String.append " " lean)

-- Defining functions
def add1 (n : Nat) : Nat := n + 1
#eval add1 7

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then k else n
#eval maximum (5 + 8) (2 * 7)

def spaceBetween (first : String) (second : String) : String :=
  String.append first (String.append " " second)
#eval spaceBetween "Lean" "Rocks"

-- Function types
#check add1
#check maximum
#check maximum 3
#check spaceBetween
#check spaceBetween "foo"

-- Exercises:
def joinStringsWith (sep s t: String) : String :=
  String.append s (String.append sep t)
#eval joinStringsWith "bar" "foo" "baz"

def volume (l w h : Nat) := l * w * h
#check volume
#eval volume 2 3 4

-- Partial application or Currying
#check joinStringsWith ": "
def colonJoin := joinStringsWith ": "
#eval colonJoin "label" "value"

-- Defining types
def str : Type := String
def s : str := "foo"
-- This fails because of number literal's overloading behavior:
-- def NaturalNumber : Type := Nat
-- def thirtyEight : NaturalNumber := 38
-- Fix 1
def NaturalNumber : Type := Nat
def thirtyEight : NaturalNumber := (38 : Nat)
-- Fix 2, using abbrev, which marks the definition of type as reducible
abbrev ℕ : Type := Nat
def thirtyNine : ℕ := 39

/-
//////////////////////// 1.4. Structures ////////////////////////
-/
structure vec2 where
    x : Float
    y : Float
deriving Repr

structure vec3 where
    overridedConstructor ::
    x : Float
    y : Float
    z : Float
deriving Repr

def origin : vec2 := { x := 0, y := 0 }
#eval origin
#check { x := 0, z := 0, y := 0 : vec3 }
#check vec3.overridedConstructor 1 2 3

-- Functions on structures
def vec2.modifyBoth (f : Float → Float) (u : vec2) : vec2 :=
    { x := f u.x, y := f u.y }
def fourandthree : vec2 := vec2.mk 4.3 3.4
#eval fourandthree.modifyBoth Float.floor

-- Exercises:
structure RectangularPrism where
    width : Float
    height : Float
    depth : Float

def volumeRect (prism : RectangularPrism) : Float :=
    prism.width * prism.height * prism.depth
#check volumeRect

def prism : RectangularPrism := RectangularPrism.mk 1 2 3
#eval volumeRect prism

structure segment where
    end1 : vec2
    end2 : vec2

def segment.length (seg : segment) : Float :=
    Float.sqrt ((seg.end1.x - seg.end2.x) ^ 2 + (seg.end1.y - seg.end2.y) ^ 2)

#check segment.length
def seg : segment := segment.mk (vec2.mk 0 0) (vec2.mk 1 1)
#eval seg.length

/-
//////////////////////// 1.5. Datatypes and Patterns ////////////////////////
-/
inductive meBool where | F : meBool | T : meBool
inductive meNat where
    | zero
    | succ (n : meNat) : meNat
#check meBool
#check meNat

def isZero (n : Nat) : Bool :=
    match n with
    | Nat.zero => true
    | Nat.succ k => false

#eval isZero 0
#eval isZero Nat.zero
#eval isZero 9

def pred (n : Nat) : Nat :=
    match n with
    | Nat.zero => 0
    | Nat.succ k => k

#eval pred 0
#eval pred 9

def zCoord (u : vec3) : Float :=
    match u with
    | { x := a, y := b, z:= c } => c

-- Recursive functions:
def even (n : Nat) : Bool :=
    match n with
    | Nat.zero => true
    | Nat.succ j => not (even j)

def plus (n k : Nat) : Nat :=
    match k with
    | Nat.zero => n
    | Nat.succ k' => Nat.succ (plus n k')

def times (n k : Nat) : Nat :=
    match k with
    | Nat.zero => Nat.zero
    | Nat.succ k' => plus n (times n k')

def minus (n k : Nat) : Nat :=
    match k with
    | Nat.zero => n
    | Nat.succ k' => pred (minus n k')

/- This fails and the reason will be discussed later:
def div (n k : Nat) : Nat :=
    if n < k then 0
    else Nat.succ (div (n - k) k) -/

/-
//////////////////////// 1.6. Polymorphism ////////////////////////
-/

structure pvec2 (α : Type) where
    x : α
    y : α
deriving Repr

def natOrigin : pvec2 Nat := { x := 0, y := 0 }

def replaceX (α : Type) (u : pvec2 α) (val : α) :=
    { u with x := val }

#check replaceX
#check replaceX Nat
#check replaceX Nat natOrigin
#check replaceX Nat natOrigin 5
#eval replaceX Nat natOrigin 5

inductive Sign where
    | pos
    | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
    match s with
    | Sign.pos => (3 : Nat)
    | Sign.neg => (-3 : Int)

-- Lists:
def primesUnder10 : List Nat := [2, 3, 5, 7]

inductive meList (α : Type) where
    | nil : meList α
    | cons : α → meList α → meList α
#check meList

def mePrimesUnder10 : meList Nat := meList.cons 2 (meList.cons 3 (meList.cons 5 (meList.cons 7 meList.nil)))

def meLength (α : Type) (list : meList α) : Nat :=
    match list with
    | meList.nil => Nat.zero
    | meList.cons head tail => Nat.succ (meLength α tail)

def pLength (α : Type) (list : List α) : Nat :=
    match list with
    | [] => Nat.zero
    | head :: tail => Nat.succ (pLength α tail)

#eval meLength Nat mePrimesUnder10
#eval pLength Nat primesUnder10

-- Implicit Arguments:
def replaceXImplicit {α : Type} (u : pvec2 α) (newX : α) : pvec2 α :=
    { u with x := newX }

def length {α : Type} (list : List α) : Nat :=
    match list with
    | [] => Nat.zero
    | head :: tail => Nat.succ (length tail)

#eval length primesUnder10
#eval replaceXImplicit natOrigin 9

#check length (α := Int)
def natsLength := length (α := Nat)
#eval natsLength primesUnder10

-- Option:
inductive meOption (α : Type) : Type where
    | none : meOption α
    | some (val : α) : meOption α

def meHead? {α : Type} (xs : List α) : Option α :=
    match xs with
    | [] => none
    | y :: _ => some y

#eval primesUnder10.head?
#eval match primesUnder10.head? with | none => -1 | some x => (x : Int)
-- This fails because Lean can't infer type: #eval [].head?
#eval [].head? (α := Int)
#eval ([] : List Int).head?

-- Prod:
structure meProd (α β : Type) : Type where
    fst : α
    snd : β

def fives : String × Int := { fst := "five", snd := 5 }
def fives2 : String × Int := ("five", 5)
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
def sevens2 : String × Int × Nat := ("VII", (7, 4 + 3))

-- Sum:
inductive meSum (α β : Type) : Type where
    | inl : α → meSum α β
    | inr : β → meSum α β

def PetName : Type := String ⊕ String -- First string is dog's name, second is cat's name
def animals : List PetName := [Sum.inl "Foo", Sum.inr "Bar", Sum.inl "Baz"]

def howManyDogs (pets : List PetName) : Nat :=
    match pets with
    | [] => 0
    | Sum.inl _ :: morePets => howManyDogs morePets + 1
    | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals

-- Unit:
inductive meUnit : Type where
    | unit : meUnit

inductive ArithExpr (ann : Type) : Type where
    | int : ann → Int → ArithExpr ann
    | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
    | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
    | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

#eval ()

-- Empty: No constructors

-- Some Errors:
/-
Universe Type error when a constructor takes another type as argument:
inductive MyType : Type where
    | ctor : (α : Type) → α → MyType

Also the constructor can't have a function that takes in the type being defined as argument:
inductive MyType : Type where
    | ctor : (MyType → Int) → MyType

Also recursive functions taking two parameters shouldn't match agains the pair, but do so separately:
def sameLength (xs : List α) (ys : List β) : Bool :=
    match (xs, ys) with
    | ([], []) => true
    | (x :: xs', y :: ys') => sameLength xs' ys'
    | _ => false
This is fixed by nested pattern matching below
-/

def sameLength (xs : List α) (ys : List β) : Bool :=
    match xs with
    | [] => match ys with
        | [] => true
        | _ => false
    | x :: xs' => match ys with
        | y :: ys' => sameLength xs' ys'
        | _ => false

/-
Forgetting an argument to inductive type:
inductive myType (α : Type) : Type where
    | ctor : α → MyType -- Here it should be α → MyType α

inductive myType (α : Type) : Type where
    | ctor : α → MyType α -- This is correct

def ofFive : MyType := ctor 5 -- Error because a type should be passed to MyType
-/

-- Exercises:
-- Function that finds the last entry in a list and returns an Option
def tail? {α : Type} (xs : List α) : Option α :=
    match xs with
    | [] => none
    | x :: [] => some x -- Pattern could be [x] here
    | x :: xs' => tail? xs' -- Pattern could be _ :: xs' here

#eval tail? [1, 2, 3, 4, 5]

-- Function that finds the first entry in a list that satisfies a given predicate
def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
    match xs with
    | [] => none
    | x :: xs' => if predicate x then some x else List.findFirst? xs' predicate

#eval List.findFirst? [1, 2, 3, 4, 5] (fun n => n > 3)
#eval List.findFirst? [1, 2, 3] (fun n => n > 5)

-- Function that switches two fields in a pair
def Prod.switch {α β : Type} (pair : α × β) : β × α :=
    (pair.snd, pair.fst) -- or: match pair with | (a, b) => (b, a)

#eval (1, 2, 3).switch

-- Rewriting PetName example using custom datatype
inductive Pet_Name where
    | dog : String → Pet_Name
    | cat : String → Pet_Name

def pets : List Pet_Name := [Pet_Name.dog "Foo", Pet_Name.cat "Bar", Pet_Name.dog "Baz"]

def how_many_dogs (pets : List Pet_Name) : Nat :=
    match pets with
    | [] => 0
    | Pet_Name.dog _ :: more_pets => how_many_dogs more_pets + 1
    | Pet_Name.cat _ :: more_pets => how_many_dogs more_pets

#eval how_many_dogs pets

-- Function that turns two lists into list of pairs with the resulting list being as long as the shortest input list
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
    match xs with
    | [] => []
    | x :: xs' => match ys with
        | [] => []
        | y :: ys' => (x, y) :: zip xs' ys'

#eval zip primesUnder10 primesUnder10
#eval zip primesUnder10 [1, 2, 3]
#eval zip [1, 2, 3] primesUnder10
#eval zip primesUnder10 ([] : List Nat)
#eval zip ([] : List Nat) primesUnder10
#eval zip ([] : List Nat) ([] : List Nat)

-- Function that returns first n entries in a list
def take {α : Type} (n : Nat) (xs : List α) : List α :=
    match xs with
    | [] => []
    | x :: xs' => if n > 0 then x :: take (n - 1) xs' else []

#eval take 0 ["foo", "bar", "baz", "meow", "woof"]
#eval take 1 ["foo", "bar", "baz", "meow", "woof"]
#eval take 2 ["foo", "bar", "baz", "meow", "woof"]
#eval take 3 ["foo", "bar", "baz", "meow", "woof"]
#eval take 9000 ["foo", "bar", "baz", "meow", "woof"]

-- Function that turns α × (β ⊕ γ) into (α × β) ⊕ (α × γ)
def prod_over_sum_expand {α β γ : Type} (pos : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
    match pos with
    | (a, Sum.inl b) => Sum.inl (a, b)
    | (a, Sum.inr c) => Sum.inr (a, c)

#eval prod_over_sum_expand ("Prime", (Sum.inl 19 : Nat ⊕ Nat))
#eval prod_over_sum_expand ("Composite", (Sum.inr 20 : Nat ⊕ Nat))

-- Function that turns Bool × α into α × α
def times_two {α : Type} (prod : Bool × α) : α × α :=
    (prod.2, prod.2)

/-
//////////////////////// 1.7. Additional Conveniences ////////////////////////
-/
-- `length` function defined in the last section (line 249) can be written without {α : Type}
-- Can also write it like this because the name of arg isn't used elsewhere
def length_short : List α → Nat
    | [] => 0
    | y :: ys => Nat.succ (length ys)

def drop_v1 : Nat → List α → List α
    | Nat.zero, xs => xs
    | _, [] => []
    | Nat.succ n, x :: xs => drop_v1 n xs -- Remove n items from list

def fromOption (default : α) : Option α → α -- `default` is a named argument here and match is applied automatically to an Option
    | none => default
    | some x => x

-- Option.getD is the same as fromOption
#eval (some "foo").getD ""
#eval none.getD ""

-- Local definitions:
def unzip_v1 : List (α × β) → List α × List β -- Convert List of pairs into pairs of List
    | [] => ([], [])
    | (x, y) :: xys => (x :: (unzip_v1 xys).fst, y :: (unzip_v1 xys).snd) -- Two recursive calls!

def unzip_v2 : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys =>
        let unzipped : List α × List β := unzip_v2 xys -- Recursive call result stored in a local variable
        (x :: unzipped.fst, y :: unzipped.snd)

def unzip_v3 : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys => let (xs, ys) : List α × List β := unzip_v3 xys; (x:: xs, y :: ys) -- `let` definition in one line via `;` and pattern matching on the result of the recursive call

def reverse (xs : List α) : List α :=
    let rec helper : List α → List α → List α
        | [], so_far => so_far
        | y :: ys, so_far => helper ys (y :: so_far)
    helper xs []

#eval reverse [1, 2, 3]

-- Type inference:
def unzip_v4 : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys =>
        let unzipped := unzip_v4 xys -- Ommitted annotation here
        (x :: unzipped.fst, y :: unzipped.snd)

def unzip_v5 (pairs : List (α × β)) := -- Ommitted return type but need named argument
    match pairs with
    | [] => ([], [])
    | (x, y) :: xys =>
        let unzipped := unzip_v5 xys
        (x :: unzipped.fst, y :: unzipped.snd)
-- Generally, explicitly writing type annotations is better for the programmer and the reader and helps the compiler too

def drop_v2 (n : Nat) (xs : List α) : List α :=
    match n, xs with -- Simulatneous pattern matching
    | Nat.zero, ys => ys
    | _, [] => []
    | Nat.succ n, y :: ys => drop_v2 n ys

def same_length (xs : List α) (ys : List β) : Bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => same_length xs' ys'
    | _, _ => false

-- Natural numbers' patterns:
def even_v2 : Nat → Bool
    | 0 => true
    | n + 1 => not (even n)

def halve_v1 : Nat → Nat
    | Nat.zero => 0
    | Nat.succ Nat.zero => 0
    | Nat.succ (Nat.succ n) => halve_v1 n + 1

def halve_v2 : Nat → Nat
    | 0 => 0
    | 1 => 0
    | n + 2 => halve_v2 n + 1

-- Anonymous functions:
#check fun x => x + 1

#check λ x => x + 1

#check fun (x : Int) => x + 1

#check fun {α : Type} {x : α} => x

#check fun
    | 0 => none
    | n + 1 => some n

def double : Nat → Nat := fun
    | 0 => 0
    | k + 1 => double k + 2

#check (· + 1)
#check (· + 5, 3)
#check ((· + 5), 3)
#eval (fun x => x + x) 9
#eval (· * 2) 9


-- Namespaces:
-- `double` in `Nat.`
def Nat.double (x : Nat) : Nat := x + x
#eval Nat.double 9
#eval (9 : Nat).double


namespace space_of_name
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end space_of_name

#check space_of_name.triple
#check space_of_name.quadruple


-- Opening/Using namespaces
def times_twelve (x : Nat) :=
    open space_of_name in
    quadruple (triple x)

open space_of_name in -- Omit `in` to use namespace globally in the file
#check quadruple

-- `if let`:
inductive Inline : Type where
    | linebreak
    | string : String → Inline
    | emph : Inline → Inline
    | strong : Inline → Inline

def Inline.string?_v1 (inline : Inline) : Option String :=
    match inline with
    | Inline.string s => some s
    | _ => none

def Inline.string?_v2 (inline : Inline) : Option String :=
    if let Inline.string s := inline then
        some s
    else none

-- Positional structure arguments:
#eval (⟨1, 2⟩ : vec2)

-- String interpolation: f-strings / ${strings}
#eval s!"three nines is {3 * 9}, it is also {space_of_name.triple 9}"

/-
//////////////////////// Apparently this is how to write a theorem proof! ////////////////////////
-/
theorem add_comm (a b : Nat) : a + b = b + a := by
    induction b with
    | zero => rw [Nat.add_zero, Nat.zero_add]
    | succ b ih => rw [Nat.add_succ, ih, Nat.succ_add]
