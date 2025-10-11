### Types

 Types are like sets of values. And an expression or value that belongs to a type means that they belong to a set of values. The `()` is the simplest value, of the type `unit`, is the only value in this type. Unit types don't return a value.
 
- `bool`: `true`, `false`. Operators are `andalso`, `orelse`, which are short circuited, and `not`. In the `if` statement, `if e1 then e2 else e3`, where `e2` and `e2` are to be of same type, and `e1` of `bool` type.

- `int`: Negation operation is done through $\sim$. $+, -, *$, exist but not / since that is for real numbers. However, operation `div` is available that discards decimal portion of he result as expected. $=, <, <=, >, >=$ for comparison. Size of integers is not imposed in SML, but is for SML/NJ (31 bits, $\sim1073741824$ to $1073741823$). Bit-twiddling operations not available for SML integers.

- `real`: Floating point numbers. Can be written as $3.141592$ or as $3141592e\sim6$. $\sim, +, -, *, /$ operations are available.`NaN` to represent a results which don't define a real number like $\sqrt{-1}$. `inf` for $\infty$. `some_number / 0` results in `inf`. Can be compared via $<, <=, >, >=$ but not $=$. Reals and integers are not interchangeable — an integer and a real can't be added — no automatic coercion or casting is done — but coercion functions are available in the Basis Library.

- `char`: Characters. Written as `#"a"`. Operations `ord` and `chr` for character → ASCII value integer, or ASCII value integer → character.

- `string`: `"` are used for representation. Operations are `size` returns length of string, `^` to concatenate two strings (infix operation), and others.

- Compound types: tuples, records, lists.

- Tuple: Order of values in tuple matters. Type of tuple is `'a * 'b * ... * 'z`. `(3, true)` is of type `int * bool`, `(true, 3)` is of type `**bool** * int`. `#n` extracts the nth element form the tuple where $n$ corresponds to the position in tuple. Tuple with one element is just that element, a tuple with no elements is the unit value.

- Records: Access elements by name, e.g., `{x = 3.0, y = 1, z = true}` of type `{x : real, y : int, z : bool}`, where names are part of the type! Order of fields doesn't matter but names matter. `#x` to select a field, where $x$ is the name of the field. A tuple $(x_1,...,x_n)$ can be seen as record $\{1=x_1,...,n=x_n\}$ (this explains the reliance of tuples on ordering since it ordering guides the naming of the fields). Empty record is the unit value.

### Declarations

`val` is used to bind values to identifiers such as `val x = 3`, `val y = 3 + 3`, `val x = 1 val y = 2`.  `let` allows one to declare local bindings used in the evaluation of some expression, e.g., $(3+4)\times(3+4)-(3+4)$ can be written as:
```sml
> let
	val a = 3 + 4
in
	(a * a) - a
end;
```
The is another kind of declaration called *local declaration*, which looks like `local local_declarations_part in top_level_declarations end`, where you can temporary variables or helper bindings that are invisible outside the `local` and `in` clauses. After the `local` block finishes, the bindings created in the `in` part becomes available for the rest of the program. An example:
```sml
> local
	val a = 3
	val b = 10
in
	val x = a + b
	val y = a * b
end; (* Now x is 13 and y is 30 *)

> x; (* Results in 13 *)
> y; (* Results in 30 *)
> a; (* Gives error *)
> b; (* Gives error *)
```
`let` and `local` seem like the same thing, however apparently, they're not. `let` is used for expressions, while `local` is used to define other bindings or functions.

Annotating types in declaration can be useful for the type inferring algorithm. Annotating expressions look like `val a = 3 + 4 : int`, while annotating the binding itself looks like `val a : int = 3 + 4`.

We can declare *types* too. This is useful when types get *too* big, in such cases we can name types with, for example, `type triple_of_ints = int * int * int`. This is called abbreviating types, since where a `triple_of_ints` is used, a value of type `int * int * int` can be used, and vice versa. Using annotation with this can be used to force the type of this abbreviation, `val a : triple_of_ints = (3, 3, 3)`.

New ways to create custom datatypes: `datatype` and `abstype`. *Deep breaths* . Here are some `datatype` declarations:
```sml
> datatype color = red | green | blue;
> datatype int_or_real = I of int | R of real;
> datatype shape = circle of real | rectangle of real * real | triangle real * real * real;
> datatype list_implementation = Empty | Cons of 'a * 'a list_implementation; (* Note that this is recursive *)
(* They kind of resemble Context Free Grammar *)
```
And here is how one might use these (note that `case` is explained later on but it's similar to *switch-case* statements from other languages like *C* with some differences):
```sml
> val some_color = blue;
> some_color = red; (* Results in false *)
> some_color = blue; (* Results in true *)
> case some_color of red => "BLOOD!" | green => "PLANTS!!" | blue => "MEOW!!!"; (* Results in MEOW!!! *)

...

> val circle1 = circle(5.0);
> val rect1 = rectangle(3.0, 4.0);
> case rect1 of circle(r) => 3.14159 * r * r | rectangle(w, h) => w * h | triangle(b, h) => 0.5 * b * h; (* Gives area of the shape rect1 is -- in this case, 12 *)  

...

> val five_primes_list = Cons(2, Cons(3, Cons(5, Cons(7, Cons(11, Empty))))))
(* Now you can perhaps create functions to operate on this list with the help of case *)
```
Now time to understand what all this means. The structure seems to be `datatype typename = Constructor1 of arguments | ... | ConstructorN of arguments`, where `Constructor1` is one way to make values of `typename`, same with other constructor functions. They can have no arguments as seen in the `color` datatype created above, or may have arguments as seen in the rest of the datatypes. Arguments are specified after the `of` keyword. Also this `|` is not the *OR* operator. So, basically datatype in a mechanism to define new types where you specify the different forms that values of that type can be in. Each for is called a constructor, and constructors are actually functions that create values of the datatype you created. For the `color` datatype above, we basically say to SML, *"Give me a new type called `color`, and there are exactly three ways to create a value of this type: by calling `red`, by calling `blue`, and by calling `green`, all with no arguments."* And here the `red`, `green`, `blue` can be thought of as values of type `color`, but they really behave as constructor functions. For the `shape` datatype, we say, *"Now I want another type called `shape`, with ways to construct being: call `circle` with one real number, call `rectangle` with two real numbers, and so on."* And then SML generates these constructor functions with `circle` of type `real -> shape` , `rectangle` of type `real * real -> shape`, and so on. The value you pass is remembered when constructing a value of the datatype you created. And then pattern matching with `case` allows you to determine which constructor was used and also to extract the data passed to the constructor.

An analogy for, say the  `shape` datatype, from *C/C++*'s combination of *struct*, *union*, and *enum* would be:
```cpp
enum shape_type { CIRCLE, RECTANGLE, TRIANGLE };

// datatype shape = circle of real | rectangle of real * real | ... is declaring this "circle" that is both a type tag (like enum) and a constructor function which has the data. Same for "rectangle" and other constructors
struct shape
{
	shape_type type;
	union
	{
		struct { double radius; } circle;
		struct { double width, height; } rectangle;
		struct { double base, height; } triangle;
	}
};

int main()
{
	shape s = {CIRCLE, {.circle = {5.0}}};
	...
}
```

Now the `abstype` or abstract type. `abstype` is a way to define types similar to `datatype`, but the additional feature is that it allows us to hide the internal details of the `datatype` and only expose certain operations that are specified in the `with end` block. The difference between `datatype` and `abstype` is transparency versus encapsulation. With `datatype`, all constructors are visible and anyone can pattern match on its values. With `abstype`, the internal structure is hidden and users must go through the provided *interface* So, `datatype` is similar to `struct` from *C* that has public members, while `abstype` is similar to `class` in *C++* where there can be private members and some defined methods to manipulate those private members in the allowed way by the programmer of the class. Kind of dumb, this private thing, this abstraction or encapsulation, but it exists to enforce an extreme high level of safety, meaning access to the internals of the value of the type is carefully controlled. But apparently, this gives control over how your type is used — you can prevent invalid operations and even change the internal representation later without breaking code that uses your type. In large-scale programs, module system, which provides more flexible abstract type, is used. The syntax is:
```sml
> abstype typename = datatype_definition
with operation_definitions
end

(* Example: Defining a stack type using abstype *)
(* Note that this is recursive, similar to the list_implementation *)
> abstype 'a stack = Empty | Push of 'a * 'a stack
with
	val empty = Empty
	fun push(x, s) = Push(x, s)
	fun pop(Empty) = raise Empty |
		pop(Push(x, s)) = (x ,s)
end
```
Here, the part `abstype 'a stack = Empty | Push of 'a * 'a stack` defines the internal representation — either a stack is `Empty` (representing an empty stack) or `Push` containing an element of type `'a ` and another stack — `Push(5, Push(3, Empty))` represents a stack with 5 on top and 3 underneath. The `with` clause defines the operations that outside code can use. The `val empty = Empty` creates a constant called `empty`, representing an empty stack. The `push` function here takes an element and an existing stack, then returns a new stack with the element added on top, by using the `Push(x, s)` constructor. The `pop` function removes the top element and returns a pair containing the top element and the remaining stack — it uses pattern matching on the internal structure: if the stack is `Empty`, raise an exception (since popping from an empty stack isn't allowed); if the stack is of the form `Push(x, s)`, return the pair `(x, s)`, where `x` is the top element and `s` is the rest of the stack. For this stack, since it is an `abstype`, you can't directly use `Empty` or `Push` or pattern match on stack values. You can only use the defined operations. You would create an empty stack first using `empty`, then `push` and `pop` elements from it, nothing more, since that is what is defined in the `with` clause.

### Pattern matching

The tuples, the records, the datatypes, all these are about building, combining things to make bigger structures. Pattern does the opposite: it takes apart what was constructed to get the things that made these structures, such as how `case` was used in previous examples. A pattern is **a partial specification of the form of a data element**, whatever that means. In the usage of `case` on the `shape` datatype, the `r` for `circle`, the `w` and `h` for `rectangle`, the `b` and `h` for the triangle, these were the partial specifications, where these just act as placeholders for the actual value passed before the `case` is executed. Pattern matching just combines two operations into one: testing what kind of structure a *thing* is and extracting the data from that structure.

```sml
> val (x, y) = (4, 5); (* Output is `val x = 4 : int` and `val y = 5 : int` *)
> val (x, y) = (3, 4, 5); (* Gives a pattern and expression not agreeing Error *)
> val (3, x) = (3, 5); (* Output is `val x = 5 : int` *)
> val (4, x) = (3, 5); (* Another Error since pattern does not match *)
```
Here, `(x, y)` is a pattern with pattern variables `x` and `y`. It is matched by the tuple `(4, 5)` but not by `(3, 4, 5)`. `(3, x)` and `(4, x)` patterns contain constants or literals (literals for types that allow equality are allowed in patterns). Note that matching a pattern is causing bindings (as shown in the comments). As seen above, the former matches with `(3, 5)` but the latter does not. Here's an arbitrarily complicated pattern:
```sml
> val (x, _, ((3, a), b)) = ({i = 10, j = 10}, (3, 4, 5), ((3, true), false));
(* Output is *)
(* `val a = true : bool` *)
(* `val b = false : bool` *)
(* `val x = {i = 10, j = 10} : {i : int, j : int}` *)
```
Here, the pattern matches, and the variables `a`, `b`, and `x` get bound. Note that `_` is a wildcard which means **"I don't care what's here, just ignore it."** It always matches and caused not binding. Keep in mind order for tuples is important but not for records. Here's what pattern matching for records looks like:
```sml
> val {first = x, second = y} = {first = 3, second = 4};
(* Output is *)
(* val x = 3 : int *)
(* val y = 4 : int *)
(* Output will be same for {second = y, first = x} *)
> val {first, second} = {first = 3, second = 4};
(* This is an abbreviation, we omit the binding variable *)
(* In this case the name of fields are used as binding name *)
(* Output is *)
(* val first = 3 : int *)
(* val second = 4 : int *)
> val {second = y, ...} = {first = 3, second = 4};
(* Ellipses notation to match a part of a record -- other fields may be present but we don't care *)
(* For this to work, the type checking engine needs to know the full type of the record being matched *)
(* Output is *)
(* val y = 4 : int *)
```
Now for the `datatype`. We can use data constructors in patterns, which are matched by a value which has been constructed by the corresponding constructor. Recall `datatype int_or_real = I of int | R of real`. A match failure in this case is raised by attempting to match a value with the wrong constructor or with the wrong value.
```sml
> val a = I(3);  (* val a = I 3 : int_or_real *)
> val (I i) = a; (* val i = 3 : int *)
> val (R i) = a; (* Error *)
> val (I 2) = a; (* Error *)
> val (I 3) = a; (* No output *)
```
Pattern matching in `let` expressions:
```sml
> let val (x, y) = (4, 5) in x + y end; (* val it = 9 : int *)
```

The `case` expression. It allows to match an expression on many patterns, and then evaluate another expression based on the matching. It was used before when `datatype` was introduces, to show how they would be used. Below is it's syntax along with some examples:
```sml
case exp
	of pattern_1 => exp_1
	|  pattern_2 => exp_2
		...
	|  pattern_n => exp_n
```
The means: evaluate `exp`, then attempt to match it to one of the patterns, in the given order. When a successful match occurs, variables in the pattern are bound to the matched values, and finally the corresponding expression is evaluated, which gives the result of the overall case expression. Some Examples:
```sml
case x
	of 0 => "zero"
	|  1 => "one"
	|  _ => "out of range" (* last pattern here is a catch-all, since it always succeeds. *)

(* This one returns the first non-zero element of a pair of integers. Here order of the patterns is important. If the first pattern matches, then the first non-zero cannot appear in the first position. Conversely, if the first pattern does not match, its first element cannot be zero, and we return it. *)
case x
	of (0, x) => x
	|  (x, _) => x

(* On the int_or_real: *)
case x
	of I _ => "integer"
	|  R _ => "real"
```
Note that SML gives a compile-time warning that a pattern is incomplete if it doesn't cover all cases. At runtime, if an unmatched expression comes, an exceptions is raised. Unreachable patterns are called *redundant*, in which case an error is reported. Examples:
```sml
case x
	of _ => 0
	 | _ => 1 (* Will never match because first pattern will always match *)

case x
	of (_, 0) => 0
	 | (_, x) => x
	 | (0, _) => 1 (* Will never match because every pair of integers will match 1st or 2nd patterns *)
```
Finally, it's possible to match a value and decompose it further at the same time in a pattern with `x as pattern`. For example:
```sml
> val (x as (y, z), w) = ((3, 4), 5);
(* Output is *)
(* val x = (3, 4) : int * int *)
(* val y = 3 : int *)
(* val z = 4 : int *)
(* val w = 5 : int *)
```