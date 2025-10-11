/- Printing a cool tree
 -  *
 - ***
 -*****
 -  *
 -  *
 -/

-- Returns a 2D Array containing strings
-- Each row and column has characters that make up the tree
-- The inner arrays are the rows or lines of the tree
def tree (rows : Nat) :=
  -- Upper part (pyramid-like)
  (List.range rows).map (λ i =>
    (List.range (2*rows - 1)).map (
      λ j => if j < (rows-1) - i || j > (rows-1) + i then " " else "*")
  ) ++
  -- Lower part (the trunk - height is one less than the upper part for aesthetics >.<)
  (List.range (rows - 1)).map (
    λ _i => (List.range (2*(rows) - 1)).map (
      λ j => if j == rows-1 then "*" else " ")
  )

-- Used to convert a 2D array of strings to a single string with multiple lines
def list_list_str_to_strln (list : List (List String)) : String :=
  String.intercalate "\n" (List.map (λ l => String.intercalate "" l) list)

-- `IO.println` is used since otherwise `\n` isn't rendered properly
#eval IO.println (list_list_str_to_strln (tree 10))
