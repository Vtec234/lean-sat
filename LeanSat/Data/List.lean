import Std.Data.HashSet

def List.union [BEq α] [Hashable α] (xs ys : List α) : List α :=
  let m := xs.foldl (·.insert ·) Std.HashSet.empty
  let (_, ret) := ys.foldl (init := (m, xs))
    fun (m, xys) y => if m.contains y then (m, xys) else (m.insert y, y :: xys)
  ret

def List.splitOn [BEq α] (sep : α) : List α → List (List α) :=
  go [] []
where go (acc : List (List α)) (soFar : List α) : List α → List (List α)
  | [] => if soFar.isEmpty then acc.reverse else (soFar.reverse :: acc).reverse
  | x :: xs => if x == sep then
    if soFar.isEmpty then go acc [] xs
    else go (soFar.reverse :: acc) [] xs
  else
    go acc (x :: soFar) xs