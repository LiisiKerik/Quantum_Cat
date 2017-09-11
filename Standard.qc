`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
Algebraic Either[A : *, B : *](Left(A), Right(B))
Struct Pair[A : *, B : *](First : A, Second : B)
Def Add_Logical(x : Logical, y : Logical) : Logical = Match x {
  False -> y,
  True -> Not y}
Def Apply_Function[A : *, B : *, C : *](x : Function A (Function B C), y : Function A B, z : A) : C = x z (y z)
Def Convert_Int : Function Int Int = Id
Def Convert_Logical(x : Int) : Logical = Equal_Int (Mod_Int x 2) 1
Def Equal_Either
  [A : *, B : *]
  (Equal_A : Function A (Function A Logical), Equal_B : Function B (Function B Logical), x : Either A B, y : Either A B) :
  Logical =
    Match x {
      Left z -> Match y {
        Left w -> Equal_A z w,
        Right -> False},
      Right z -> Match y {
        Left -> False,
        Right w -> Equal_B z w}}
Def Equal_Maybe[A : *](Equal_A : Function A (Function A Logical), x : Maybe A, y : Maybe A) : Logical = Match x {
  Nothing -> Match y {
    Nothing -> True,
    Wrap -> False},
  Wrap z -> Match y {
    Nothing -> False,
    Wrap w -> Equal_A z w}}
Def Equal_Pair
  [A : *, B : *]
  (Equal_A : Function A (Function A Logical), Equal_B : Function B (Function B Logical), x : Pair A B, y : Pair A B) :
  Logical =
    Multiply_Logical (Equal_A (First x) (First y)) (Equal_B (Second x) (Second y))
Def Id[A : *](x : A) : A = x
Def Identity[A : *](Convert_A : Function Int A) : A = Convert_A 1
Def Lift_Array[A : *](x : Int, y : A) : Array A = Array x (Lift_Function y)
Def Lift_Either[A : *, B : *] : Function B (Either A B) = Right
Def Lift_Function[A : *, B : *](x : A, _ : B) : A = x
Def Minus[A : *](Add_A : Function A (Function A A), Negate_A : Function A A, x : A, y : A) : A = Add_A x (Negate_A y)
Def Multiply_Logical(x : Logical, y : Logical) : Logical = Match x {
  False -> False,
  True -> y}
Def Not(x : Logical) : Logical = Match x {
  False -> True,
  True -> False}
Def Not_Equal[A : *](Equal_A : Function A (Function A Logical), x : A, y : A) : Logical = Not (Equal_A x y)
Def Zero[A : *](Convert_A : Function Int A) : A = Convert_A 0
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````