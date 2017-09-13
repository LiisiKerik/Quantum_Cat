`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
Algebraic Either[A : *, B : *](Left(A), Right(B))
Struct Pair[A : *, B : *](First : A, Second : B)
Def Add_Array[A : *](Add_A : Function A (Function A A), x : Array A, y : Array A) : Maybe (Array A) = Zip_Array Add_A x y
Def Add_Logical(x : Logical, y : Logical) : Logical = Match x {
  False -> y,
  True -> Not y}
Def Apply_Array[A : *, B : *](x : Array (Function A B), y : Array A) : Maybe (Array B) =
  Match Equal_Int (Length x) (Length y) {
    False -> Nothing,
    True -> Array (Length x) (z -> (Unsafe_Index x z) (Unsafe_Index y z))}
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
Def Lift_Array[A : *](x : Int, y : A) : Maybe (Array A) = Array x (Lift_Function y)
Def Lift_Either[A : *, B : *] : Function B (Either A B) = Right
Def Lift_Function[A : *, B : *](x : A, _ : B) : A = x
Def Map_Array[A : *, B : *](f : Function A B, x : Array A) : Array B = Unsafe_Array (Length x) (y -> f (Unsafe_Index x y))
Def Map_Either[A : *, B : *, C : *](f : Function A B, x : Either C A) : Either C B = Match x {
  Left y -> Left y,
  Right y -> Right (f y)}
Def Map_Function[A : *, B : *, C : *](f : Function A B, g : Function C A, x : C) : B = f (g x)
Def Map_Pair[A : *, B : *, C : *](f : Function A B, x : Pair C A) : Pair C B = Pair (First x) (f (Second x))
Def Minus[A : *](Add_A : Function A (Function A A), Negate_A : Function A A, x : A, y : A) : A = Add_A x (Negate_A y)
Def Multiply_Logical(x : Logical, y : Logical) : Logical = Match x {
  False -> False,
  True -> y}
Def Not(x : Logical) : Logical = Match x {
  False -> True,
  True -> False}
Def Not_Equal[A : *](Equal_A : Function A (Function A Logical), x : A, y : A) : Logical = Not (Equal_A x y)
Def Unsafe_Array[A : *](x : Int, f : Function Int A) : Array A = Unsafe_Maybe (Array x f)
Def Unsafe_Either[A : *, B : *](x : Either A B) : B = Match x {
  Left -> Crash,
  Right y -> y}
Def Unsafe_Index[A : *](x : Array A, y : Int) : A = Unsafe_Maybe (Index x y)
Def Unsafe_Lift_Array[A : *](x : Int, y : A) : Array A = Unsafe_Maybe (Lift_Array x y)
Def Unsafe_Maybe[A : *](x : Maybe A) : A = Match x {
  Nothing -> Crash,
  Wrap y -> y}
Def Zero[A : *](Convert_A : Function Int A) : A = Convert_A 0
Def Zip_Array[A : *, B : *, C : *](f : Function A (Function B C), x : Array A) : Function (Array B) (Maybe (Array C)) =
  Apply_Array (Map_Array f x)
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````