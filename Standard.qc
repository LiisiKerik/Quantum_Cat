`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
Load Algebra.qc
Struct Qint(qint : Array Qbit)
Def Add_Qbit(x : Qbit, y : Qbit) : Qbit = CX y (CX x (Take Unit))
Def Add_Qint(x : Qint, y : Qint) : Maybe Qint = Match Equal_Int (Length (qint x)) (Length (qint y)) {
  False -> Nothing,
  True -> Wrap (Qint (Add_Qint' 0 (Length (qint x)) (Take Unit) (qint x) (qint y)))}
Def Add_Qint'(i : Int, n : Int, carry : Qbit, x : Array Qbit, y : Array Qbit) : Array Qbit =
Def Add_Qint_Unsafe(x : Qint, y : Qint) : Qint = Unsafe_Maybe (Add_Qint x y)
Def Take_Qint(x : Int) : Maybe Qint = Map_Maybe Qint (Array x (_ -> Take Unit))
Def Take_Qint_Unsafe(x : Int) : Qint = Unsafe_Maybe (Take_Qint x)
Def Uniform_Qbit(_ : Unit) : Qbit = H (Take Unit)
Def Uniform_Qint(x : Int) : Maybe Qint = Map_Maybe (y -> Qint (Map_Array H (qint y))) (Take_Qint x)
Def Uniform_Qint_Unsafe(x : Int) : Qint = Unsafe_Maybe (Uniform_Qint x)
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````