`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
Load Algebra.qc
Struct Qint(qint : Array Qbit)
Def Take_Qint(x : Int) : Maybe Qint = Map_Maybe Qint (Array x (_ -> Take Unit))
Def Take_Qint_Unsafe(x : Int) : Qint = Unsafe_Maybe (Take_Qint x)
Def Uniform_Qbit(_ : Unit) : Qbit = H (Take Unit)
Def Uniform_Qint(x : Int) : Maybe Qint = Map_Maybe (y -> Qint (Map_Array H (qint y))) (Take_Qint x)
Def Uniform_Qint_Unsafe(x : Int) : Qint = Unsafe_Maybe (Uniform_Qint x)
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````