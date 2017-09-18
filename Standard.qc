`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
Load Algebra.qc
Struct Qint(qint : Array Qbit)
Def H_Qint(x : Qint) : Qint = Qint (Map_Array H (qint x))
Def Take_Qint(x : Int) : Maybe Qint = Map_Maybe Qint (Array x (_ -> Take Unit))
Def Take_Qint_Unsafe(x : Int) : Qint = Unsafe_Maybe (Take_Qint x)
Def Uniform_Qbit(_ : Unit) : Qbit = H (Take Unit)
Def Uniform_Qint(x : Int) : Maybe Qint = Map_Maybe H_Qint (Take_Qint x)
Def Uniform_Qint_Unsafe(x : Int) : Qint = Unsafe_Maybe (Uniform_Qint x)
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````