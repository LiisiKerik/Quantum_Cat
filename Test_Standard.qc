`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
Load Algebra.qc
Load Standard.qc
Def Test_Add_Qbit(_ : Unit) : Creg = Measure (Unsafe_Array 1 (_ -> Add_Qbit (Take Unit) (Take Unit)))
Def Test_Add_Qint(x : Int) : Creg = Measure (qint (Add_Qint_Unsafe (Take_Qint_Unsafe x) (Take_Qint_Unsafe x)))
Def Test_Uniform_Qbit(_ : Unit) : Creg = Measure (Unsafe_Array 1 (_ -> Uniform_Qbit Unit))
Def Test_Uniform_Qint(x : Int) : Creg = Measure (qint (Uniform_Qint_Unsafe x))
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````