`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
Load Algebra.qc
Load Standard.qc
Def Test_Add_Qbit(_ : Unit) : Creg = Measure (Unsafe_Array 1 (_ -> Add_Qbit (Take Unit) (Take Unit)))
Def Test_Uniform_Qbit(_ : Unit) : Creg = Measure (Unsafe_Array 1 (_ -> Uniform_Qbit Unit))
Def Test_Uniform_Qint(x : Int) : Creg = Measure (qint (Unsafe_Maybe (Uniform_Qint x)))
`Unsafe_Maybe (Map_Maybe (Map_Function Measure qint) (Uniform_Qint x))
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````