`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
Load Algebra.qc
Load Standard.qc
Def Random_Qbit(_ : Unit) : Creg = Measure (Unsafe_Array 1 (_ -> Uniform_Qbit Unit))
Def Random_Qint(x : Int) : Maybe Creg = Map_Maybe (Map_Function Measure qint) (Uniform_Qint x)
Def Random_Qint_Unsafe(x : Int) : Creg = Unsafe_Maybe (Random_Qint x)
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````