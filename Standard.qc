`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
Load Algebra.qc
Def Take_Array(x : Int) : Maybe (Array Qbit) = Lift_Array x Take
Def Uniform_Qbit : Qbit = H Take
Def Uniform_Array_Qbit(x : Int) : Maybe (Array Qbit) = Lift_Array x Uniform_Qbit
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````