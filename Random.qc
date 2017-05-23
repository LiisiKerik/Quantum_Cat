`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
~/
  Hello World!
  ~/
    Testing whether nested multiline comments work...
  /~
/~
Def H1{n}(x : Arr[Qbit]{n}) : Arr[Qbit]{n} = Map[Qbit, Qbit]{n}(H, x)
Def H2{n} : Arr[Qbit]{n} -> Arr[Qbit]{n} = Map[Qbit, Qbit]{n}(H)
Def Id[U](x : U) : U = x
Def Main : Creg{4} = Random'{4}
Def Random'{n} : Creg{n} = Measure{n}(Uniform1{n})
Def Take1{n} : Arr[Qbit]{n} = Lift[Qbit]{n}(Take)
Def Uniform : Qbit = H(Take)
Def Uniform1{n} : Arr[Qbit]{n} = Lift[Qbit]{n}(Uniform)
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````