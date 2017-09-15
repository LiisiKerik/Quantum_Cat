`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
~/
  Hello World!
  ~/
    Testing whether nested multiline comments work...
  /~
/~
Def H2{n} : Arr[Qbit]{n} -> Arr[Qbit]{n} = Map[Qbit, Qbit]{n}(H)
Def Main : Creg = Random'
Def Random'{n} : Creg{n} = Measure{n}(Uniform1{n})
Def Take1{n} : Arr[Qbit]{n} = Lift[Qbit]{n}(Take)
Def Uniform1{n} : Arr[Qbit]{n} = Lift[Qbit]{n}(Uniform)
`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````