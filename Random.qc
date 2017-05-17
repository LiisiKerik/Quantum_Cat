`````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````````
~/
Synonym(Cbits{n}, Arr[Cbit]{n})
Synonym(Qbits{n}, Arr[Qbit]{n})
/~
Def HH{n}(x : Arr[Qbit]{n}) : Arr[Qbit]{n} = Map[Qbit, Qbit]{n}(H, x)
Def Id[U](x : U) : U = x
Def Main : Arr[Cbit]{4} = Random'{4}
Def Measure'{n}(x : Arr[Qbit]{n}) : Arr[Cbit]{n} = Map[Qbit, Cbit]{n}(Measure, x)
Def Random : Cbit = Measure(Uniform)
Def Random'{n} : Arr[Cbit]{n} = Lift[Cbit]{n}(Random)
Def Take'{n} : Arr[Qbit]{n} = Lift[Qbit]{n}(Take)
Def Uniform : Qbit = H(Take)
Def Uniform'{n} : Arr[Qbit]{n} = Lift[Qbit]{n}(Uniform)
~/
  Hello World!
  ~/
    Testing whether nested multiline comments work...
  /~
/~