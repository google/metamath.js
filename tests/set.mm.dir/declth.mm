include "le9lt10.mm"
include "decltc.mm"

theorem declth
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume declt.a: |- A e. NN0
  assume declt.b: |- B e. NN0
  assume declth.c: |- C e. NN0
  assume declth.d: |- D e. NN0
  assume declth.e: |- C <_ 9
  assume declth.l: |- A < B


  assert |- ; A C < ; B D

  proof
    cA
    cB
    cC
    cD
    declt.a
    declt.b
    declth.c
    declth.d
    cC
    declth.c
    declth.e
    le9lt10
    declth.l
    decltc
end
