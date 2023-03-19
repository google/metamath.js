include "cdc.mm"
include "deccl.mm"
include "declth.mm"

theorem 3declth
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume 3decltc.a: |- A e. NN0
  assume 3decltc.b: |- B e. NN0
  assume 3decltc.c: |- C e. NN0
  assume 3decltc.d: |- D e. NN0
  assume 3decltc.e: |- E e. NN0
  assume 3decltc.f: |- F e. NN0
  assume 3decltc.3: |- A < B
  assume 3declth.1: |- C <_ 9
  assume 3declth.2: |- E <_ 9


  assert |- ; ; A C E < ; ; B D F

  proof
    cA
    cC
    cdc
    cB
    cD
    cdc
    cE
    cF
    cA
    cC
    3decltc.a
    3decltc.c
    deccl
    cB
    cD
    3decltc.b
    3decltc.d
    deccl
    3decltc.e
    3decltc.f
    3declth.2
    cA
    cB
    cC
    cD
    3decltc.a
    3decltc.b
    3decltc.c
    3decltc.d
    3declth.1
    3decltc.3
    declth
    declth
end
