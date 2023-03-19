include "cdc.mm"
include "deccl.mm"
include "decltc.mm"

theorem 3decltc
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
  assume 3decltc.1: |- C < ; 1 0
  assume 3decltc.2: |- E < ; 1 0


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
    3decltc.2
    cA
    cB
    cC
    cD
    3decltc.a
    3decltc.b
    3decltc.c
    3decltc.d
    3decltc.1
    3decltc.3
    decltc
    decltc
end
