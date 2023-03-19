include "cdc.mm"
include "deccl.mm"
include "decltcOLD.mm"

theorem 3decltcOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume 3decltcOLD.a: |- A e. NN0
  assume 3decltcOLD.b: |- B e. NN0
  assume 3decltcOLD.c: |- C e. NN0
  assume 3decltcOLD.d: |- D e. NN0
  assume 3decltcOLD.e: |- E e. NN0
  assume 3decltcOLD.f: |- F e. NN0
  assume 3decltcOLD.1: |- C < 10
  assume 3decltcOLD.2: |- E < 10
  assume 3decltcOLD.3: |- A < B


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
    3decltcOLD.a
    3decltcOLD.c
    deccl
    cB
    cD
    3decltcOLD.b
    3decltcOLD.d
    deccl
    3decltcOLD.e
    3decltcOLD.f
    3decltcOLD.2
    cA
    cB
    cC
    cD
    3decltcOLD.a
    3decltcOLD.b
    3decltcOLD.c
    3decltcOLD.d
    3decltcOLD.1
    3decltcOLD.3
    decltcOLD
    decltcOLD
end
