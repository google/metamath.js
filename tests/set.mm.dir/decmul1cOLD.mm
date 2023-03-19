include "cmul.mm"
include "co.mm"
include "c10.mm"
include "caddc.mm"
include "cdc.mm"
include "10nn0OLD.mm"
include "dfdecOLD.mm"
include "eqtri.mm"
include "nummul1c.mm"
include "eqtr4i.mm"

theorem decmul1cOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cN: class N
  assume decmul1.p: |- P e. NN0
  assume decmul1.a: |- A e. NN0
  assume decmul1.b: |- B e. NN0
  assume decmul1.n: |- N = ; A B
  assume decmul1.0: |- D e. NN0
  assume decmul1c.e: |- E e. NN0
  assume decmul1c.c: |- ( ( A x. P ) + E ) = C
  assume decmul1c.2: |- ( B x. P ) = ; E D


  assert |- ( N x. P ) = ; C D

  proof
    cN
    cP
    cmul
    co
    c10
    cC
    cmul
    co
    cD
    caddc
    co
    cC
    cD
    cdc
    cA
    cB
    cC
    cD
    cP
    c10
    cE
    cN
    10nn0OLD
    decmul1.p
    decmul1.a
    decmul1.b
    cN
    cA
    cB
    cdc
    c10
    cA
    cmul
    co
    cB
    caddc
    co
    decmul1.n
    cA
    cB
    dfdecOLD
    eqtri
    decmul1.0
    decmul1c.e
    decmul1c.c
    cB
    cP
    cmul
    co
    cE
    cD
    cdc
    c10
    cE
    cmul
    co
    cD
    caddc
    co
    decmul1c.2
    cE
    cD
    dfdecOLD
    eqtri
    nummul1c
    cC
    cD
    dfdecOLD
    eqtr4i
end
