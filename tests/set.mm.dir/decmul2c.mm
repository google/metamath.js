include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "caddc.mm"
include "10nn0.mm"
include "dfdec10.mm"
include "eqtri.mm"
include "nummul2c.mm"
include "eqtr4i.mm"

theorem decmul2c
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
  assume decmul2c.c: |- ( ( P x. A ) + E ) = C
  assume decmul2c.2: |- ( P x. B ) = ; E D


  assert |- ( P x. N ) = ; C D

  proof
    cP
    cN
    cmul
    co
    c1
    cc0
    cdc
    #
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
    @0
    cE
    cN
    10nn0
    decmul1.p
    decmul1.a
    decmul1.b
    cN
    cA
    cB
    cdc
    @0
    cA
    cmul
    co
    cB
    caddc
    co
    decmul1.n
    cA
    cB
    dfdec10
    eqtri
    decmul1.0
    decmul1c.e
    decmul2c.c
    cP
    cB
    cmul
    co
    cE
    cD
    cdc
    @0
    cE
    cmul
    co
    cD
    caddc
    co
    decmul2c.2
    cE
    cD
    dfdec10
    eqtri
    nummul2c
    cC
    cD
    dfdec10
    eqtr4i
end
