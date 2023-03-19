include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "10nn.mm"
include "numltc.mm"
include "dfdec10.mm"
include "3brtr4i.mm"

theorem decltc
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume declt.a: |- A e. NN0
  assume declt.b: |- B e. NN0
  assume decltc.c: |- C e. NN0
  assume decltc.d: |- D e. NN0
  assume decltc.s: |- C < ; 1 0
  assume decltc.l: |- A < B


  assert |- ; A C < ; B D

  proof
    c1
    cc0
    cdc
    #
    cA
    cmul
    co
    cC
    caddc
    co
    @0
    cB
    cmul
    co
    cD
    caddc
    co
    cA
    cC
    cdc
    cB
    cD
    cdc
    clt
    cA
    cB
    cC
    cD
    @0
    10nn
    declt.a
    declt.b
    decltc.c
    decltc.d
    decltc.s
    decltc.l
    numltc
    cA
    cC
    dfdec10
    cB
    cD
    dfdec10
    3brtr4i
end
