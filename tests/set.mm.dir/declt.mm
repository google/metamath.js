include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "10nn.mm"
include "numlt.mm"
include "dfdec10.mm"
include "3brtr4i.mm"

theorem declt
  let cA: class A
  let cB: class B
  let cC: class C
  assume declt.a: |- A e. NN0
  assume declt.b: |- B e. NN0
  assume declt.c: |- C e. NN
  assume declt.l: |- B < C


  assert |- ; A B < ; A C

  proof
    c1
    cc0
    cdc
    #
    cA
    cmul
    co
    #
    cB
    caddc
    co
    @1
    cC
    caddc
    co
    cA
    cB
    cdc
    cA
    cC
    cdc
    clt
    cA
    cB
    cC
    @0
    10nn
    declt.a
    declt.b
    declt.c
    declt.l
    numlt
    cA
    cB
    dfdec10
    cA
    cC
    dfdec10
    3brtr4i
end
