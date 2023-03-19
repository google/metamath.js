include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdc.mm"
include "clt.mm"
include "10nnOLD.mm"
include "numlt.mm"
include "dfdecOLD.mm"
include "3brtr4i.mm"

theorem decltOLD
  let cA: class A
  let cB: class B
  let cC: class C
  assume declt.a: |- A e. NN0
  assume declt.b: |- B e. NN0
  assume declt.c: |- C e. NN
  assume declt.l: |- B < C


  assert |- ; A B < ; A C

  proof
    c10
    cA
    cmul
    co
    #
    cB
    caddc
    co
    @0
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
    c10
    10nnOLD
    declt.a
    declt.b
    declt.c
    declt.l
    numlt
    cA
    cB
    dfdecOLD
    cA
    cC
    dfdecOLD
    3brtr4i
end
