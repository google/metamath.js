include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdc.mm"
include "clt.mm"
include "10nnOLD.mm"
include "numltc.mm"
include "dfdecOLD.mm"
include "3brtr4i.mm"

theorem decltcOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume declt.a: |- A e. NN0
  assume declt.b: |- B e. NN0
  assume decltcOLD.3: |- C e. NN0
  assume decltcOLD.4: |- D e. NN0
  assume decltcOLD.5: |- C < 10
  assume decltcOLD.6: |- A < B


  assert |- ; A C < ; B D

  proof
    c10
    cA
    cmul
    co
    cC
    caddc
    co
    c10
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
    c10
    10nnOLD
    declt.a
    declt.b
    decltcOLD.3
    decltcOLD.4
    decltcOLD.5
    decltcOLD.6
    numltc
    cA
    cC
    dfdecOLD
    cB
    cD
    dfdecOLD
    3brtr4i
end
