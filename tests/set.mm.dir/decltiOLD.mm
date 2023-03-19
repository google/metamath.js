include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdc.mm"
include "clt.mm"
include "10nnOLD.mm"
include "numlti.mm"
include "dfdecOLD.mm"
include "breqtrri.mm"

theorem decltiOLD
  let cA: class A
  let cB: class B
  let cC: class C
  assume decltiOLD.1: |- A e. NN
  assume decltiOLD.2: |- B e. NN0
  assume decltiOLD.3: |- C e. NN0
  assume decltiOLD.4: |- C < 10


  assert |- C < ; A B

  proof
    cC
    c10
    cA
    cmul
    co
    cB
    caddc
    co
    cA
    cB
    cdc
    clt
    cA
    cB
    cC
    c10
    10nnOLD
    decltiOLD.1
    decltiOLD.2
    decltiOLD.3
    decltiOLD.4
    numlti
    cA
    cB
    dfdecOLD
    breqtrri
end
