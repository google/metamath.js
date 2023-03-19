include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "10nn.mm"
include "numlti.mm"
include "dfdec10.mm"
include "breqtrri.mm"

theorem declti
  let cA: class A
  let cB: class B
  let cC: class C
  assume declti.a: |- A e. NN
  assume declti.b: |- B e. NN0
  assume declti.c: |- C e. NN0
  assume declti.l: |- C < ; 1 0


  assert |- C < ; A B

  proof
    cC
    c1
    cc0
    cdc
    #
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
    @0
    10nn
    declti.a
    declti.b
    declti.c
    declti.l
    numlti
    cA
    cB
    dfdec10
    breqtrri
end
