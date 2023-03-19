include "wceq.mm"
include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdc.mm"
include "oveq2.mm"
include "dfdecOLD.mm"
include "3eqtr4g.mm"

theorem deceq2OLD
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ; C A = ; C B )

  proof
    cA
    cB
    wceq
    c10
    cC
    cmul
    co
    #
    cA
    caddc
    co
    @0
    cB
    caddc
    co
    cC
    cA
    cdc
    cC
    cB
    cdc
    cA
    cB
    @0
    caddc
    oveq2
    cC
    cA
    dfdecOLD
    cC
    cB
    dfdecOLD
    3eqtr4g
end
