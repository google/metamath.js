include "wceq.mm"
include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdc.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "dfdecOLD.mm"
include "3eqtr4g.mm"

theorem deceq1OLD
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ; A C = ; B C )

  proof
    cA
    cB
    wceq
    #
    c10
    cA
    cmul
    co
    #
    cC
    caddc
    co
    c10
    cB
    cmul
    co
    #
    cC
    caddc
    co
    cA
    cC
    cdc
    cB
    cC
    cdc
    @0
    @1
    @2
    cC
    caddc
    cA
    cB
    c10
    cmul
    oveq2
    oveq1d
    cA
    cC
    dfdecOLD
    cB
    cC
    dfdecOLD
    3eqtr4g
end
