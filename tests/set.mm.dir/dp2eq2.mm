include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cdp2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "df-dp2.mm"
include "3eqtr4g.mm"

theorem dp2eq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> _ C A = _ C B )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    cC
    cB
    @1
    cdiv
    co
    #
    caddc
    co
    cC
    cA
    cdp2
    cC
    cB
    cdp2
    @0
    @2
    @3
    cC
    caddc
    cA
    cB
    @1
    cdiv
    oveq1
    oveq2d
    cC
    cA
    df-dp2
    cC
    cB
    df-dp2
    3eqtr4g
end
