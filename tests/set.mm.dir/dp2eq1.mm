include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cdp2.mm"
include "oveq1.mm"
include "df-dp2.mm"
include "3eqtr4g.mm"

theorem dp2eq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> _ A C = _ B C )

  proof
    cA
    cB
    wceq
    cA
    cC
    c1
    cc0
    cdc
    cdiv
    co
    #
    caddc
    co
    cB
    @0
    caddc
    co
    cA
    cC
    cdp2
    cB
    cC
    cdp2
    cA
    cB
    @0
    caddc
    oveq1
    cA
    cC
    df-dp2
    cB
    cC
    df-dp2
    3eqtr4g
end
