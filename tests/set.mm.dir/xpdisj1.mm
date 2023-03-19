include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "xpeq1.mm"
include "inxp.mm"
include "0xp.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"

theorem xpdisj1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A i^i B ) = (/) -> ( ( A X. C ) i^i ( B X. D ) ) = (/) )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    @0
    cC
    cD
    cin
    #
    cxp
    c0
    @1
    cxp
    #
    cA
    cC
    cxp
    cB
    cD
    cxp
    cin
    c0
    @0
    c0
    @1
    xpeq1
    cA
    cC
    cB
    cD
    inxp
    @2
    c0
    @1
    0xp
    eqcomi
    3eqtr4g
end
