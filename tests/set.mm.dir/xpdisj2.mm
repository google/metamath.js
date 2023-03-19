include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "xpeq2.mm"
include "inxp.mm"
include "xp0.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"

theorem xpdisj2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A i^i B ) = (/) -> ( ( C X. A ) i^i ( D X. B ) ) = (/) )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    cC
    cD
    cin
    #
    @0
    cxp
    @1
    c0
    cxp
    #
    cC
    cA
    cxp
    cD
    cB
    cxp
    cin
    c0
    @0
    c0
    @1
    xpeq2
    cC
    cA
    cD
    cB
    inxp
    @2
    c0
    @1
    xp0
    eqcomi
    3eqtr4g
end
