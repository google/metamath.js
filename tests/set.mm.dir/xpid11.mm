include "cxp.mm"
include "wceq.mm"
include "cdm.mm"
include "dmeq.mm"
include "dmxpid.mm"
include "3eqtr3g.mm"
include "xpeq12.mm"
include "anidms.mm"
include "impbii.mm"

theorem xpid11
  let cA: class A
  let cB: class B


  assert |- ( ( A X. A ) = ( B X. B ) <-> A = B )

  proof
    cA
    cA
    cxp
    #
    cB
    cB
    cxp
    #
    wceq
    #
    cA
    cB
    wceq
    #
    @2
    @0
    cdm
    @1
    cdm
    cA
    cB
    @0
    @1
    dmeq
    cA
    dmxpid
    cB
    dmxpid
    3eqtr3g
    @3
    @2
    cA
    cB
    cA
    cB
    xpeq12
    anidms
    impbii
end
