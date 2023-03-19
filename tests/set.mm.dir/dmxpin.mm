include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "inxp.mm"
include "dmeqi.mm"
include "dmxpid.mm"
include "eqtri.mm"

theorem dmxpin
  let cA: class A
  let cB: class B


  assert |- dom ( ( A X. A ) i^i ( B X. B ) ) = ( A i^i B )

  proof
    cA
    cA
    cxp
    cB
    cB
    cxp
    cin
    #
    cdm
    cA
    cB
    cin
    #
    @1
    cxp
    #
    cdm
    @1
    @0
    @2
    cA
    cA
    cB
    cB
    inxp
    dmeqi
    @1
    dmxpid
    eqtri
end
