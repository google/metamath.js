include "ccom.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wrel.mm"
include "wss.mm"
include "relco.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "dmcoss.mm"
include "rncoss.mm"
include "xpss12.mm"
include "mp2an.mm"
include "sstri.mm"

theorem cossxp
  let cA: class A
  let cB: class B


  assert |- ( A o. B ) C_ ( dom B X. ran A )

  proof
    cA
    cB
    ccom
    #
    @0
    cdm
    #
    @0
    crn
    #
    cxp
    #
    cB
    cdm
    #
    cA
    crn
    #
    cxp
    #
    @0
    wrel
    @0
    @3
    wss
    cA
    cB
    relco
    @0
    relssdmrn
    ax-mp
    @1
    @4
    wss
    @2
    @5
    wss
    @3
    @6
    wss
    cA
    cB
    dmcoss
    cA
    cB
    rncoss
    @1
    @4
    @2
    @5
    xpss12
    mp2an
    sstri
end
