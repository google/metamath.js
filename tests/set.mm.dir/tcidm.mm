include "ctc.mm"
include "cfv.mm"
include "wss.mm"
include "wtr.mm"
include "ssid.mm"
include "tctr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "fvex.mm"
include "tcmin.mm"
include "ax-mp.mm"
include "mp2an.mm"
include "tcid.mm"
include "eqssi.mm"

theorem tcidm
  let cA: class A


  assert |- ( TC ` ( TC ` A ) ) = ( TC ` A )

  proof
    cA
    ctc
    cfv
    #
    ctc
    cfv
    #
    @0
    @0
    @0
    wss
    #
    @0
    wtr
    #
    @1
    @0
    wss
    #
    @0
    ssid
    cA
    tctr
    @0
    cvv
    wcel
    #
    @2
    @3
    wa
    @4
    wi
    cA
    ctc
    fvex
    #
    @0
    @0
    cvv
    tcmin
    ax-mp
    mp2an
    @5
    @0
    @1
    wss
    @6
    @0
    cvv
    tcid
    ax-mp
    eqssi
end
