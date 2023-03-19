include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "ctop.mm"
include "wcel.mm"
include "wceq.mm"
include "retop.mm"
include "uniretop.mm"
include "restid.mm"
include "ax-mp.mm"
include "cv.mm"
include "cicc.mm"
include "wss.mm"
include "wral.mm"
include "iccssre.mm"
include "rgen2a.mm"
include "wb.mm"
include "ssid.mm"
include "reconn.mm"
include "mpbir.mm"
include "eqeltrri.mm"

theorem retopconn
  let vx: setvar x
  let vy: setvar y


  assert |- ( topGen ` ran (,) ) e. Conn

  proof
    cioo
    crn
    ctg
    cfv
    #
    cr
    crest
    co
    #
    @0
    cconn
    @0
    ctop
    wcel
    @1
    @0
    wceq
    retop
    @0
    ctop
    cr
    uniretop
    restid
    ax-mp
    @1
    cconn
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cicc
    co
    cr
    wss
    #
    vy
    cr
    wral
    vx
    cr
    wral
    #
    @5
    vx
    vy
    cr
    @3
    @4
    iccssre
    rgen2a
    cr
    cr
    wss
    @2
    @6
    wb
    cr
    ssid
    vx
    vy
    cr
    reconn
    ax-mp
    mpbir
    eqeltrri
end
