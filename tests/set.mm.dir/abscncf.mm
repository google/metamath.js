include "cabs.mm"
include "cc.mm"
include "cr.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "absf.mm"
include "abscn2.mm"
include "rgen2.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "ssid.mm"
include "ax-resscn.mm"
include "elcncf2.mm"
include "mp2an.mm"
include "mpbir2an.mm"

theorem abscncf
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- abs e. ( CC -cn-> RR )

  proof
    cabs
    cc
    cr
    ccncf
    co
    wcel
    #
    cc
    cr
    cabs
    wf
    #
    vw
    cv
    #
    vx
    cv
    #
    cmin
    co
    cabs
    cfv
    vz
    cv
    clt
    wbr
    @2
    cabs
    cfv
    @3
    cabs
    cfv
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    wi
    vw
    cc
    wral
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    cc
    wral
    #
    absf
    @4
    vx
    vy
    cc
    crp
    vy
    vz
    vw
    @3
    abscn2
    rgen2
    cc
    cc
    wss
    cr
    cc
    wss
    @0
    @1
    @5
    wa
    wb
    cc
    ssid
    ax-resscn
    vx
    vy
    vz
    vw
    cc
    cr
    cabs
    elcncf2
    mp2an
    mpbir2an
end
