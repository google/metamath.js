include "cim.mm"
include "cc.mm"
include "cr.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "imf.mm"
include "imcn2.mm"
include "rgen2.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "ssid.mm"
include "ax-resscn.mm"
include "elcncf2.mm"
include "mp2an.mm"
include "mpbir2an.mm"

theorem imcncf
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Im e. ( CC -cn-> RR )

  proof
    cim
    cc
    cr
    ccncf
    co
    wcel
    #
    cc
    cr
    cim
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
    cim
    cfv
    @3
    cim
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
    imf
    @4
    vx
    vy
    cc
    crp
    vy
    vz
    vw
    @3
    imcn2
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
    cim
    elcncf2
    mp2an
    mpbir2an
end
