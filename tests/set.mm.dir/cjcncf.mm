include "ccj.mm"
include "cc.mm"
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
include "cjf.mm"
include "cjcn2.mm"
include "rgen2.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "ssid.mm"
include "elcncf2.mm"
include "mp2an.mm"
include "mpbir2an.mm"

theorem cjcncf
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- * e. ( CC -cn-> CC )

  proof
    ccj
    cc
    cc
    ccncf
    co
    wcel
    #
    cc
    cc
    ccj
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
    ccj
    cfv
    @3
    ccj
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
    cjf
    @4
    vx
    vy
    cc
    crp
    vy
    vz
    vw
    @3
    cjcn2
    rgen2
    cc
    cc
    wss
    #
    @6
    @0
    @1
    @5
    wa
    wb
    cc
    ssid
    #
    @7
    vx
    vy
    vz
    vw
    cc
    cc
    ccj
    elcncf2
    mp2an
    mpbir2an
end
