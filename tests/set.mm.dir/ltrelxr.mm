include "clt.mm"
include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "cltrr.mm"
include "wbr.mm"
include "w3a.mm"
include "copab.mm"
include "cmnf.mm"
include "csn.mm"
include "cun.mm"
include "cpnf.mm"
include "cxp.mm"
include "cxr.mm"
include "df-ltxr.mm"
include "wa.mm"
include "df-3an.mm"
include "opabbii.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "wss.mm"
include "ressxr.mm"
include "cpr.mm"
include "snsspr2.mm"
include "ssun2.mm"
include "df-xr.mm"
include "sseqtr4i.mm"
include "unssi.mm"
include "snsspr1.mm"
include "xpss12.mm"
include "mp2an.mm"

theorem ltrelxr
  let vx: setvar x
  let vy: setvar y


  assert |- < C_ ( RR* X. RR* )

  proof
    clt
    vx
    cv
    #
    cr
    wcel
    #
    vy
    cv
    #
    cr
    wcel
    #
    @0
    @2
    cltrr
    wbr
    #
    w3a
    #
    vx
    vy
    copab
    #
    cr
    cmnf
    csn
    #
    cun
    #
    cpnf
    csn
    #
    cxp
    #
    @7
    cr
    cxp
    #
    cun
    #
    cun
    cxr
    cxr
    cxp
    #
    vx
    vy
    df-ltxr
    @6
    @12
    @13
    @6
    cr
    cr
    cxp
    #
    @13
    @6
    @1
    @3
    wa
    @4
    wa
    #
    vx
    vy
    copab
    @14
    @5
    @15
    vx
    vy
    @1
    @3
    @4
    df-3an
    opabbii
    @4
    vx
    vy
    cr
    cr
    opabssxp
    eqsstri
    rexpssxrxp
    sstri
    @10
    @11
    @13
    @8
    cxr
    wss
    @9
    cxr
    wss
    @10
    @13
    wss
    cr
    @7
    cxr
    ressxr
    @7
    cpnf
    cmnf
    cpr
    #
    cxr
    cpnf
    cmnf
    snsspr2
    @16
    cr
    @16
    cun
    cxr
    @16
    cr
    ssun2
    df-xr
    sseqtr4i
    #
    sstri
    #
    unssi
    @9
    @16
    cxr
    cpnf
    cmnf
    snsspr1
    @17
    sstri
    @8
    cxr
    @9
    cxr
    xpss12
    mp2an
    @7
    cxr
    wss
    cr
    cxr
    wss
    @11
    @13
    wss
    @18
    ressxr
    @7
    cxr
    cr
    cxr
    xpss12
    mp2an
    unssi
    unssi
    eqsstri
end
