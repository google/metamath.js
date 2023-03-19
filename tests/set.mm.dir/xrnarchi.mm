include "cv.mm"
include "cxrs.mm"
include "cinftm.mm"
include "cfv.mm"
include "wbr.mm"
include "cxr.mm"
include "wrex.mm"
include "carchi.mm"
include "wcel.mm"
include "wn.mm"
include "c1.mm"
include "cpnf.mm"
include "1re.mm"
include "rexri.mm"
include "pnfxr.mm"
include "crp.mm"
include "1rp.mm"
include "pnfinf.mm"
include "ax-mp.mm"
include "breq1.mm"
include "breq2.mm"
include "rspc2ev.mm"
include "mp3an.mm"
include "wral.mm"
include "rexnal.mm"
include "dfrex2.mm"
include "rexbii.mm"
include "cvv.mm"
include "wb.mm"
include "xrsex.mm"
include "cc0.mm"
include "xrsbas.mm"
include "xrs0.mm"
include "eqid.mm"
include "isarchi.mm"
include "notbii.mm"
include "3bitr4i.mm"
include "mpbi.mm"

theorem xrnarchi
  let vx: setvar x
  let vy: setvar y


  assert |- -. RR*s e. Archi

  proof
    vx
    cv
    #
    vy
    cv
    #
    cxrs
    cinftm
    cfv
    #
    wbr
    #
    vy
    cxr
    wrex
    #
    vx
    cxr
    wrex
    #
    cxrs
    carchi
    wcel
    #
    wn
    #
    c1
    cxr
    wcel
    cpnf
    cxr
    wcel
    c1
    cpnf
    @2
    wbr
    #
    @5
    c1
    1re
    rexri
    pnfxr
    c1
    crp
    wcel
    @8
    1rp
    c1
    pnfinf
    ax-mp
    @3
    @8
    c1
    @1
    @2
    wbr
    vx
    vy
    c1
    cpnf
    cxr
    cxr
    @0
    c1
    @1
    @2
    breq1
    @1
    cpnf
    c1
    @2
    breq2
    rspc2ev
    mp3an
    @3
    wn
    vy
    cxr
    wral
    #
    wn
    #
    vx
    cxr
    wrex
    @9
    vx
    cxr
    wral
    #
    wn
    @5
    @7
    @9
    vx
    cxr
    rexnal
    @4
    @10
    vx
    cxr
    @3
    vy
    cxr
    dfrex2
    rexbii
    @6
    @11
    cxrs
    cvv
    wcel
    @6
    @11
    wb
    xrsex
    vx
    vy
    cxr
    @2
    cvv
    cxrs
    cc0
    xrsbas
    xrs0
    @2
    eqid
    isarchi
    ax-mp
    notbii
    3bitr4i
    mpbi
end
