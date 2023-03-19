include "cvol.mm"
include "cdm.mm"
include "cr.mm"
include "csiga.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "pwssb.mm"
include "mblss.mm"
include "mprgbir.mm"
include "rembl.mm"
include "cmmbl.mm"
include "rgen.mm"
include "ciun.mm"
include "cn.mm"
include "cen.mm"
include "nnenom.mm"
include "ensymi.mm"
include "domentr.mm"
include "mpan2.mm"
include "elpwi.mm"
include "dfss3.mm"
include "sylib.mm"
include "iunmbl2.mm"
include "syl2anr.mm"
include "ex.mm"
include "uniiun.mm"
include "eleq1i.mm"
include "syl6ibr.mm"
include "3pm3.2i.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "reex.mm"
include "pwex.mm"
include "ssexi.mm"
include "issiga.mm"
include "ax-mp.mm"
include "mpbir2an.mm"

theorem dmvlsiga
  let vx: setvar x
  let vy: setvar y


  assert |- dom vol e. ( sigAlgebra ` RR )

  proof
    cvol
    cdm
    #
    cr
    csiga
    cfv
    wcel
    #
    @0
    cr
    cpw
    #
    wss
    #
    cr
    @0
    wcel
    #
    cr
    vx
    cv
    #
    cdif
    @0
    wcel
    #
    vx
    @0
    wral
    #
    @5
    com
    cdom
    wbr
    #
    @5
    cuni
    #
    @0
    wcel
    #
    wi
    #
    vx
    @0
    cpw
    #
    wral
    #
    w3a
    #
    @3
    @5
    cr
    wss
    vx
    @0
    vx
    @0
    cr
    pwssb
    @5
    mblss
    mprgbir
    #
    @4
    @7
    @13
    rembl
    @6
    vx
    @0
    @5
    cmmbl
    rgen
    @11
    vx
    @12
    @5
    @12
    wcel
    #
    @8
    vy
    @5
    vy
    cv
    #
    ciun
    #
    @0
    wcel
    #
    @10
    @16
    @8
    @19
    @8
    @5
    cn
    cdom
    wbr
    #
    @17
    @0
    wcel
    vy
    @5
    wral
    #
    @19
    @16
    @8
    com
    cn
    cen
    wbr
    @20
    cn
    com
    nnenom
    ensymi
    @5
    com
    cn
    domentr
    mpan2
    @16
    @5
    @0
    wss
    @21
    @5
    @0
    elpwi
    vy
    @5
    @0
    dfss3
    sylib
    @5
    @17
    vy
    iunmbl2
    syl2anr
    ex
    @9
    @18
    @0
    vy
    @5
    uniiun
    eleq1i
    syl6ibr
    rgen
    3pm3.2i
    @0
    cvv
    wcel
    @1
    @3
    @14
    wa
    wb
    @0
    @2
    cr
    reex
    pwex
    @15
    ssexi
    vx
    @0
    cr
    issiga
    ax-mp
    mpbir2an
end
