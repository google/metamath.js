include "wcel.mm"
include "cpw.mm"
include "csiga.mm"
include "cfv.mm"
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
include "ssid.mm"
include "a1i.mm"
include "pwidg.mm"
include "difss.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "a1d.mm"
include "ralrimiv.mm"
include "sspwuni.mm"
include "vuniex.mm"
include "elpw.mm"
include "bitr4i.mm"
include "biimpi.mm"
include "elpwi.mm"
include "imim1i.mm"
include "mp1i.mm"
include "3jca.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "pwexg.mm"
include "issiga.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem pwsiga
  let cO: class O
  let cV: class V
  let vx: setvar x


  assert |- ( O e. V -> ~P O e. ( sigAlgebra ` O ) )

  proof
    cO
    cV
    wcel
    #
    cO
    cpw
    #
    cO
    csiga
    cfv
    wcel
    #
    @1
    @1
    wss
    #
    cO
    @1
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    #
    @1
    wcel
    #
    vx
    @1
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
    @1
    wcel
    #
    wi
    #
    vx
    @1
    cpw
    #
    wral
    #
    w3a
    #
    @3
    @0
    @1
    ssid
    a1i
    @0
    @4
    @8
    @14
    cO
    cV
    pwidg
    @0
    @7
    vx
    @1
    @0
    @7
    @5
    @1
    wcel
    @0
    @7
    @6
    cO
    wss
    cO
    @5
    difss
    @6
    cO
    cV
    elpw2g
    mpbiri
    a1d
    ralrimiv
    @0
    @12
    vx
    @13
    @5
    @1
    wss
    #
    @12
    wi
    @5
    @13
    wcel
    #
    @12
    wi
    @0
    @16
    @11
    @9
    @16
    @11
    @16
    @10
    cO
    wss
    @11
    @5
    cO
    sspwuni
    @10
    cO
    vx
    vuniex
    elpw
    bitr4i
    biimpi
    a1d
    @17
    @16
    @12
    @5
    @1
    elpwi
    imim1i
    mp1i
    ralrimiv
    3jca
    @0
    @1
    cvv
    wcel
    @2
    @3
    @15
    wa
    wb
    cO
    cV
    pwexg
    vx
    @1
    cO
    issiga
    syl
    mpbir2and
end
