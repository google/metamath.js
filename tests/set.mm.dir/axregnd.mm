include "weq.mm"
include "wal.mm"
include "wel.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "axregndlem2.mm"
include "nfnae.mm"
include "nfan.mm"
include "wnf.mm"
include "cv.mm"
include "nfcvf.mm"
include "nfcrd.mm"
include "adantr.mm"
include "nfnd.mm"
include "adantl.mm"
include "nfimd.mm"
include "wb.mm"
include "elequ1.mm"
include "notbid.mm"
include "imbi12d.mm"
include "a1i.mm"
include "cbvald.mm"
include "anbi2d.mm"
include "exbid.mm"
include "syl5ib.mm"
include "ex.mm"
include "axregndlem1.mm"
include "aecoms.mm"
include "19.8a.mm"
include "nfae.mm"
include "elirrv.mm"
include "elequ2.mm"
include "mtbii.mm"
include "a1d.mm"
include "alimi.mm"
include "anim2i.mm"
include "expcom.mm"
include "eximd.mm"
include "syl5.mm"
include "pm2.61ii.mm"

theorem axregnd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( x e. y -> E. x ( x e. y /\ A. z ( z e. x -> -. z e. y ) ) )

  proof
    vz
    vx
    weq
    vz
    wal
    #
    vz
    vy
    weq
    #
    vz
    wal
    #
    vx
    vy
    wel
    #
    @3
    vz
    vx
    wel
    #
    vz
    vy
    wel
    #
    wn
    #
    wi
    #
    vz
    wal
    #
    wa
    #
    vx
    wex
    #
    wi
    #
    @0
    wn
    #
    @2
    wn
    #
    @11
    @3
    @3
    vw
    vx
    wel
    #
    vw
    vy
    wel
    #
    wn
    #
    wi
    #
    vw
    wal
    #
    wa
    #
    vx
    wex
    @12
    @13
    wa
    #
    @10
    vx
    vy
    vw
    axregndlem2
    @20
    @19
    @9
    vx
    @12
    @13
    vx
    vz
    vx
    vx
    nfnae
    vz
    vy
    vx
    nfnae
    nfan
    @20
    @18
    @8
    @3
    @20
    @17
    @7
    vw
    vz
    @12
    @13
    vz
    vz
    vx
    vz
    nfnae
    vz
    vy
    vz
    nfnae
    nfan
    @20
    @14
    @16
    vz
    @12
    @14
    vz
    wnf
    @13
    @12
    vz
    vw
    vx
    cv
    vz
    vx
    nfcvf
    nfcrd
    adantr
    @13
    @16
    vz
    wnf
    @12
    @13
    @15
    vz
    @13
    vz
    vw
    vy
    cv
    vz
    vy
    nfcvf
    nfcrd
    nfnd
    adantl
    nfimd
    vw
    vz
    weq
    #
    @17
    @7
    wb
    wi
    @20
    @21
    @14
    @4
    @16
    @6
    vw
    vz
    vx
    elequ1
    @21
    @15
    @5
    vw
    vz
    vy
    elequ1
    notbid
    imbi12d
    a1i
    cbvald
    anbi2d
    exbid
    syl5ib
    ex
    @11
    vx
    vz
    vx
    vy
    vz
    axregndlem1
    aecoms
    @3
    @3
    vx
    wex
    @2
    @10
    @3
    vx
    19.8a
    @2
    @3
    @9
    vx
    vz
    vy
    vx
    nfae
    @3
    @2
    @9
    @2
    @8
    @3
    @1
    @7
    vz
    @1
    @6
    @4
    @1
    vz
    vz
    wel
    @5
    vz
    elirrv
    vz
    vy
    vz
    elequ2
    mtbii
    a1d
    alimi
    anim2i
    expcom
    eximd
    syl5
    pm2.61ii
end
