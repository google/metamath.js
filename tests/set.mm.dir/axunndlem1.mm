include "weq.mm"
include "wal.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wn.mm"
include "cv.mm"
include "en2lp.mm"
include "elequ2.mm"
include "anbi2d.mm"
include "mtbii.mm"
include "sps.mm"
include "nexdv.mm"
include "pm2.21d.mm"
include "axc4i.mm"
include "19.8a.mm"
include "syl.mm"
include "zfun.mm"
include "nfnae.mm"
include "nfvd.mm"
include "nfcvf.mm"
include "nfcrd.mm"
include "nfand.mm"
include "nfexd.mm"
include "nfimd.mm"
include "wb.mm"
include "elequ1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "a1i.mm"
include "cbvald.mm"
include "mpbii.mm"
include "pm2.61i.mm"

theorem axunndlem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- E. x A. y ( E. x ( y e. x /\ x e. z ) -> y e. x )

  proof
    vy
    vz
    weq
    #
    vy
    wal
    #
    vy
    vx
    wel
    #
    vx
    vz
    wel
    #
    wa
    #
    vx
    wex
    #
    @2
    wi
    #
    vy
    wal
    #
    vx
    wex
    #
    @1
    @7
    @8
    @0
    @6
    vy
    @1
    @5
    @2
    @1
    @4
    vx
    @0
    @4
    wn
    vy
    @0
    @2
    vx
    vy
    wel
    #
    wa
    @4
    vy
    cv
    vx
    cv
    en2lp
    @0
    @9
    @3
    @2
    vy
    vz
    vx
    elequ2
    anbi2d
    mtbii
    sps
    nexdv
    pm2.21d
    axc4i
    @7
    vx
    19.8a
    syl
    @1
    wn
    #
    vw
    vx
    wel
    #
    @3
    wa
    #
    vx
    wex
    #
    @11
    wi
    #
    vw
    wal
    #
    vx
    wex
    @8
    vx
    vw
    vz
    zfun
    @10
    @15
    @7
    vx
    @10
    @14
    @6
    vw
    vy
    vy
    vz
    vy
    nfnae
    @10
    @13
    @11
    vy
    @10
    @12
    vy
    vx
    vy
    vz
    vx
    nfnae
    @10
    @11
    @3
    vy
    @10
    @11
    vy
    nfvd
    #
    @10
    vy
    vx
    vz
    cv
    vy
    vz
    nfcvf
    nfcrd
    nfand
    nfexd
    @16
    nfimd
    vw
    vy
    weq
    #
    @14
    @6
    wb
    wi
    @10
    @17
    @13
    @5
    @11
    @2
    @17
    @12
    @4
    vx
    @17
    @11
    @2
    @3
    vw
    vy
    vx
    elequ1
    #
    anbi1d
    exbidv
    @18
    imbi12d
    a1i
    cbvald
    exbidv
    mpbii
    pm2.61i
end
