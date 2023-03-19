include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wel.mm"
include "wex.mm"
include "wi.mm"
include "axpowndlem4.mm"
include "axpowndlem1.mm"
include "aecoms.mm"
include "a1d.mm"
include "wa.mm"
include "nfnae.mm"
include "nfae.mm"
include "nfan.mm"
include "el.mm"
include "cv.mm"
include "nfcvf2.mm"
include "nfcvd.mm"
include "nfeld.mm"
include "wb.mm"
include "elequ2.mm"
include "a1i.mm"
include "cbvexd.mm"
include "mpbii.mm"
include "19.8a.mm"
include "syl.mm"
include "df-ex.mm"
include "sylib.mm"
include "adantr.mm"
include "biidd.mm"
include "dral1.mm"
include "alnex.mm"
include "3bitr3g.mm"
include "nd2.mm"
include "mtt.mm"
include "bitrd.mm"
include "dral2.mm"
include "adantl.mm"
include "mtbid.mm"
include "pm2.21d.mm"
include "alrimi.mm"
include "ex.mm"
include "pm2.61i.mm"
include "pm2.61ii.mm"

theorem axpownd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( -. x = y -> E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) )

  proof
    vy
    vx
    weq
    vy
    wal
    vy
    vz
    weq
    vy
    wal
    #
    vx
    vy
    weq
    #
    wn
    #
    vx
    vy
    wel
    #
    vz
    wex
    #
    vx
    vz
    wel
    vy
    wal
    #
    wi
    #
    vx
    wal
    #
    vy
    vx
    wel
    #
    wi
    #
    vy
    wal
    #
    vx
    wex
    #
    wi
    #
    vx
    vy
    vz
    axpowndlem4
    @12
    vx
    vy
    vx
    vy
    vz
    axpowndlem1
    #
    aecoms
    @1
    vx
    wal
    #
    @0
    @12
    wi
    @14
    @12
    @0
    @13
    a1d
    @14
    wn
    #
    @0
    @12
    @15
    @0
    wa
    #
    @11
    @2
    @16
    @10
    @11
    @16
    @9
    vy
    @15
    @0
    vy
    vx
    vy
    vy
    nfnae
    #
    vy
    vz
    vy
    nfae
    nfan
    @16
    @7
    @8
    @16
    @3
    vy
    wex
    #
    wn
    #
    vx
    wal
    #
    @7
    @15
    @20
    wn
    #
    @0
    @15
    @18
    vx
    wex
    #
    @21
    @15
    @18
    @22
    @15
    vx
    vw
    wel
    #
    vw
    wex
    @18
    vx
    vw
    el
    @15
    @23
    @3
    vw
    vy
    @17
    @15
    vy
    vx
    cv
    vw
    cv
    #
    vx
    vy
    nfcvf2
    @15
    vy
    @24
    nfcvd
    nfeld
    vw
    vy
    weq
    @23
    @3
    wb
    wi
    @15
    vw
    vy
    vx
    elequ2
    a1i
    cbvexd
    mpbii
    @18
    vx
    19.8a
    syl
    @18
    vx
    df-ex
    sylib
    adantr
    @0
    @20
    @7
    wb
    @15
    @19
    @6
    vy
    vz
    vx
    @0
    @19
    @4
    wn
    #
    @6
    @0
    @3
    wn
    #
    vy
    wal
    @26
    vz
    wal
    @19
    @25
    @26
    @26
    vy
    vz
    @0
    @26
    biidd
    dral1
    @3
    vy
    alnex
    @3
    vz
    alnex
    3bitr3g
    @0
    @5
    wn
    @25
    @6
    wb
    vy
    vz
    vx
    nd2
    @5
    @4
    mtt
    syl
    bitrd
    dral2
    adantl
    mtbid
    pm2.21d
    alrimi
    @10
    vx
    19.8a
    syl
    a1d
    ex
    pm2.61i
    pm2.61ii
end
