include "weq.mm"
include "wn.mm"
include "wal.mm"
include "wel.mm"
include "wex.mm"
include "wi.mm"
include "sp.mm"
include "con3i.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "wcel.mm"
include "p0ex.mm"
include "eleq2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "spcev.mm"
include "0ex.mm"
include "snid.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "mpg.mm"
include "neq0.mm"
include "con1bii.mm"
include "imbi1i.mm"
include "albii.mm"
include "exbii.mm"
include "mpbir.mm"
include "nfnae.mm"
include "nfcvf2.mm"
include "nfcvd.mm"
include "nfeld.mm"
include "nfexd.mm"
include "nfnd.mm"
include "nfimd.mm"
include "wb.mm"
include "wa.mm"
include "nfeqf2.mm"
include "nfan1.mm"
include "elequ2.mm"
include "adantl.mm"
include "exbid.mm"
include "notbid.mm"
include "elequ1.mm"
include "imbi12d.mm"
include "ex.mm"
include "cbvald.mm"
include "mpbii.mm"
include "nfae.mm"
include "axc11r.mm"
include "alnex.mm"
include "3imtr3g.mm"
include "nd3.mm"
include "pm2.21d.mm"
include "jad.mm"
include "spsd.mm"
include "imim1d.mm"
include "alimd.mm"
include "eximd.mm"
include "syl5com.mm"
include "axpowndlem2.mm"
include "pm2.61d.mm"
include "syl.mm"

theorem axpowndlem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint y z
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- ( -. x = y -> E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) )

  proof
    vx
    vy
    weq
    #
    wn
    @0
    vx
    wal
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
    @1
    @0
    @0
    vx
    sp
    con3i
    @2
    vx
    vz
    weq
    vx
    wal
    #
    @11
    @2
    @3
    vx
    wex
    #
    wn
    #
    @8
    wi
    #
    vy
    wal
    #
    vx
    wex
    #
    @12
    @11
    @2
    vx
    vw
    wel
    #
    vx
    wex
    #
    wn
    #
    vw
    vx
    wel
    #
    wi
    #
    vw
    wal
    #
    vx
    wex
    #
    @17
    @24
    vw
    cv
    #
    c0
    wceq
    #
    @21
    wi
    #
    vw
    wal
    #
    vx
    wex
    #
    @26
    @25
    c0
    csn
    #
    wcel
    #
    wi
    #
    @29
    vw
    @28
    @32
    vw
    wal
    vx
    @30
    p0ex
    vx
    cv
    #
    @30
    wceq
    #
    @27
    @32
    vw
    @34
    @21
    @31
    @26
    @33
    @30
    @25
    eleq2
    imbi2d
    albidv
    spcev
    @26
    @31
    c0
    @30
    wcel
    c0
    0ex
    snid
    @25
    c0
    @30
    eleq1
    mpbiri
    mpg
    @23
    @28
    vx
    @22
    @27
    vw
    @20
    @26
    @21
    @26
    @19
    vx
    @25
    neq0
    con1bii
    imbi1i
    albii
    exbii
    mpbir
    @2
    @23
    @16
    vx
    vx
    vy
    vx
    nfnae
    #
    @2
    @22
    @15
    vw
    vy
    vx
    vy
    vy
    nfnae
    @2
    @20
    @21
    vy
    @2
    @19
    vy
    @2
    @18
    vy
    vx
    @35
    @2
    vy
    @33
    @25
    vx
    vy
    nfcvf2
    #
    @2
    vy
    @25
    nfcvd
    #
    nfeld
    nfexd
    nfnd
    @2
    vy
    @25
    @33
    @37
    @36
    nfeld
    nfimd
    @2
    vw
    vy
    weq
    #
    @22
    @15
    wb
    @2
    @38
    wa
    #
    @20
    @14
    @21
    @8
    @39
    @19
    @13
    @39
    @18
    @3
    vx
    @2
    @38
    vx
    @35
    vx
    vy
    vw
    nfeqf2
    nfan1
    @38
    @18
    @3
    wb
    @2
    vw
    vy
    vx
    elequ2
    adantl
    exbid
    notbid
    @38
    @21
    @8
    wb
    @2
    vw
    vy
    vx
    elequ1
    adantl
    imbi12d
    ex
    cbvald
    exbid
    mpbii
    @12
    @16
    @10
    vx
    vx
    vz
    vx
    nfae
    @12
    @15
    @9
    vy
    vx
    vz
    vy
    nfae
    @12
    @7
    @14
    @8
    @12
    @6
    @14
    vx
    @12
    @4
    @5
    @14
    @12
    @3
    wn
    #
    vz
    wal
    @40
    vx
    wal
    @4
    wn
    @14
    @40
    vz
    vx
    axc11r
    @3
    vz
    alnex
    @3
    vx
    alnex
    3imtr3g
    @12
    @5
    @14
    vx
    vz
    vy
    nd3
    pm2.21d
    jad
    spsd
    imim1d
    alimd
    eximd
    syl5com
    vx
    vy
    vz
    axpowndlem2
    pm2.61d
    syl
end
