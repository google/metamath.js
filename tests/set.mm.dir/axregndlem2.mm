include "weq.mm"
include "wal.mm"
include "wel.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "axreg2.mm"
include "ax-gen.mm"
include "nfnae.mm"
include "nfan.mm"
include "cv.mm"
include "nfcvd.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantr.mm"
include "nfeld.mm"
include "nfv.mm"
include "adantl.mm"
include "nfnd.mm"
include "nfimd.mm"
include "nfald.mm"
include "nfand.mm"
include "nfexd.mm"
include "wb.mm"
include "simpr.mm"
include "eleq1d.mm"
include "nfcvf2.mm"
include "nfeqd.mm"
include "nfan1.mm"
include "eleq2d.mm"
include "imbi1d.mm"
include "albid.mm"
include "anbi12d.mm"
include "ex.mm"
include "cbvexd.mm"
include "imbi12d.mm"
include "cbvald.mm"
include "mpbii.mm"
include "19.21bi.mm"
include "elirrv.mm"
include "elequ2.mm"
include "mtbii.mm"
include "sps.mm"
include "pm2.21d.mm"
include "axregndlem1.mm"
include "pm2.61ii.mm"

theorem axregndlem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint y z
  disjoint w x
  disjoint w z
  disjoint w y
  assert |- ( x e. y -> E. x ( x e. y /\ A. z ( z e. x -> -. z e. y ) ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    vx
    vz
    weq
    vx
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
    @1
    wn
    #
    @2
    wn
    #
    @11
    @12
    @13
    wa
    #
    @11
    vx
    @14
    vw
    vy
    wel
    #
    @15
    vz
    vw
    wel
    #
    @6
    wi
    #
    vz
    wal
    #
    wa
    #
    vw
    wex
    #
    wi
    #
    vw
    wal
    @11
    vx
    wal
    @21
    vw
    vw
    vy
    vz
    axreg2
    ax-gen
    @14
    @21
    @11
    vw
    vx
    @12
    @13
    vx
    vx
    vy
    vx
    nfnae
    vx
    vz
    vx
    nfnae
    nfan
    #
    @14
    @15
    @20
    vx
    @14
    vx
    vw
    cv
    #
    vy
    cv
    #
    @14
    vx
    @23
    nfcvd
    #
    @12
    vx
    @24
    wnfc
    @13
    vx
    vy
    nfcvf
    adantr
    #
    nfeld
    #
    @14
    @19
    vx
    vw
    @14
    vw
    nfv
    @14
    @15
    @18
    vx
    @27
    @14
    @17
    vx
    vz
    @12
    @13
    vz
    vx
    vy
    vz
    nfnae
    vx
    vz
    vz
    nfnae
    nfan
    #
    @14
    @16
    @6
    vx
    @14
    vx
    vz
    cv
    #
    @23
    @13
    vx
    @29
    wnfc
    @12
    vx
    vz
    nfcvf
    adantl
    #
    @25
    nfeld
    @14
    @5
    vx
    @14
    vx
    @29
    @24
    @30
    @26
    nfeld
    nfnd
    nfimd
    nfald
    nfand
    #
    nfexd
    nfimd
    @14
    vw
    vx
    weq
    #
    @21
    @11
    wb
    @14
    @32
    wa
    #
    @15
    @3
    @20
    @10
    @33
    @23
    vx
    cv
    #
    @24
    @14
    @32
    simpr
    #
    eleq1d
    #
    @14
    @20
    @10
    wb
    @32
    @14
    @19
    @9
    vw
    vx
    @22
    @31
    @14
    @32
    @19
    @9
    wb
    @33
    @15
    @3
    @18
    @8
    @36
    @33
    @17
    @7
    vz
    @14
    @32
    vz
    @28
    @14
    vz
    @23
    @34
    @14
    vz
    @23
    nfcvd
    @13
    vz
    @34
    wnfc
    @12
    vx
    vz
    nfcvf2
    adantl
    nfeqd
    nfan1
    @33
    @16
    @4
    @6
    @33
    @23
    @34
    @29
    @35
    eleq2d
    imbi1d
    albid
    anbi12d
    ex
    cbvexd
    adantr
    imbi12d
    ex
    cbvald
    mpbii
    19.21bi
    ex
    @1
    @3
    @10
    @0
    @3
    wn
    vx
    @0
    vx
    vx
    wel
    @3
    vx
    elirrv
    vx
    vy
    vx
    elequ2
    mtbii
    sps
    pm2.21d
    vx
    vy
    vz
    axregndlem1
    pm2.61ii
end
