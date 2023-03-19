include "weq.mm"
include "wal.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wn.mm"
include "axunndlem1.mm"
include "nfnae.mm"
include "nfan.mm"
include "nfv.mm"
include "cv.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantr.mm"
include "nfcvd.mm"
include "nfeld.mm"
include "adantl.mm"
include "nfand.mm"
include "nfexd.mm"
include "nfimd.mm"
include "nfald.mm"
include "wb.mm"
include "nfcvf2.mm"
include "nfeqd.mm"
include "nfan1.mm"
include "elequ2.mm"
include "elequ1.mm"
include "anbi12d.mm"
include "a1i.mm"
include "cbvexd.mm"
include "imbi12d.mm"
include "albid.mm"
include "ex.mm"
include "mpbii.mm"
include "nfae.mm"
include "elirrv.mm"
include "mtbiri.mm"
include "intnanrd.mm"
include "sps.mm"
include "nexd.mm"
include "pm2.21d.mm"
include "alrimi.mm"
include "19.8a.mm"
include "syl.mm"
include "intnand.mm"
include "pm2.61ii.mm"

theorem axunnd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- E. x A. y ( E. x ( y e. x /\ x e. z ) -> y e. x )

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
    #
    vx
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
    @4
    wi
    #
    vy
    wal
    #
    vx
    wex
    #
    @1
    wn
    #
    @3
    wn
    #
    @10
    @11
    @12
    wa
    #
    vy
    vw
    wel
    #
    vw
    vz
    wel
    #
    wa
    #
    vw
    wex
    #
    @14
    wi
    #
    vy
    wal
    #
    vw
    wex
    @10
    vw
    vy
    vz
    axunndlem1
    @13
    @19
    @9
    vw
    vx
    @11
    @12
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
    @13
    @18
    vx
    vy
    @11
    @12
    vy
    vx
    vy
    vy
    nfnae
    vx
    vz
    vy
    nfnae
    nfan
    #
    @13
    @17
    @14
    vx
    @13
    @16
    vx
    vw
    @13
    vw
    nfv
    @13
    @14
    @15
    vx
    @13
    vx
    vy
    cv
    #
    vw
    cv
    #
    @11
    vx
    @22
    wnfc
    @12
    vx
    vy
    nfcvf
    adantr
    @13
    vx
    @23
    nfcvd
    #
    nfeld
    #
    @13
    vx
    @23
    vz
    cv
    #
    @24
    @12
    vx
    @26
    wnfc
    @11
    vx
    vz
    nfcvf
    adantl
    nfeld
    nfand
    #
    nfexd
    @25
    nfimd
    nfald
    @13
    vw
    vx
    weq
    #
    @19
    @9
    wb
    @13
    @28
    wa
    #
    @18
    @8
    vy
    @13
    @28
    vy
    @21
    @13
    vy
    @23
    vx
    cv
    #
    @13
    vy
    @23
    nfcvd
    @11
    vy
    @30
    wnfc
    @12
    vx
    vy
    nfcvf2
    adantr
    nfeqd
    nfan1
    @29
    @17
    @7
    @14
    @4
    @13
    @17
    @7
    wb
    @28
    @13
    @16
    @6
    vw
    vx
    @20
    @27
    @28
    @16
    @6
    wb
    wi
    @13
    @28
    @14
    @4
    @15
    @5
    vw
    vx
    vy
    elequ2
    #
    vw
    vx
    vz
    elequ1
    anbi12d
    a1i
    cbvexd
    adantr
    @28
    @14
    @4
    wb
    @13
    @31
    adantl
    imbi12d
    albid
    ex
    cbvexd
    mpbii
    ex
    @1
    @9
    @10
    @1
    @8
    vy
    vx
    vy
    vy
    nfae
    @1
    @7
    @4
    @1
    @6
    vx
    vx
    vy
    vx
    nfae
    @0
    @6
    wn
    #
    vx
    @0
    @4
    @5
    @0
    @4
    vy
    vy
    wel
    vy
    elirrv
    vx
    vy
    vy
    elequ2
    mtbiri
    intnanrd
    sps
    nexd
    pm2.21d
    alrimi
    @9
    vx
    19.8a
    #
    syl
    @3
    @9
    @10
    @3
    @8
    vy
    vx
    vz
    vy
    nfae
    @3
    @7
    @4
    @3
    @6
    vx
    vx
    vz
    vx
    nfae
    @2
    @32
    vx
    @2
    @5
    @4
    @2
    @5
    vz
    vz
    wel
    vz
    elirrv
    vx
    vz
    vz
    elequ1
    mtbiri
    intnand
    sps
    nexd
    pm2.21d
    alrimi
    @33
    syl
    pm2.61ii
end
