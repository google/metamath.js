include "weq.mm"
include "wal.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wn.mm"
include "zfinf.mm"
include "nfnae.mm"
include "nfan.mm"
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
include "simpr.mm"
include "eleq2d.mm"
include "nfcvf2.mm"
include "nfeqd.mm"
include "nfan1.mm"
include "elequ2.mm"
include "anbi2d.mm"
include "exbid.mm"
include "imbi12d.mm"
include "albid.mm"
include "anbi12d.mm"
include "ex.mm"
include "cbvexd.mm"
include "mpbii.mm"
include "a1d.mm"
include "nd1.mm"
include "pm2.21d.mm"
include "nd2.mm"
include "pm2.61ii.mm"

theorem axinfndlem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint y z
  disjoint w x
  disjoint w z
  disjoint w y
  assert |- ( A. x y e. z -> E. x ( y e. x /\ A. y ( y e. x -> E. z ( y e. z /\ z e. x ) ) ) )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    vx
    vz
    weq
    vx
    wal
    #
    vy
    vz
    wel
    #
    vx
    wal
    #
    vy
    vx
    wel
    #
    @4
    @2
    vz
    vx
    wel
    #
    wa
    #
    vz
    wex
    #
    wi
    #
    vy
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
    @1
    wn
    #
    @12
    @13
    @14
    wa
    #
    @11
    @3
    @15
    vy
    vw
    wel
    #
    @16
    @2
    vz
    vw
    wel
    #
    wa
    #
    vz
    wex
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    vw
    wex
    @11
    vw
    vy
    vz
    zfinf
    @15
    @22
    @10
    vw
    vx
    @13
    @14
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
    @15
    @16
    @21
    vx
    @15
    vx
    vy
    cv
    #
    vw
    cv
    #
    @13
    vx
    @23
    wnfc
    @14
    vx
    vy
    nfcvf
    adantr
    #
    @15
    vx
    @24
    nfcvd
    #
    nfeld
    #
    @15
    @20
    vx
    vy
    @13
    @14
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
    @15
    @16
    @19
    vx
    @27
    @15
    @18
    vx
    vz
    @13
    @14
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
    @15
    @2
    @17
    vx
    @15
    vx
    @23
    vz
    cv
    #
    @25
    @14
    vx
    @30
    wnfc
    @13
    vx
    vz
    nfcvf
    adantl
    #
    nfeld
    @15
    vx
    @30
    @24
    @31
    @26
    nfeld
    nfand
    nfexd
    nfimd
    nfald
    nfand
    @15
    vw
    vx
    weq
    #
    @22
    @10
    wb
    @15
    @32
    wa
    #
    @16
    @4
    @21
    @9
    @33
    @24
    vx
    cv
    #
    @23
    @15
    @32
    simpr
    eleq2d
    #
    @33
    @20
    @8
    vy
    @15
    @32
    vy
    @28
    @15
    vy
    @24
    @34
    @15
    vy
    @24
    nfcvd
    @13
    vy
    @34
    wnfc
    @14
    vx
    vy
    nfcvf2
    adantr
    nfeqd
    nfan1
    @33
    @16
    @4
    @19
    @7
    @35
    @33
    @18
    @6
    vz
    @15
    @32
    vz
    @29
    @15
    vz
    @24
    @34
    @15
    vz
    @24
    nfcvd
    @14
    vz
    @34
    wnfc
    @13
    vx
    vz
    nfcvf2
    adantl
    nfeqd
    nfan1
    @32
    @18
    @6
    wb
    @15
    @32
    @17
    @5
    @2
    vw
    vx
    vz
    elequ2
    anbi2d
    adantl
    exbid
    imbi12d
    albid
    anbi12d
    ex
    cbvexd
    mpbii
    a1d
    ex
    @0
    @3
    @11
    vx
    vy
    vz
    nd1
    pm2.21d
    @1
    @3
    @11
    vx
    vz
    vy
    nd2
    pm2.21d
    pm2.61ii
end
