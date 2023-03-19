include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wel.mm"
include "wex.mm"
include "wi.mm"
include "wa.mm"
include "zfpow.mm"
include "19.8a.mm"
include "sp.mm"
include "imim12i.mm"
include "alimi.mm"
include "imim1i.mm"
include "eximii.mm"
include "nfnae.mm"
include "nfan.mm"
include "nfv.mm"
include "wnf.mm"
include "cv.mm"
include "nfcvd.mm"
include "nfcvf.mm"
include "nfeld.mm"
include "nfexd.mm"
include "adantr.mm"
include "nfald.mm"
include "adantl.mm"
include "nfimd.mm"
include "wb.mm"
include "nfeqf2.mm"
include "naecoms.mm"
include "nfan1.mm"
include "elequ1.mm"
include "exbid.mm"
include "adantll.mm"
include "albid.mm"
include "adantlr.mm"
include "imbi12d.mm"
include "ex.mm"
include "cbvald.mm"
include "elequ2.mm"
include "cbvexd.mm"
include "mpbii.mm"

theorem axpowndlem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint y z
  disjoint w x
  disjoint w z
  disjoint w y
  assert |- ( -. A. x x = y -> ( -. A. x x = z -> E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    #
    vx
    vz
    weq
    vx
    wal
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
    #
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
    @0
    @1
    wa
    #
    vw
    vy
    wel
    #
    vz
    wex
    #
    vw
    vz
    wel
    #
    vy
    wal
    #
    wi
    #
    vw
    wal
    #
    vy
    vw
    wel
    #
    wi
    #
    vy
    wal
    #
    vw
    wex
    @11
    @13
    @15
    wi
    #
    vw
    wal
    #
    @19
    wi
    #
    vy
    wal
    @21
    vw
    vw
    vy
    vz
    zfpow
    @24
    @20
    vy
    @18
    @23
    @19
    @17
    @22
    vw
    @13
    @14
    @16
    @15
    @13
    vz
    19.8a
    @15
    vy
    sp
    imim12i
    alimi
    imim1i
    alimi
    eximii
    @12
    @21
    @10
    vw
    vx
    @0
    @1
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
    @12
    @20
    vx
    vy
    @0
    @1
    vy
    vx
    vy
    vy
    nfnae
    #
    vx
    vz
    vy
    nfnae
    #
    nfan
    #
    @12
    @18
    @19
    vx
    @12
    @17
    vx
    vw
    @12
    vw
    nfv
    @12
    @14
    @16
    vx
    @0
    @14
    vx
    wnf
    @1
    @0
    @13
    vx
    vz
    vx
    vy
    vz
    nfnae
    @0
    vx
    vw
    cv
    #
    vy
    cv
    #
    @0
    vx
    @29
    nfcvd
    #
    vx
    vy
    nfcvf
    #
    nfeld
    nfexd
    adantr
    @1
    @16
    vx
    wnf
    @0
    @1
    @15
    vx
    vy
    @27
    @1
    vx
    @29
    vz
    cv
    @1
    vx
    @29
    nfcvd
    vx
    vz
    nfcvf
    nfeld
    nfald
    adantl
    nfimd
    #
    nfald
    @0
    @19
    vx
    wnf
    @1
    @0
    vx
    @30
    @29
    @32
    @31
    nfeld
    adantr
    nfimd
    nfald
    @12
    vw
    vx
    weq
    #
    @21
    @10
    wb
    @12
    @34
    wa
    #
    @20
    @9
    vy
    @12
    @34
    vy
    @28
    @0
    @34
    vy
    wnf
    #
    @1
    @36
    vy
    vx
    vy
    vx
    vw
    nfeqf2
    naecoms
    #
    adantr
    nfan1
    @35
    @18
    @7
    @19
    @8
    @12
    @18
    @7
    wb
    @34
    @12
    @17
    @6
    vw
    vx
    @25
    @33
    @12
    @34
    @17
    @6
    wb
    @35
    @14
    @3
    @16
    @5
    @1
    @34
    @14
    @3
    wb
    @0
    @1
    @34
    wa
    @13
    @2
    vz
    @1
    @34
    vz
    vx
    vz
    vz
    nfnae
    @34
    vz
    wnf
    vz
    vx
    vz
    vx
    vw
    nfeqf2
    naecoms
    nfan1
    @34
    @13
    @2
    wb
    @1
    vw
    vx
    vy
    elequ1
    adantl
    exbid
    adantll
    @0
    @34
    @16
    @5
    wb
    @1
    @0
    @34
    wa
    @15
    @4
    vy
    @0
    @34
    vy
    @26
    @37
    nfan1
    @34
    @15
    @4
    wb
    @0
    vw
    vx
    vz
    elequ1
    adantl
    albid
    adantlr
    imbi12d
    ex
    cbvald
    adantr
    @34
    @19
    @8
    wb
    @12
    vw
    vx
    vy
    elequ2
    adantl
    imbi12d
    albid
    ex
    cbvexd
    mpbii
    ex
end
