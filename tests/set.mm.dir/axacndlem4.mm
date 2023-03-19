include "weq.mm"
include "wal.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wi.mm"
include "wn.mm"
include "w3a.mm"
include "zfac.mm"
include "nfnae.mm"
include "nf3an.mm"
include "cv.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "nfeld.mm"
include "3ad2ant3.mm"
include "nfand.mm"
include "nfcvd.mm"
include "nfexd.mm"
include "nfeqd.mm"
include "nfbid.mm"
include "nfald.mm"
include "nfimd.mm"
include "nfcvf2.mm"
include "nfan1.mm"
include "nf5rd.mm"
include "adantr.mm"
include "sp.mm"
include "impbid1.mm"
include "simpr.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "exbid.mm"
include "bibi1d.mm"
include "albid.mm"
include "imbi12d.mm"
include "ex.mm"
include "cbvexd.mm"
include "mpbii.mm"
include "3exp.mm"
include "axacndlem2.mm"
include "axacndlem1.mm"
include "nfae.mm"
include "alimi.mm"
include "nd2.mm"
include "pm2.21d.mm"
include "syl5.mm"
include "alrimi.mm"
include "19.8a.mm"
include "syl.mm"
include "pm2.61iii.mm"

theorem axacndlem4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint y z
  disjoint w y
  disjoint w z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint v w
  assert |- E. x A. y A. z ( A. x ( y e. z /\ z e. w ) -> E. w A. y ( E. w ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) )

  proof
    vx
    vz
    weq
    vx
    wal
    #
    vx
    vy
    weq
    vx
    wal
    #
    vx
    vw
    weq
    vx
    wal
    #
    vy
    vz
    wel
    #
    vz
    vw
    wel
    #
    wa
    #
    vx
    wal
    #
    @5
    vy
    vw
    wel
    #
    vw
    vx
    wel
    #
    wa
    #
    wa
    #
    vw
    wex
    #
    vy
    vw
    weq
    #
    wb
    #
    vy
    wal
    #
    vw
    wex
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wex
    #
    @0
    wn
    #
    @1
    wn
    #
    @2
    wn
    #
    @19
    @20
    @21
    @22
    w3a
    #
    @5
    @5
    @7
    vw
    vv
    wel
    #
    wa
    #
    wa
    #
    vw
    wex
    #
    @12
    wb
    #
    vy
    wal
    #
    vw
    wex
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vv
    wex
    @19
    vv
    vy
    vz
    vw
    zfac
    @23
    @33
    @18
    vv
    vx
    @20
    @21
    @22
    vx
    vx
    vz
    vx
    nfnae
    vx
    vy
    vx
    nfnae
    vx
    vw
    vx
    nfnae
    nf3an
    @23
    @32
    vx
    vy
    @20
    @21
    @22
    vy
    vx
    vz
    vy
    nfnae
    vx
    vy
    vy
    nfnae
    vx
    vw
    vy
    nfnae
    nf3an
    #
    @23
    @31
    vx
    vz
    @20
    @21
    @22
    vz
    vx
    vz
    vz
    nfnae
    vx
    vy
    vz
    nfnae
    vx
    vw
    vz
    nfnae
    nf3an
    #
    @23
    @5
    @30
    vx
    @23
    @3
    @4
    vx
    @23
    vx
    vy
    cv
    #
    vz
    cv
    #
    @21
    @20
    vx
    @36
    wnfc
    @22
    vx
    vy
    nfcvf
    3ad2ant2
    #
    @20
    @21
    vx
    @37
    wnfc
    @22
    vx
    vz
    nfcvf
    3ad2ant1
    #
    nfeld
    @23
    vx
    @37
    vw
    cv
    #
    @39
    @22
    @20
    vx
    @40
    wnfc
    @21
    vx
    vw
    nfcvf
    3ad2ant3
    #
    nfeld
    nfand
    #
    @23
    @29
    vx
    vw
    @20
    @21
    @22
    vw
    vx
    vz
    vw
    nfnae
    vx
    vy
    vw
    nfnae
    vx
    vw
    vw
    nfnae
    nf3an
    #
    @23
    @28
    vx
    vy
    @34
    @23
    @27
    @12
    vx
    @23
    @26
    vx
    vw
    @43
    @23
    @5
    @25
    vx
    @42
    @23
    @7
    @24
    vx
    @23
    vx
    @36
    @40
    @38
    @41
    nfeld
    @23
    vx
    @40
    vv
    cv
    #
    @41
    @23
    vx
    @44
    nfcvd
    nfeld
    nfand
    nfand
    nfexd
    @23
    vx
    @36
    @40
    @38
    @41
    nfeqd
    nfbid
    nfald
    nfexd
    nfimd
    nfald
    nfald
    @23
    vv
    vx
    weq
    #
    @33
    @18
    wb
    @23
    @45
    wa
    #
    @32
    @17
    vy
    @23
    @45
    vy
    @34
    @23
    vy
    @44
    vx
    cv
    #
    @23
    vy
    @44
    nfcvd
    @21
    @20
    vy
    @47
    wnfc
    @22
    vx
    vy
    nfcvf2
    3ad2ant2
    nfeqd
    nfan1
    #
    @46
    @31
    @16
    vz
    @23
    @45
    vz
    @35
    @23
    vz
    @44
    @47
    @23
    vz
    @44
    nfcvd
    @20
    @21
    vz
    @47
    wnfc
    @22
    vx
    vz
    nfcvf2
    3ad2ant1
    nfeqd
    nfan1
    @46
    @5
    @6
    @30
    @15
    @46
    @5
    @6
    @23
    @5
    @6
    wi
    @45
    @23
    @5
    vx
    @42
    nf5rd
    adantr
    @5
    vx
    sp
    impbid1
    @46
    @29
    @14
    vw
    @23
    @45
    vw
    @43
    @23
    vw
    @44
    @47
    @23
    vw
    @44
    nfcvd
    @22
    @20
    vw
    @47
    wnfc
    @21
    vx
    vw
    nfcvf2
    3ad2ant3
    nfeqd
    nfan1
    #
    @46
    @28
    @13
    vy
    @48
    @46
    @27
    @11
    @12
    @46
    @26
    @10
    vw
    @49
    @46
    @25
    @9
    @5
    @46
    @24
    @8
    @7
    @46
    @44
    @47
    @40
    @23
    @45
    simpr
    eleq2d
    anbi2d
    anbi2d
    exbid
    bibi1d
    albid
    exbid
    imbi12d
    albid
    albid
    ex
    cbvexd
    mpbii
    3exp
    vx
    vy
    vz
    vw
    axacndlem2
    vx
    vy
    vz
    vw
    axacndlem1
    @2
    @18
    @19
    @2
    @17
    vy
    vx
    vw
    vy
    nfae
    @2
    @16
    vz
    vx
    vw
    vz
    nfae
    @6
    @4
    vx
    wal
    #
    @2
    @15
    @5
    @4
    vx
    @3
    @4
    simpr
    alimi
    @2
    @50
    @15
    vx
    vw
    vz
    nd2
    pm2.21d
    syl5
    alrimi
    alrimi
    @18
    vx
    19.8a
    syl
    pm2.61iii
end
