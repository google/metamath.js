include "weq.mm"
include "wal.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wi.mm"
include "wn.mm"
include "w3a.mm"
include "axacndlem4.mm"
include "nfnae.mm"
include "nf3an.mm"
include "cv.mm"
include "nfcvd.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "3ad2ant1.mm"
include "nfeld.mm"
include "3ad2ant3.mm"
include "nfand.mm"
include "nfald.mm"
include "nfv.mm"
include "3ad2ant2.mm"
include "nfexd.mm"
include "nfeqd.mm"
include "nfbid.mm"
include "nfimd.mm"
include "nfcvf2.mm"
include "nfan1.mm"
include "simpr.mm"
include "eleq1d.mm"
include "anbi1d.mm"
include "albid.mm"
include "anbi12d.mm"
include "exbid.mm"
include "eqeq1d.mm"
include "bibi12d.mm"
include "ex.mm"
include "cbvald.mm"
include "adantr.mm"
include "imbi12d.mm"
include "mpbii.mm"
include "3exp.mm"
include "axacndlem3.mm"
include "axacndlem1.mm"
include "aecoms.mm"
include "nfae.mm"
include "en2lp.mm"
include "elequ2.mm"
include "anbi2d.mm"
include "mtbii.mm"
include "sps.mm"
include "pm2.21d.mm"
include "spsd.mm"
include "alrimi.mm"
include "axc4i.mm"
include "19.8a.mm"
include "syl.mm"
include "pm2.61iii.mm"

theorem axacndlem5
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint w z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint v w
  assert |- E. x A. y A. z ( A. x ( y e. z /\ z e. w ) -> E. w A. y ( E. w ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) )

  proof
    vy
    vz
    weq
    vy
    wal
    #
    vy
    vx
    weq
    vy
    wal
    #
    vy
    vw
    weq
    #
    vy
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
    @6
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
    @2
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
    @3
    wn
    #
    @19
    @20
    @21
    @22
    w3a
    #
    vv
    vz
    wel
    #
    @5
    wa
    #
    vx
    wal
    #
    @25
    vv
    vw
    wel
    #
    @9
    wa
    #
    wa
    #
    vw
    wex
    #
    vv
    vw
    weq
    #
    wb
    #
    vv
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
    vv
    wal
    #
    vx
    wex
    @19
    vx
    vv
    vz
    vw
    axacndlem4
    @23
    @37
    @18
    vx
    @20
    @21
    @22
    vx
    vy
    vz
    vx
    nfnae
    vy
    vx
    vx
    nfnae
    vy
    vw
    vx
    nfnae
    nf3an
    #
    @23
    @36
    @17
    vv
    vy
    @20
    @21
    @22
    vy
    vy
    vz
    vy
    nfnae
    vy
    vx
    vy
    nfnae
    vy
    vw
    vy
    nfnae
    nf3an
    #
    @23
    @35
    vy
    vz
    @20
    @21
    @22
    vz
    vy
    vz
    vz
    nfnae
    vy
    vx
    vz
    nfnae
    vy
    vw
    vz
    nfnae
    nf3an
    #
    @23
    @26
    @34
    vy
    @23
    @25
    vy
    vx
    @38
    @23
    @24
    @5
    vy
    @23
    vy
    vv
    cv
    #
    vz
    cv
    #
    @23
    vy
    @41
    nfcvd
    #
    @20
    @21
    vy
    @42
    wnfc
    @22
    vy
    vz
    nfcvf
    3ad2ant1
    #
    nfeld
    @23
    vy
    @42
    vw
    cv
    #
    @44
    @22
    @20
    vy
    @45
    wnfc
    @21
    vy
    vw
    nfcvf
    3ad2ant3
    #
    nfeld
    nfand
    #
    nfald
    @23
    @33
    vy
    vw
    @20
    @21
    @22
    vw
    vy
    vz
    vw
    nfnae
    vy
    vx
    vw
    nfnae
    vy
    vw
    vw
    nfnae
    nf3an
    #
    @23
    @32
    vy
    vv
    @23
    vv
    nfv
    @23
    @30
    @31
    vy
    @23
    @29
    vy
    vw
    @48
    @23
    @25
    @28
    vy
    @47
    @23
    @27
    @9
    vy
    @23
    vy
    @41
    @45
    @43
    @46
    nfeld
    @23
    vy
    @45
    vx
    cv
    #
    @46
    @21
    @20
    vy
    @49
    wnfc
    @22
    vy
    vx
    nfcvf
    3ad2ant2
    nfeld
    nfand
    nfand
    nfexd
    @23
    vy
    @41
    @45
    @43
    @46
    nfeqd
    nfbid
    #
    nfald
    nfexd
    nfimd
    nfald
    @23
    vv
    vy
    weq
    #
    @36
    @17
    wb
    @23
    @51
    wa
    #
    @35
    @16
    vz
    @23
    @51
    vz
    @40
    @23
    vz
    @41
    vy
    cv
    #
    @23
    vz
    @41
    nfcvd
    @20
    @21
    vz
    @53
    wnfc
    @22
    vy
    vz
    nfcvf2
    3ad2ant1
    nfeqd
    nfan1
    @52
    @26
    @7
    @34
    @15
    @52
    @25
    @6
    vx
    @23
    @51
    vx
    @38
    @23
    vx
    @41
    @53
    @23
    vx
    @41
    nfcvd
    @21
    @20
    vx
    @53
    wnfc
    @22
    vy
    vx
    nfcvf2
    3ad2ant2
    nfeqd
    nfan1
    @52
    @24
    @4
    @5
    @52
    @41
    @53
    @42
    @23
    @51
    simpr
    #
    eleq1d
    anbi1d
    #
    albid
    @23
    @34
    @15
    wb
    @51
    @23
    @33
    @14
    vw
    @48
    @23
    @32
    @13
    vv
    vy
    @39
    @50
    @23
    @51
    @32
    @13
    wb
    @52
    @30
    @12
    @31
    @2
    @52
    @29
    @11
    vw
    @23
    @51
    vw
    @48
    @23
    vw
    @41
    @53
    @23
    vw
    @41
    nfcvd
    @22
    @20
    vw
    @53
    wnfc
    @21
    vy
    vw
    nfcvf2
    3ad2ant3
    nfeqd
    nfan1
    @52
    @25
    @6
    @28
    @10
    @55
    @52
    @27
    @8
    @9
    @52
    @41
    @53
    @45
    @54
    eleq1d
    anbi1d
    anbi12d
    exbid
    @52
    @41
    @53
    @45
    @54
    eqeq1d
    bibi12d
    ex
    cbvald
    exbid
    adantr
    imbi12d
    albid
    ex
    cbvald
    exbid
    mpbii
    3exp
    vx
    vy
    vz
    vw
    axacndlem3
    @19
    vx
    vy
    vx
    vy
    vz
    vw
    axacndlem1
    aecoms
    @3
    @18
    @19
    @2
    @17
    vy
    @3
    @16
    vz
    vy
    vw
    vz
    nfae
    @3
    @6
    @15
    vx
    @3
    @6
    @15
    @2
    @6
    wn
    vy
    @2
    @4
    vz
    vy
    wel
    #
    wa
    @6
    @53
    @42
    en2lp
    @2
    @56
    @5
    @4
    vy
    vw
    vz
    elequ2
    anbi2d
    mtbii
    sps
    pm2.21d
    spsd
    alrimi
    axc4i
    @18
    vx
    19.8a
    syl
    pm2.61iii
end
