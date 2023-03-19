include "weq.mm"
include "wal.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wi.mm"
include "wn.mm"
include "w3a.mm"
include "axacndlem5.mm"
include "nfnae.mm"
include "nf3an.mm"
include "cv.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "3ad2ant2.mm"
include "nfcvd.mm"
include "nfeld.mm"
include "3ad2ant3.mm"
include "nfand.mm"
include "nfald.mm"
include "3ad2ant1.mm"
include "nfexd.mm"
include "nfeqd.mm"
include "nfbid.mm"
include "nfimd.mm"
include "nfcvf2.mm"
include "nfan1.mm"
include "simpr.mm"
include "eleq2d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "albid.mm"
include "anbi1d.mm"
include "exbid.mm"
include "bibi1d.mm"
include "imbi12d.mm"
include "ex.mm"
include "cbvald.mm"
include "mpbii.mm"
include "3exp.mm"
include "axacndlem2.mm"
include "aecoms.mm"
include "axacndlem3.mm"
include "nfae.mm"
include "alimi.mm"
include "nd3.mm"
include "pm2.21d.mm"
include "syl5.mm"
include "axc4i.mm"
include "alrimi.mm"
include "19.8a.mm"
include "syl.mm"
include "pm2.61iii.mm"

theorem axacnd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- E. x A. y A. z ( A. x ( y e. z /\ z e. w ) -> E. w A. y ( E. w ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) )

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
    vz
    wal
    #
    vz
    vw
    weq
    #
    vz
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
    @3
    wn
    #
    @20
    @21
    @22
    @23
    w3a
    #
    vy
    vv
    wel
    #
    vv
    vw
    wel
    #
    wa
    #
    vx
    wal
    #
    @27
    @10
    wa
    #
    vw
    wex
    #
    @13
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
    vv
    wal
    #
    vy
    wal
    #
    vx
    wex
    @20
    vx
    vy
    vv
    vw
    axacndlem5
    @24
    @36
    @19
    vx
    @21
    @22
    @23
    vx
    vz
    vx
    vx
    nfnae
    vz
    vy
    vx
    nfnae
    vz
    vw
    vx
    nfnae
    nf3an
    #
    @24
    @35
    @18
    vy
    @21
    @22
    @23
    vy
    vz
    vx
    vy
    nfnae
    vz
    vy
    vy
    nfnae
    vz
    vw
    vy
    nfnae
    nf3an
    #
    @24
    @34
    @17
    vv
    vz
    @21
    @22
    @23
    vz
    vz
    vx
    vz
    nfnae
    vz
    vy
    vz
    nfnae
    vz
    vw
    vz
    nfnae
    nf3an
    @24
    @28
    @33
    vz
    @24
    @27
    vz
    vx
    @37
    @24
    @25
    @26
    vz
    @24
    vz
    vy
    cv
    #
    vv
    cv
    #
    @22
    @21
    vz
    @39
    wnfc
    @23
    vz
    vy
    nfcvf
    3ad2ant2
    #
    @24
    vz
    @40
    nfcvd
    #
    nfeld
    @24
    vz
    @40
    vw
    cv
    #
    @42
    @23
    @21
    vz
    @43
    wnfc
    @22
    vz
    vw
    nfcvf
    3ad2ant3
    #
    nfeld
    nfand
    #
    nfald
    @24
    @32
    vz
    vw
    @21
    @22
    @23
    vw
    vz
    vx
    vw
    nfnae
    vz
    vy
    vw
    nfnae
    vz
    vw
    vw
    nfnae
    nf3an
    #
    @24
    @31
    vz
    vy
    @38
    @24
    @30
    @13
    vz
    @24
    @29
    vz
    vw
    @46
    @24
    @27
    @10
    vz
    @45
    @24
    @8
    @9
    vz
    @24
    vz
    @39
    @43
    @41
    @44
    nfeld
    @24
    vz
    @43
    vx
    cv
    #
    @44
    @21
    @22
    vz
    @47
    wnfc
    @23
    vz
    vx
    nfcvf
    3ad2ant1
    nfeld
    nfand
    nfand
    nfexd
    @24
    vz
    @39
    @43
    @41
    @44
    nfeqd
    nfbid
    nfald
    nfexd
    nfimd
    @24
    vv
    vz
    weq
    #
    @34
    @17
    wb
    @24
    @48
    wa
    #
    @28
    @7
    @33
    @16
    @49
    @27
    @6
    vx
    @24
    @48
    vx
    @37
    @24
    vx
    @40
    vz
    cv
    #
    @24
    vx
    @40
    nfcvd
    @21
    @22
    vx
    @50
    wnfc
    @23
    vz
    vx
    nfcvf2
    3ad2ant1
    nfeqd
    nfan1
    @49
    @25
    @4
    @26
    @5
    @49
    @40
    @50
    @39
    @24
    @48
    simpr
    #
    eleq2d
    @49
    @40
    @50
    @43
    @51
    eleq1d
    anbi12d
    #
    albid
    @49
    @32
    @15
    vw
    @24
    @48
    vw
    @46
    @24
    vw
    @40
    @50
    @24
    vw
    @40
    nfcvd
    @23
    @21
    vw
    @50
    wnfc
    @22
    vz
    vw
    nfcvf2
    3ad2ant3
    nfeqd
    nfan1
    #
    @49
    @31
    @14
    vy
    @24
    @48
    vy
    @38
    @24
    vy
    @40
    @50
    @24
    vy
    @40
    nfcvd
    @22
    @21
    vy
    @50
    wnfc
    @23
    vz
    vy
    nfcvf2
    3ad2ant2
    nfeqd
    nfan1
    @49
    @30
    @12
    @13
    @49
    @29
    @11
    vw
    @53
    @49
    @27
    @6
    @10
    @52
    anbi1d
    exbid
    bibi1d
    albid
    exbid
    imbi12d
    ex
    cbvald
    albid
    exbid
    mpbii
    3exp
    @20
    vx
    vz
    vx
    vy
    vz
    vw
    axacndlem2
    aecoms
    @20
    vy
    vz
    vx
    vy
    vz
    vw
    axacndlem3
    aecoms
    @3
    @19
    @20
    @3
    @18
    vy
    vz
    vw
    vy
    nfae
    @2
    @17
    vz
    @7
    @5
    vx
    wal
    #
    @3
    @16
    @6
    @5
    vx
    @4
    @5
    simpr
    alimi
    @3
    @54
    @16
    vz
    vw
    vx
    nd3
    pm2.21d
    syl5
    axc4i
    alrimi
    @19
    vx
    19.8a
    syl
    pm2.61iii
end
