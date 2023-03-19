include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "weq.mm"
include "wn.mm"
include "axinfndlem1.mm"
include "ax-gen.mm"
include "nfnae.mm"
include "nfan.mm"
include "cv.mm"
include "nfcvd.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantl.mm"
include "nfeld.mm"
include "nfald.mm"
include "adantr.mm"
include "nfand.mm"
include "nfexd.mm"
include "nfimd.mm"
include "wb.mm"
include "nfcvf2.mm"
include "nfeqd.mm"
include "nfan1.mm"
include "simpr.mm"
include "eleq1d.mm"
include "albid.mm"
include "anbi1d.mm"
include "exbid.mm"
include "imbi12d.mm"
include "ex.mm"
include "cbvald.mm"
include "anbi12d.mm"
include "mpbii.mm"
include "19.21bi.mm"
include "nd1.mm"
include "aecoms.mm"
include "pm2.21d.mm"
include "nd3.mm"
include "pm2.61ii.mm"
include "19.35ri.mm"

theorem axinfnd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- E. x ( y e. z -> ( y e. x /\ A. y ( y e. x -> E. z ( y e. z /\ z e. x ) ) ) )

  proof
    vy
    vz
    wel
    #
    vy
    vx
    wel
    #
    @1
    @0
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
    vy
    vx
    weq
    vy
    wal
    #
    vy
    vz
    weq
    vy
    wal
    #
    @0
    vx
    wal
    #
    @7
    vx
    wex
    #
    wi
    #
    @8
    wn
    #
    @9
    wn
    #
    @12
    @13
    @14
    wa
    #
    @12
    vy
    @15
    vw
    vz
    wel
    #
    vx
    wal
    #
    vw
    vx
    wel
    #
    @18
    @16
    @2
    wa
    #
    vz
    wex
    #
    wi
    #
    vw
    wal
    #
    wa
    #
    vx
    wex
    #
    wi
    #
    vw
    wal
    @12
    vy
    wal
    @25
    vw
    vx
    vw
    vz
    axinfndlem1
    ax-gen
    @15
    @25
    @12
    vw
    vy
    @13
    @14
    vy
    vy
    vx
    vy
    nfnae
    vy
    vz
    vy
    nfnae
    nfan
    #
    @15
    @17
    @24
    vy
    @15
    @16
    vy
    vx
    @13
    @14
    vx
    vy
    vx
    vx
    nfnae
    vy
    vz
    vx
    nfnae
    nfan
    #
    @15
    vy
    vw
    cv
    #
    vz
    cv
    #
    @15
    vy
    @28
    nfcvd
    #
    @14
    vy
    @29
    wnfc
    @13
    vy
    vz
    nfcvf
    adantl
    #
    nfeld
    #
    nfald
    @15
    @23
    vy
    vx
    @27
    @15
    @18
    @22
    vy
    @15
    vy
    @28
    vx
    cv
    #
    @30
    @13
    vy
    @33
    wnfc
    @14
    vy
    vx
    nfcvf
    adantr
    #
    nfeld
    #
    @15
    @21
    vy
    vw
    @13
    @14
    vw
    vy
    vx
    vw
    nfnae
    vy
    vz
    vw
    nfnae
    nfan
    @15
    @18
    @20
    vy
    @35
    @15
    @19
    vy
    vz
    @13
    @14
    vz
    vy
    vx
    vz
    nfnae
    vy
    vz
    vz
    nfnae
    nfan
    #
    @15
    @16
    @2
    vy
    @32
    @15
    vy
    @29
    @33
    @31
    @34
    nfeld
    nfand
    nfexd
    nfimd
    #
    nfald
    nfand
    nfexd
    nfimd
    @15
    vw
    vy
    weq
    #
    @25
    @12
    wb
    @15
    @38
    wa
    #
    @17
    @10
    @24
    @11
    @39
    @16
    @0
    vx
    @15
    @38
    vx
    @27
    @15
    vx
    @28
    vy
    cv
    #
    @15
    vx
    @28
    nfcvd
    @13
    vx
    @40
    wnfc
    @14
    vy
    vx
    nfcvf2
    adantr
    nfeqd
    nfan1
    #
    @39
    @28
    @40
    @29
    @15
    @38
    simpr
    #
    eleq1d
    #
    albid
    @39
    @23
    @7
    vx
    @41
    @39
    @18
    @1
    @22
    @6
    @39
    @28
    @40
    @33
    @42
    eleq1d
    #
    @15
    @22
    @6
    wb
    @38
    @15
    @21
    @5
    vw
    vy
    @26
    @37
    @15
    @38
    @21
    @5
    wb
    @39
    @18
    @1
    @20
    @4
    @44
    @39
    @19
    @3
    vz
    @15
    @38
    vz
    @36
    @15
    vz
    @28
    @40
    @15
    vz
    @28
    nfcvd
    @14
    vz
    @40
    wnfc
    @13
    vy
    vz
    nfcvf2
    adantl
    nfeqd
    nfan1
    @39
    @16
    @0
    @2
    @43
    anbi1d
    exbid
    imbi12d
    ex
    cbvald
    adantr
    anbi12d
    exbid
    imbi12d
    ex
    cbvald
    mpbii
    19.21bi
    ex
    @8
    @10
    @11
    @10
    wn
    vx
    vy
    vx
    vy
    vz
    nd1
    aecoms
    pm2.21d
    @9
    @10
    @11
    vy
    vz
    vx
    nd3
    pm2.21d
    pm2.61ii
    19.35ri
end
