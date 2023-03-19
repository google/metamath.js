include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cxr.mm"
include "csn.mm"
include "cun.mm"
include "cfi.mm"
include "ctg.mm"
include "ctsr.mm"
include "wcel.mm"
include "wceq.mm"
include "letsr.mm"
include "ledm.mm"
include "leordtvallem1.mm"
include "leordtvallem2.mm"
include "ordtval.mm"
include "ax-mp.mm"
include "wss.mm"
include "cvv.mm"
include "snex.mm"
include "cpw.mm"
include "xrex.mm"
include "pwex.mm"
include "cv.mm"
include "cpnf.mm"
include "cioc.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "eqid.mm"
include "iocssxr.mm"
include "elpw2.mm"
include "mpbir.mm"
include "a1i.mm"
include "fmpti.mm"
include "frn.mm"
include "eqsstri.mm"
include "cmnf.mm"
include "cico.mm"
include "icossxr.mm"
include "unssi.mm"
include "ssexi.mm"
include "unex.mm"
include "ssun2.mm"
include "fiss.mm"
include "mp2an.mm"
include "fvex.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cuni.mm"
include "ovex.mm"
include "unipr.mm"
include "cicc.mm"
include "mnfxr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "mnflt0.mm"
include "0lepnf.mm"
include "df-icc.mm"
include "df-ioc.mm"
include "xrltnle.mm"
include "xrletr.mm"
include "wa.mm"
include "xrlttr.mm"
include "wi.mm"
include "xrltle.mm"
include "3adant2.mm"
include "syld.mm"
include "ixxun.mm"
include "mpanr12.mm"
include "mp3an.mm"
include "1re.mm"
include "rexri.mm"
include "0lt1.mm"
include "df-ico.mm"
include "xrlelttr.mm"
include "ixxss2.mm"
include "unss1.mm"
include "eqsstr3i.mm"
include "iccmax.mm"
include "uncom.mm"
include "3sstr3i.mm"
include "eqssi.mm"
include "eqtri.mm"
include "ssun1.mm"
include "wrex.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "elrnmpti.mm"
include "eleqtrri.mm"
include "sselii.mm"
include "oveq2.mm"
include "prssi.mm"
include "ssfii.mm"
include "sstri.mm"
include "eltg3i.mm"
include "eqeltrri.mm"
include "snssi.mm"
include "bastg.mm"
include "ctb.mm"
include "ctop.mm"
include "fibas.mm"
include "tgcl.mm"
include "fitop.mm"
include "mp2b.mm"
include "sseqtri.mm"
include "2basgen.mm"
include "eqtr4i.mm"

theorem leordtval2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume leordtval.1: |- A = ran ( x e. RR* |-> ( x (,] +oo ) )
  assume leordtval.2: |- B = ran ( x e. RR* |-> ( -oo [,) x ) )


  assert |- ( ordTop ` <_ ) = ( topGen ` ( fi ` ( A u. B ) ) )

  proof
    cle
    cordt
    cfv
    #
    cxr
    csn
    #
    cA
    cB
    cun
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    @2
    cfi
    cfv
    #
    ctg
    cfv
    #
    cle
    ctsr
    wcel
    @0
    @5
    wceq
    letsr
    vx
    vy
    cA
    cB
    cle
    ctsr
    cxr
    ledm
    vx
    vy
    cA
    leordtval.1
    leordtvallem1
    vx
    vy
    cA
    cB
    leordtval.1
    leordtval.2
    leordtvallem2
    ordtval
    ax-mp
    @6
    @4
    wss
    #
    @4
    @7
    wss
    @7
    @5
    wceq
    @3
    cvv
    wcel
    @2
    @3
    wss
    @8
    @1
    @2
    cxr
    snex
    @2
    cxr
    cpw
    #
    cxr
    xrex
    pwex
    cA
    cB
    @9
    cA
    vx
    cxr
    vx
    cv
    #
    cpnf
    cioc
    co
    #
    cmpt
    #
    crn
    #
    @9
    leordtval.1
    cxr
    @9
    @12
    wf
    @13
    @9
    wss
    vx
    cxr
    @9
    @11
    @12
    @12
    eqid
    #
    @11
    @9
    wcel
    #
    @10
    cxr
    wcel
    #
    @15
    @11
    cxr
    wss
    @10
    cpnf
    iocssxr
    @11
    cxr
    xrex
    elpw2
    mpbir
    a1i
    fmpti
    cxr
    @9
    @12
    frn
    ax-mp
    eqsstri
    cB
    vx
    cxr
    cmnf
    @10
    cico
    co
    #
    cmpt
    #
    crn
    #
    @9
    leordtval.2
    cxr
    @9
    @18
    wf
    @19
    @9
    wss
    vx
    cxr
    @9
    @17
    @18
    @18
    eqid
    #
    @17
    @9
    wcel
    #
    @16
    @21
    @17
    cxr
    wss
    cmnf
    @10
    icossxr
    @17
    cxr
    xrex
    elpw2
    mpbir
    a1i
    fmpti
    cxr
    @9
    @18
    frn
    ax-mp
    eqsstri
    unssi
    ssexi
    #
    unex
    @2
    @1
    ssun2
    @2
    @3
    cvv
    fiss
    mp2an
    @4
    @7
    cfi
    cfv
    #
    @7
    @7
    cvv
    wcel
    @3
    @7
    wss
    @4
    @23
    wss
    @6
    ctg
    fvex
    @1
    @2
    @7
    cxr
    @7
    wcel
    @1
    @7
    wss
    cc0
    cpnf
    cioc
    co
    #
    cmnf
    c1
    cico
    co
    #
    cpr
    #
    cuni
    #
    cxr
    @7
    @27
    @24
    @25
    cun
    #
    cxr
    @24
    @25
    cc0
    cpnf
    cioc
    ovex
    cmnf
    c1
    cico
    ovex
    unipr
    @28
    cxr
    @24
    @25
    cxr
    cc0
    cpnf
    iocssxr
    cmnf
    c1
    icossxr
    unssi
    cmnf
    cpnf
    cicc
    co
    #
    @25
    @24
    cun
    #
    cxr
    @28
    @29
    cmnf
    cc0
    cicc
    co
    #
    @24
    cun
    #
    @30
    cmnf
    cxr
    wcel
    #
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @32
    @29
    wceq
    #
    mnfxr
    0xr
    pnfxr
    @33
    @34
    @35
    w3a
    cmnf
    cc0
    clt
    wbr
    #
    cc0
    cpnf
    cle
    wbr
    @36
    mnflt0
    0lepnf
    vx
    vy
    vz
    vw
    cmnf
    cc0
    cpnf
    cioc
    cicc
    cle
    cle
    clt
    cle
    cicc
    clt
    cle
    vx
    vy
    vz
    df-icc
    #
    vx
    vy
    vz
    df-ioc
    cc0
    vw
    cv
    #
    xrltnle
    @38
    @39
    cc0
    cpnf
    xrletr
    @33
    @34
    @39
    cxr
    wcel
    #
    w3a
    @37
    cc0
    @39
    clt
    wbr
    wa
    cmnf
    @39
    clt
    wbr
    #
    cmnf
    @39
    cle
    wbr
    #
    cmnf
    cc0
    @39
    xrlttr
    @33
    @40
    @41
    @42
    wi
    @34
    cmnf
    @39
    xrltle
    3adant2
    syld
    ixxun
    mpanr12
    mp3an
    @31
    @25
    wss
    #
    @32
    @30
    wss
    c1
    cxr
    wcel
    #
    cc0
    c1
    clt
    wbr
    @43
    c1
    1re
    rexri
    #
    0lt1
    vx
    vy
    vz
    vw
    cmnf
    cc0
    c1
    cicc
    cle
    clt
    cle
    cico
    clt
    vx
    vy
    vz
    df-ico
    @38
    @39
    cc0
    c1
    xrlelttr
    ixxss2
    mp2an
    @31
    @25
    @24
    unss1
    ax-mp
    eqsstr3i
    iccmax
    @25
    @24
    uncom
    3sstr3i
    eqssi
    eqtri
    @6
    cvv
    wcel
    #
    @26
    @6
    wss
    @27
    @7
    wcel
    @2
    cfi
    fvex
    #
    @26
    @2
    @6
    @24
    @2
    wcel
    @25
    @2
    wcel
    @26
    @2
    wss
    cA
    @2
    @24
    cA
    cB
    ssun1
    @24
    @13
    cA
    @24
    @13
    wcel
    @24
    @11
    wceq
    #
    vx
    cxr
    wrex
    #
    @34
    @24
    @24
    wceq
    #
    @49
    0xr
    @24
    eqid
    @48
    @50
    vx
    cc0
    cxr
    @10
    cc0
    wceq
    @11
    @24
    @24
    @10
    cc0
    cpnf
    cioc
    oveq1
    eqeq2d
    rspcev
    mp2an
    vx
    cxr
    @11
    @24
    @12
    @14
    @10
    cpnf
    cioc
    ovex
    elrnmpti
    mpbir
    leordtval.1
    eleqtrri
    sselii
    cB
    @2
    @25
    cB
    cA
    ssun2
    @25
    @19
    cB
    @25
    @19
    wcel
    @25
    @17
    wceq
    #
    vx
    cxr
    wrex
    #
    @44
    @25
    @25
    wceq
    #
    @52
    @45
    @25
    eqid
    @51
    @53
    vx
    c1
    cxr
    @10
    c1
    wceq
    @17
    @25
    @25
    @10
    c1
    cmnf
    cico
    oveq2
    eqeq2d
    rspcev
    mp2an
    vx
    cxr
    @17
    @25
    @18
    @20
    cmnf
    @10
    cico
    ovex
    elrnmpti
    mpbir
    leordtval.2
    eleqtrri
    sselii
    @24
    @25
    @2
    prssi
    mp2an
    @2
    cvv
    wcel
    @2
    @6
    wss
    @22
    @2
    cvv
    ssfii
    ax-mp
    #
    sstri
    @26
    @6
    cvv
    eltg3i
    mp2an
    eqeltrri
    cxr
    @7
    snssi
    ax-mp
    @2
    @6
    @7
    @54
    @46
    @6
    @7
    wss
    @47
    @6
    cvv
    bastg
    ax-mp
    sstri
    unssi
    @3
    @7
    cvv
    fiss
    mp2an
    @6
    ctb
    wcel
    @7
    ctop
    wcel
    @23
    @7
    wceq
    @2
    fibas
    @6
    tgcl
    @7
    fitop
    mp2b
    sseqtri
    @6
    @4
    2basgen
    mp2an
    eqtr4i
end
