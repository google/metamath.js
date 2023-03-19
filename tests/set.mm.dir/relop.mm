include "cop.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "cpr.mm"
include "wa.mm"
include "wex.mm"
include "df-rel.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "dfss2.mm"
include "wo.mm"
include "elop.mm"
include "elvv.mm"
include "imbi12i.mm"
include "jaob.mm"
include "bitri.mm"
include "albii.mm"
include "19.26.mm"
include "weq.mm"
include "snex.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "vex.mm"
include "opeqsn.mm"
include "syl6bb.mm"
include "2exbidv.mm"
include "imbi12d.mm"
include "spcv.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "cbvexv.mm"
include "ax6evr.mm"
include "19.41v.mm"
include "mpbiran.mm"
include "exbii.mm"
include "eqid.mm"
include "a1bi.mm"
include "3bitr2ri.mm"
include "sylib.mm"
include "prex.mm"
include "mpi.mm"
include "opeqpr.mm"
include "idd.mm"
include "eqtr2.mm"
include "preqsn.mm"
include "simplbi.mm"
include "syl.mm"
include "dfsn2.mm"
include "preq2.mm"
include "syl5req.mm"
include "syl5eq.mm"
include "anbi12d.mm"
include "biimpd.mm"
include "expd.mm"
include "com12.mm"
include "adantr.mm"
include "mpd.mm"
include "expcom.mm"
include "impd.mm"
include "jaod.mm"
include "syl5bi.mm"
include "2eximdv.mm"
include "exlimiv.mm"
include "imp.mm"
include "syl2an.mm"
include "sylbi.mm"
include "simpr.mm"
include "equid.mm"
include "jctl.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "opeq12.mm"
include "spc2ev.mm"
include "adantlr.mm"
include "preq12.mm"
include "biimpa.mm"
include "dfop.mm"
include "syl6eqr.mm"
include "jaodan.mm"
include "ex.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "exlimivv.mm"
include "impbii.mm"

theorem relop
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume relop.1: |- A e. _V
  assume relop.2: |- B e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B v
  disjoint B w
  disjoint B z
  assert |- ( Rel <. A , B >. <-> E. x E. y ( A = { x } /\ B = { x , y } ) )

  proof
    cA
    cB
    cop
    #
    wrel
    @0
    cvv
    cvv
    cxp
    #
    wss
    #
    cA
    vx
    cv
    #
    csn
    #
    wceq
    #
    cB
    @3
    vy
    cv
    #
    cpr
    #
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @0
    df-rel
    @2
    @10
    @2
    vz
    cv
    #
    cA
    csn
    #
    wceq
    #
    @11
    @3
    @6
    cop
    #
    wceq
    #
    vy
    wex
    vx
    wex
    #
    wi
    #
    vz
    wal
    #
    @11
    cA
    cB
    cpr
    #
    wceq
    #
    @16
    wi
    #
    vz
    wal
    #
    wa
    #
    @10
    @2
    @11
    @0
    wcel
    #
    @11
    @1
    wcel
    #
    wi
    #
    vz
    wal
    #
    @23
    vz
    @0
    @1
    dfss2
    @27
    @17
    @21
    wa
    #
    vz
    wal
    @23
    @26
    @28
    vz
    @26
    @13
    @20
    wo
    #
    @16
    wi
    @28
    @24
    @29
    @25
    @16
    @11
    cA
    cB
    relop.1
    relop.2
    elop
    #
    vx
    vy
    @11
    elvv
    imbi12i
    @13
    @16
    @20
    jaob
    bitri
    albii
    @17
    @21
    vz
    19.26
    bitri
    bitri
    @18
    cA
    vw
    cv
    #
    csn
    #
    wceq
    #
    vw
    wex
    #
    @19
    @14
    wceq
    #
    vy
    wex
    vx
    wex
    #
    @10
    @22
    @18
    @12
    @12
    wceq
    #
    vx
    vy
    weq
    #
    @5
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    wi
    #
    @34
    @17
    @42
    vz
    @12
    cA
    snex
    @13
    @13
    @37
    @16
    @41
    @11
    @12
    @12
    eqeq1
    @13
    @15
    @39
    vx
    vy
    @13
    @15
    @12
    @14
    wceq
    #
    @39
    @11
    @12
    @14
    eqeq1
    @43
    @14
    @12
    wceq
    @39
    @12
    @14
    eqcom
    @3
    @6
    cA
    vx
    vex
    #
    vy
    vex
    #
    relop.1
    opeqsn
    bitri
    syl6bb
    2exbidv
    imbi12d
    spcv
    @34
    @5
    vx
    wex
    @41
    @42
    @33
    @5
    vw
    vx
    vw
    vx
    weq
    #
    @32
    @4
    cA
    @31
    @3
    sneq
    eqeq2d
    cbvexv
    @40
    @5
    vx
    @40
    @38
    vy
    wex
    @5
    vy
    vx
    ax6evr
    @38
    @5
    vy
    19.41v
    mpbiran
    exbii
    @37
    @41
    @12
    eqid
    a1bi
    3bitr2ri
    sylib
    @22
    @19
    @19
    wceq
    #
    @36
    @19
    eqid
    @21
    @47
    @36
    wi
    vz
    @19
    cA
    cB
    prex
    @20
    @20
    @47
    @16
    @36
    @11
    @19
    @19
    eqeq1
    @20
    @15
    @35
    vx
    vy
    @11
    @19
    @14
    eqeq1
    2exbidv
    imbi12d
    spcv
    mpi
    @34
    @36
    @10
    @33
    @36
    @10
    wi
    vw
    @33
    @35
    @9
    vx
    vy
    @35
    @9
    cA
    @7
    wceq
    #
    cB
    @4
    wceq
    #
    wa
    #
    wo
    #
    @33
    @9
    @35
    @14
    @19
    wceq
    @51
    @19
    @14
    eqcom
    @3
    @6
    cA
    cB
    @44
    @45
    relop.1
    relop.2
    opeqpr
    bitri
    @33
    @9
    @9
    @50
    @33
    @9
    idd
    @33
    @48
    @49
    @9
    @48
    @33
    @49
    @9
    wi
    #
    @48
    @33
    wa
    #
    @38
    @52
    @53
    @7
    @32
    wceq
    #
    @38
    cA
    @7
    @32
    eqtr2
    @54
    @38
    vy
    vw
    weq
    @3
    @6
    @31
    @44
    @45
    vw
    vex
    preqsn
    simplbi
    syl
    @48
    @38
    @52
    wi
    @33
    @38
    @48
    @52
    @38
    @48
    @49
    @9
    @38
    @50
    @9
    @38
    @48
    @5
    @49
    @8
    @38
    @7
    @4
    cA
    @38
    @4
    @3
    @3
    cpr
    #
    @7
    @3
    dfsn2
    #
    @3
    @6
    @3
    preq2
    #
    syl5req
    eqeq2d
    @38
    @4
    @7
    cB
    @38
    @4
    @55
    @7
    @56
    @57
    syl5eq
    eqeq2d
    anbi12d
    biimpd
    expd
    com12
    adantr
    mpd
    expcom
    impd
    jaod
    syl5bi
    2eximdv
    exlimiv
    imp
    syl2an
    sylbi
    @9
    @2
    vx
    vy
    @9
    vz
    @0
    @1
    @9
    @29
    @11
    @31
    vv
    cv
    #
    cop
    #
    wceq
    #
    vv
    wex
    vw
    wex
    #
    @24
    @25
    @9
    @29
    @61
    @9
    @13
    @61
    @20
    @5
    @13
    @61
    @8
    @5
    @13
    wa
    #
    @11
    @3
    @3
    cop
    #
    wceq
    #
    @61
    @62
    @11
    @12
    @63
    @5
    @13
    simpr
    @5
    @63
    @12
    wceq
    #
    @13
    @5
    vx
    vx
    weq
    #
    @5
    wa
    @65
    @5
    @66
    vx
    equid
    jctl
    @3
    @3
    cA
    @44
    @44
    relop.1
    opeqsn
    sylibr
    adantr
    eqtr4d
    @60
    @64
    vw
    vv
    @3
    @3
    @44
    @44
    @46
    vv
    vx
    weq
    wa
    @59
    @63
    @11
    @31
    @58
    @3
    @3
    opeq12
    eqeq2d
    spc2ev
    syl
    adantlr
    @9
    @20
    wa
    #
    @15
    @61
    @67
    @11
    @4
    @7
    cpr
    #
    @14
    @9
    @20
    @11
    @68
    wceq
    @9
    @19
    @68
    @11
    cA
    cB
    @4
    @7
    preq12
    eqeq2d
    biimpa
    @3
    @6
    @44
    @45
    dfop
    syl6eqr
    @60
    @15
    vw
    vv
    @3
    @6
    @44
    @45
    @46
    vv
    vy
    weq
    wa
    @59
    @14
    @11
    @31
    @58
    @3
    @6
    opeq12
    eqeq2d
    spc2ev
    syl
    jaodan
    ex
    @30
    vw
    vv
    @11
    elvv
    3imtr4g
    ssrdv
    exlimivv
    impbii
    bitri
end
