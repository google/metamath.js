include "wac.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wel.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wal.mm"
include "cfv.mm"
include "wcel.mm"
include "dfac3.mm"
include "cpr.mm"
include "wceq.mm"
include "cab.mm"
include "nfra1.mm"
include "wmo.mm"
include "rsp.mm"
include "weq.mm"
include "equid.mm"
include "neeq1.mm"
include "eqeq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpanr2.mm"
include "fveq2.mm"
include "preq1d.mm"
include "preq2.mm"
include "eqtr2d.mm"
include "anim2i.mm"
include "reximi.mm"
include "syl.mm"
include "prex.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "vex.mm"
include "prid2.mm"
include "fvex.mm"
include "prid1.mm"
include "pm3.2i.mm"
include "eleq2.mm"
include "sylancl.mm"
include "eleq1.mm"
include "spcev.mm"
include "sylan2.mm"
include "ex.mm"
include "syl8.mm"
include "impd.mm"
include "pm2.43d.mm"
include "df-rex.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "wb.mm"
include "wn.mm"
include "elirrv.mm"
include "mtbii.mm"
include "con2i.mm"
include "prel12.mm"
include "ancom.mm"
include "syl5rbbr.mm"
include "sylan9bbr.mm"
include "adantrr.mm"
include "pm5.32da.mm"
include "preleq.mm"
include "syl6bir.mm"
include "eqeq2d.mm"
include "biimparc.mm"
include "syl6.mm"
include "exp4c.mm"
include "com13.mm"
include "com4r.mm"
include "imp.mm"
include "imp4a.mm"
include "com3l.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "expd.mm"
include "imp4b.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "alrimiv.mm"
include "mo2icl.mm"
include "jctird.mm"
include "weu.mm"
include "df-reu.mm"
include "eu5.mm"
include "bitri.mm"
include "syl6ibr.mm"
include "ralrimi.mm"
include "crn.mm"
include "csn.mm"
include "cun.mm"
include "cpw.mm"
include "rnex.mm"
include "p0ex.mm"
include "unex.mm"
include "pwex.mm"
include "wss.mm"
include "ssun1.mm"
include "fvrn0.mm"
include "sselii.mm"
include "elun2.mm"
include "prssi.mm"
include "sylancr.mm"
include "elpw.mm"
include "syl5ibrcom.mm"
include "adantld.mm"
include "abssi.mm"
include "ssexi.mm"
include "rexeq.mm"
include "reubidv.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "exlimiv.mm"
include "alimi.mm"
include "dfac2a.mm"
include "impbii.mm"

theorem dfac2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint u x
  disjoint f x
  disjoint g x
  disjoint u y
  disjoint f y
  disjoint g y
  disjoint u z
  disjoint f z
  disjoint g z
  disjoint u w
  disjoint f w
  disjoint g w
  disjoint u v
  disjoint f v
  disjoint g v
  disjoint f u
  disjoint g u
  disjoint f g
  assert |- ( CHOICE <-> A. x E. y A. z e. x ( z =/= (/) -> E! w e. z E. v e. y ( z e. v /\ w e. v ) ) )

  proof
    wac
    vz
    cv
    #
    c0
    wne
    #
    vz
    vv
    wel
    #
    vw
    vv
    wel
    #
    wa
    #
    vv
    vy
    cv
    #
    wrex
    #
    vw
    @0
    wreu
    #
    wi
    #
    vz
    vx
    cv
    #
    wral
    #
    vy
    wex
    #
    vx
    wal
    #
    wac
    @1
    @0
    vf
    cv
    #
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vz
    @9
    wral
    #
    vf
    wex
    #
    vx
    wal
    @12
    vx
    vz
    vf
    dfac3
    @18
    @11
    vx
    @17
    @11
    vf
    @17
    @1
    @4
    vv
    vu
    cv
    #
    c0
    wne
    #
    vg
    cv
    #
    @19
    @13
    cfv
    #
    @19
    cpr
    #
    wceq
    #
    wa
    #
    vu
    @9
    wrex
    #
    vg
    cab
    #
    wrex
    #
    vw
    @0
    wreu
    #
    wi
    #
    vz
    @9
    wral
    #
    @11
    @17
    @30
    vz
    @9
    @16
    vz
    @9
    nfra1
    @17
    vz
    vx
    wel
    #
    @1
    @29
    @17
    @32
    @1
    wa
    #
    vw
    vz
    wel
    #
    @28
    wa
    #
    vw
    wex
    #
    @35
    vw
    wmo
    #
    wa
    #
    @29
    @17
    @33
    @36
    @37
    @17
    @33
    @36
    @17
    @32
    @1
    @33
    @36
    wi
    #
    @17
    @32
    @1
    @15
    @39
    @16
    vz
    @9
    rsp
    @15
    @33
    @36
    @33
    @15
    @2
    @14
    vv
    cv
    #
    wcel
    #
    wa
    #
    vv
    @27
    wrex
    #
    @36
    @33
    @14
    @0
    cpr
    #
    @27
    wcel
    #
    @0
    @44
    wcel
    #
    @14
    @44
    wcel
    #
    wa
    #
    @43
    @33
    @20
    @44
    @23
    wceq
    #
    wa
    #
    vu
    @9
    wrex
    #
    @45
    @33
    @20
    vu
    vz
    weq
    #
    wa
    #
    vu
    @9
    wrex
    #
    @51
    @32
    @1
    vz
    vz
    weq
    #
    @54
    vz
    equid
    @53
    @1
    @55
    wa
    vu
    @0
    @9
    @52
    @20
    @1
    @52
    @55
    @19
    @0
    c0
    neeq1
    @19
    @0
    @0
    eqeq1
    anbi12d
    rspcev
    mpanr2
    @53
    @50
    vu
    @9
    @52
    @49
    @20
    @52
    @23
    @14
    @19
    cpr
    @44
    @52
    @22
    @14
    @19
    @19
    @0
    @13
    fveq2
    preq1d
    @19
    @0
    @14
    preq2
    eqtr2d
    anim2i
    reximi
    syl
    @26
    @51
    vg
    @44
    @14
    @0
    prex
    @21
    @44
    wceq
    #
    @25
    @50
    vu
    @9
    @56
    @24
    @49
    @20
    @21
    @44
    @23
    eqeq1
    anbi2d
    rexbidv
    elab
    sylibr
    @46
    @47
    @14
    @0
    vz
    vex
    #
    prid2
    @14
    @0
    @0
    @13
    fvex
    #
    prid1
    pm3.2i
    @42
    @48
    vv
    @44
    @27
    @40
    @44
    wceq
    @2
    @46
    @41
    @47
    @40
    @44
    @0
    eleq2
    @40
    @44
    @14
    eleq2
    anbi12d
    rspcev
    sylancl
    @35
    @15
    @43
    wa
    vw
    @14
    @58
    vw
    cv
    #
    @14
    wceq
    #
    @34
    @15
    @28
    @43
    @59
    @14
    @0
    eleq1
    @60
    @4
    @42
    vv
    @27
    @60
    @3
    @41
    @2
    @59
    @14
    @40
    eleq1
    anbi2d
    rexbidv
    anbi12d
    spcev
    sylan2
    ex
    syl8
    impd
    pm2.43d
    @17
    @35
    @60
    wi
    #
    vw
    wal
    @37
    @17
    @61
    vw
    @17
    @34
    @28
    @60
    @28
    @40
    @27
    wcel
    #
    @4
    wa
    #
    vv
    wex
    @17
    @34
    wa
    #
    @60
    @4
    vv
    @27
    df-rex
    @64
    @63
    @60
    vv
    @17
    @34
    @62
    @4
    @60
    @62
    @34
    @17
    @4
    @60
    wi
    #
    @62
    @34
    @17
    @65
    @62
    @20
    @40
    @23
    wceq
    #
    wa
    #
    vu
    @9
    wrex
    #
    @34
    @17
    wa
    #
    @65
    wi
    #
    @26
    @68
    vg
    @40
    vv
    vex
    vg
    vv
    weq
    #
    @25
    @67
    vu
    @9
    @71
    @24
    @66
    @20
    @21
    @40
    @23
    eqeq1
    anbi2d
    rexbidv
    elab
    @67
    @70
    vu
    @9
    @69
    vu
    vx
    wel
    #
    @67
    @65
    @69
    @72
    @20
    @66
    @65
    @34
    @17
    @72
    @20
    @66
    @65
    wi
    #
    wi
    wi
    @17
    @72
    @20
    @34
    @73
    @17
    @72
    @20
    @22
    @19
    wcel
    #
    @34
    @73
    wi
    @16
    @20
    @74
    wi
    vz
    @19
    @9
    vz
    vu
    weq
    #
    @1
    @20
    @15
    @74
    @0
    @19
    c0
    neeq1
    @75
    @15
    @22
    @0
    wcel
    @74
    @75
    @14
    @22
    @0
    @0
    @19
    @13
    fveq2
    #
    eleq1d
    @0
    @19
    @22
    eleq2
    bitrd
    imbi12d
    rspccv
    @66
    @34
    @74
    @65
    @66
    @34
    @74
    @4
    @60
    @66
    @34
    @74
    wa
    #
    @4
    wa
    #
    @59
    @22
    wceq
    #
    @75
    wa
    #
    @60
    @66
    @78
    @77
    @59
    @0
    cpr
    @23
    wceq
    #
    wa
    @80
    @66
    @77
    @81
    @4
    @66
    @34
    @81
    @4
    wb
    #
    @74
    @34
    @66
    vw
    vz
    weq
    #
    wn
    #
    @82
    @83
    @34
    @83
    vw
    vw
    wel
    @34
    vw
    elirrv
    @59
    @0
    @59
    eleq2
    mtbii
    con2i
    @84
    @81
    @59
    @23
    wcel
    #
    @0
    @23
    wcel
    #
    wa
    #
    @66
    @4
    @59
    @0
    @22
    @19
    vw
    vex
    #
    @57
    @19
    @13
    fvex
    #
    vu
    vex
    #
    prel12
    @4
    @3
    @2
    wa
    @66
    @87
    @3
    @2
    ancom
    @66
    @3
    @85
    @2
    @86
    @40
    @23
    @59
    eleq2
    @40
    @23
    @0
    eleq2
    anbi12d
    syl5rbbr
    sylan9bbr
    sylan2
    adantrr
    pm5.32da
    @59
    @0
    @22
    @19
    @88
    @57
    @89
    @90
    preleq
    syl6bir
    @75
    @60
    @79
    @75
    @14
    @22
    @59
    @76
    eqeq2d
    biimparc
    syl6
    exp4c
    com13
    syl8
    com4r
    imp
    imp4a
    com3l
    rexlimiv
    sylbi
    expd
    com13
    imp4b
    exlimdv
    syl5bi
    expimpd
    alrimiv
    @35
    vw
    @14
    mo2icl
    syl
    jctird
    @29
    @35
    vw
    weu
    @38
    @28
    vw
    @0
    df-reu
    @35
    vw
    eu5
    bitri
    syl6ibr
    expd
    ralrimi
    @10
    @31
    vy
    @27
    @27
    @13
    crn
    #
    c0
    csn
    #
    cun
    #
    @9
    cun
    #
    cpw
    #
    @94
    @93
    @9
    @91
    @92
    @13
    vf
    vex
    rnex
    p0ex
    unex
    vx
    vex
    unex
    pwex
    @26
    vg
    @95
    @25
    @21
    @95
    wcel
    #
    vu
    @9
    @72
    @24
    @96
    @20
    @72
    @96
    @24
    @23
    @95
    wcel
    #
    @72
    @23
    @94
    wss
    #
    @97
    @72
    @22
    @94
    wcel
    @19
    @94
    wcel
    @98
    @93
    @94
    @22
    @93
    @9
    ssun1
    @13
    @19
    fvrn0
    sselii
    @19
    @9
    @93
    elun2
    @22
    @19
    @94
    prssi
    sylancr
    @23
    @94
    @22
    @19
    prex
    elpw
    sylibr
    @21
    @23
    @95
    eleq1
    syl5ibrcom
    adantld
    rexlimiv
    abssi
    ssexi
    @5
    @27
    wceq
    #
    @8
    @30
    vz
    @9
    @99
    @7
    @29
    @1
    @99
    @6
    @28
    vw
    @0
    @4
    vv
    @5
    @27
    rexeq
    reubidv
    imbi2d
    ralbidv
    spcev
    syl
    exlimiv
    alimi
    sylbi
    vx
    vy
    vz
    vw
    vv
    dfac2a
    impbii
end
