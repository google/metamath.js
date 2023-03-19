include "cv.mm"
include "crdg.mm"
include "wfn.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wlim.mm"
include "cima.mm"
include "cuni.mm"
include "cif.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "rdgeq2.mm"
include "ifeq1.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "cvv.mm"
include "cdm.mm"
include "crn.mm"
include "cmpt.mm"
include "crecs.mm"
include "cres.mm"
include "df-rdg.mm"
include "dfrecs3.mm"
include "wcel.mm"
include "wb.mm"
include "w3a.mm"
include "vex.mm"
include "resex.mm"
include "eqeq1.mm"
include "wrel.mm"
include "relres.mm"
include "reldm0.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "dmeq.mm"
include "limeq.mm"
include "syl.mm"
include "rneq.mm"
include "df-ima.mm"
include "syl6eqr.mm"
include "id.mm"
include "fveq12d.mm"
include "fveq2d.mm"
include "ifbieq12d.mm"
include "ifbieq2d.mm"
include "eqid.mm"
include "imaexg.mm"
include "uniex.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "cin.mm"
include "dmres.mm"
include "wss.mm"
include "onelss.mm"
include "imp.mm"
include "3adant2.mm"
include "fndm.mm"
include "3ad2ant2.mm"
include "sseqtr4d.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "unieq.mm"
include "word.mm"
include "onelon.mm"
include "eloni.mm"
include "csuc.mm"
include "w3o.mm"
include "ordzsl.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "sucid.mm"
include "fvres.mm"
include "ordunisuc.mm"
include "3eqtr4a.mm"
include "nsuceq0.mm"
include "neii.mm"
include "iffalsei.mm"
include "wn.mm"
include "nlimsucg.mm"
include "iffalse.mm"
include "mp2b.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "reseq2.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "wne.mm"
include "df-lim.mm"
include "simp2bi.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "3eqtr4d.mm"
include "3jaoi.mm"
include "sylbi.mm"
include "sylan9eqr.mm"
include "mpdan.mm"
include "3expa.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "rexbiia.mm"
include "abbii.mm"
include "unieqi.mm"
include "3eqtri.mm"
include "vtoclg.mm"

theorem dfrdg2
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cF: class F
  let cI: class I
  let cV: class V
  let vg: setvar g
  let vi: setvar i
  let vz: setvar z

  disjoint F f
  disjoint f x
  disjoint F x
  disjoint f y
  disjoint F y
  disjoint I f
  disjoint I x
  disjoint I y
  disjoint x y
  disjoint f g
  disjoint F g
  disjoint f i
  disjoint F i
  disjoint g i
  disjoint g x
  disjoint g y
  disjoint I i
  disjoint i x
  disjoint i y
  disjoint f z
  disjoint F z
  disjoint i z
  disjoint y z
  assert |- ( I e. V -> rec ( F , I ) = U. { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = if ( y = (/) , I , if ( Lim y , U. ( f " y ) , ( F ` ( f ` U. y ) ) ) ) ) } )

  proof
    cF
    vi
    cv
    #
    crdg
    #
    vf
    cv
    #
    vx
    cv
    #
    wfn
    #
    vy
    cv
    #
    @2
    cfv
    #
    @5
    c0
    wceq
    #
    @0
    @5
    wlim
    #
    @2
    @5
    cima
    #
    cuni
    #
    @5
    cuni
    #
    @2
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cif
    #
    wceq
    #
    vy
    @3
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    vf
    cab
    #
    cuni
    #
    wceq
    cF
    cI
    crdg
    #
    @4
    @6
    @7
    cI
    @14
    cif
    #
    wceq
    #
    vy
    @3
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    vf
    cab
    #
    cuni
    #
    wceq
    vi
    cI
    cV
    @0
    cI
    wceq
    #
    @1
    @22
    @21
    @29
    @0
    cI
    cF
    rdgeq2
    @30
    @20
    @28
    @30
    @19
    @27
    vf
    @30
    @18
    @26
    vx
    con0
    @30
    @17
    @25
    @4
    @30
    @16
    @24
    vy
    @3
    @30
    @15
    @23
    @6
    @7
    @0
    cI
    @14
    ifeq1
    eqeq2d
    ralbidv
    anbi2d
    rexbidv
    abbidv
    unieqd
    eqeq12d
    @1
    vg
    cvv
    vg
    cv
    #
    c0
    wceq
    #
    @0
    @31
    cdm
    #
    wlim
    #
    @31
    crn
    #
    cuni
    #
    @33
    cuni
    #
    @31
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    #
    crecs
    @4
    @6
    @2
    @5
    cres
    #
    @42
    cfv
    #
    wceq
    #
    vy
    @3
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    vf
    cab
    #
    cuni
    @21
    vg
    cF
    @0
    df-rdg
    vx
    vy
    vf
    @42
    dfrecs3
    @49
    @20
    @48
    @19
    vf
    @47
    @18
    vx
    con0
    @3
    con0
    wcel
    #
    @4
    @46
    @17
    @50
    @4
    wa
    @45
    @16
    vy
    @3
    @50
    @4
    @5
    @3
    wcel
    #
    @45
    @16
    wb
    @50
    @4
    @51
    w3a
    #
    @44
    @15
    @6
    @52
    @44
    @43
    cdm
    #
    c0
    wceq
    #
    @0
    @53
    wlim
    #
    @10
    @53
    cuni
    #
    @43
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cif
    #
    @15
    @43
    cvv
    wcel
    @44
    @60
    wceq
    @2
    @5
    vf
    vex
    #
    resex
    vg
    @43
    @41
    @60
    cvv
    @42
    @31
    @43
    wceq
    #
    @32
    @54
    @40
    @59
    @0
    @62
    @32
    @43
    c0
    wceq
    #
    @54
    @31
    @43
    c0
    eqeq1
    @43
    wrel
    @63
    @54
    wb
    @2
    @5
    relres
    @43
    reldm0
    ax-mp
    syl6bb
    @62
    @34
    @55
    @36
    @39
    @10
    @58
    @62
    @33
    @53
    wceq
    @34
    @55
    wb
    @31
    @43
    dmeq
    #
    @33
    @53
    limeq
    syl
    @62
    @35
    @9
    @62
    @35
    @43
    crn
    @9
    @31
    @43
    rneq
    @2
    @5
    df-ima
    syl6eqr
    unieqd
    @62
    @38
    @57
    cF
    @62
    @37
    @56
    @31
    @43
    @62
    id
    @62
    @33
    @53
    @64
    unieqd
    fveq12d
    fveq2d
    ifbieq12d
    ifbieq2d
    @42
    eqid
    @54
    @0
    @59
    vi
    vex
    @55
    @10
    @58
    @9
    @2
    cvv
    wcel
    @9
    cvv
    wcel
    @61
    @2
    @5
    cvv
    imaexg
    ax-mp
    uniex
    @57
    cF
    fvex
    ifex
    ifex
    fvmpt
    ax-mp
    @52
    @53
    @5
    wceq
    #
    @60
    @15
    wceq
    @52
    @53
    @5
    @2
    cdm
    #
    cin
    #
    @5
    @2
    @5
    dmres
    @52
    @5
    @66
    wss
    @67
    @5
    wceq
    @52
    @5
    @3
    @66
    @50
    @51
    @5
    @3
    wss
    #
    @4
    @50
    @51
    @68
    @3
    @5
    onelss
    imp
    3adant2
    @4
    @50
    @66
    @3
    wceq
    @51
    @3
    @2
    fndm
    3ad2ant2
    sseqtr4d
    @5
    @66
    df-ss
    sylib
    syl5eq
    @65
    @52
    @60
    @7
    @0
    @8
    @10
    @11
    @43
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cif
    #
    @15
    @65
    @54
    @7
    @59
    @71
    @0
    @53
    @5
    c0
    eqeq1
    @65
    @55
    @8
    @58
    @70
    @10
    @53
    @5
    limeq
    @65
    @57
    @69
    cF
    @65
    @56
    @11
    @43
    @53
    @5
    unieq
    fveq2d
    fveq2d
    ifbieq2d
    ifbieq2d
    @52
    @5
    word
    #
    @72
    @15
    wceq
    #
    @50
    @51
    @73
    @4
    @50
    @51
    wa
    @5
    con0
    wcel
    @73
    @3
    @5
    onelon
    @5
    eloni
    syl
    3adant2
    @73
    @7
    @5
    vz
    cv
    #
    csuc
    #
    wceq
    #
    vz
    con0
    wrex
    #
    @8
    w3o
    @74
    vz
    @5
    ordzsl
    @7
    @74
    @78
    @8
    @7
    @72
    @0
    @15
    @7
    @0
    @71
    iftrue
    @7
    @0
    @14
    iftrue
    eqtr4d
    @77
    @74
    vz
    con0
    @75
    con0
    wcel
    #
    @74
    @77
    @76
    c0
    wceq
    #
    @0
    @76
    wlim
    #
    @10
    @76
    cuni
    #
    @2
    @76
    cres
    #
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cif
    #
    @80
    @0
    @81
    @10
    @82
    @2
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cif
    #
    wceq
    @79
    @85
    @89
    @87
    @91
    @79
    @84
    @88
    cF
    @79
    @75
    @83
    cfv
    #
    @75
    @2
    cfv
    #
    @84
    @88
    @75
    @76
    wcel
    @92
    @93
    wceq
    @75
    vz
    vex
    #
    sucid
    @75
    @76
    @2
    fvres
    ax-mp
    @79
    @82
    @75
    @83
    @79
    @75
    word
    @82
    @75
    wceq
    @75
    eloni
    @75
    ordunisuc
    syl
    #
    fveq2d
    @79
    @82
    @75
    @2
    @95
    fveq2d
    3eqtr4a
    fveq2d
    @87
    @86
    @85
    @80
    @0
    @86
    @76
    c0
    @75
    nsuceq0
    neii
    #
    iffalsei
    @75
    cvv
    wcel
    #
    @81
    wn
    #
    @86
    @85
    wceq
    @94
    @75
    cvv
    nlimsucg
    #
    @81
    @10
    @85
    iffalse
    mp2b
    eqtri
    @91
    @90
    @89
    @80
    @0
    @90
    @96
    iffalsei
    @97
    @98
    @90
    @89
    wceq
    @94
    @99
    @81
    @10
    @89
    iffalse
    mp2b
    eqtri
    3eqtr4g
    @77
    @72
    @87
    @15
    @91
    @77
    @7
    @80
    @71
    @86
    @0
    @5
    @76
    c0
    eqeq1
    #
    @77
    @8
    @81
    @70
    @85
    @10
    @5
    @76
    limeq
    #
    @77
    @69
    @84
    cF
    @77
    @11
    @82
    @43
    @83
    @5
    @76
    @2
    reseq2
    @5
    @76
    unieq
    #
    fveq12d
    fveq2d
    ifbieq2d
    ifbieq2d
    @77
    @7
    @80
    @14
    @90
    @0
    @100
    @77
    @8
    @81
    @13
    @89
    @10
    @101
    @77
    @12
    @88
    cF
    @77
    @11
    @82
    @2
    @102
    fveq2d
    fveq2d
    ifbieq2d
    ifbieq2d
    eqeq12d
    syl5ibrcom
    rexlimiv
    @8
    @72
    @14
    @15
    @8
    @71
    @10
    @72
    @14
    @8
    @10
    @70
    iftrue
    @8
    @7
    @0
    @71
    @8
    @5
    c0
    @8
    @73
    @5
    c0
    wne
    @5
    @11
    wceq
    @5
    df-lim
    simp2bi
    neneqd
    #
    iffalsed
    @8
    @10
    @13
    iftrue
    3eqtr4d
    @8
    @7
    @0
    @14
    @103
    iffalsed
    eqtr4d
    3jaoi
    sylbi
    syl
    sylan9eqr
    mpdan
    syl5eq
    eqeq2d
    3expa
    ralbidva
    pm5.32da
    rexbiia
    abbii
    unieqi
    3eqtri
    vtoclg
end
