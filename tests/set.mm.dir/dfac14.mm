include "wac.mm"
include "cv.mm"
include "cdm.mm"
include "ctop.mm"
include "wf.mm"
include "cfv.mm"
include "cixp.mm"
include "cpt.mm"
include "ccl.mm"
include "wceq.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wcel.mm"
include "weq.mm"
include "fveq2.mm"
include "unieqd.mm"
include "pweqd.mm"
include "cbvixpv.mm"
include "eleq2i.mm"
include "cmpt.mm"
include "simplr.mm"
include "feqmptd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "cvv.mm"
include "eqid.mm"
include "vex.mm"
include "dmex.mm"
include "a1i.mm"
include "ctopon.mm"
include "ffvelrnda.mm"
include "toptopon.mm"
include "sylib.mm"
include "simpr.mm"
include "sylibr.mm"
include "wfn.mm"
include "elixp.mm"
include "simprbi.mm"
include "syl.mm"
include "r19.21bi.mm"
include "elpwid.mm"
include "ciun.mm"
include "wacn.mm"
include "fvex.mm"
include "iunex.mm"
include "simpll.mm"
include "acacni.mm"
include "sylancl.mm"
include "syl5eleqr.mm"
include "ptclsg.mm"
include "eqtrd.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "ex.mm"
include "alrimiv.mm"
include "wfun.mm"
include "c0.mm"
include "crn.mm"
include "wnel.mm"
include "wne.mm"
include "csn.mm"
include "cun.mm"
include "crab.mm"
include "wn.mm"
include "simplrr.mm"
include "df-nel.mm"
include "wfo.mm"
include "funforn.mm"
include "fof.mm"
include "sylbi.mm"
include "ad2antrl.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "simprl.mm"
include "funfn.mm"
include "wss.mm"
include "ssun1.mm"
include "elpw.mm"
include "mpbir.mm"
include "rgenw.mm"
include "sylanblrc.mm"
include "simpl.mm"
include "snex.mm"
include "unex.mm"
include "ssun2.mm"
include "uniex.mm"
include "pwex.mm"
include "snid.mm"
include "sselii.mm"
include "epttop.mm"
include "mp2an.mm"
include "topontopi.mm"
include "fmptd.mm"
include "mptex.mm"
include "id.mm"
include "dmeq.mm"
include "rabex.mm"
include "dmmpti.mm"
include "syl6eq.mm"
include "feq12d.mm"
include "ixpeq1d.mm"
include "fveq1.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "eleq1d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "rabeqbidv.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "toponunii.mm"
include "syl6eqr.mm"
include "ixpeq2dva.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "spcv.mm"
include "sylc.mm"
include "ixpeq2dv.mm"
include "rspcv.mm"
include "dfac14lem.mm"
include "dfac9.mm"
include "impbii.mm"

theorem dfac14
  let vf: setvar f
  let vk: setvar k
  let vs: setvar s
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y

  disjoint f k
  disjoint f s
  disjoint k s
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint g k
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint k x
  disjoint k y
  disjoint s x
  disjoint s y
  disjoint x y
  assert |- ( CHOICE <-> A. f ( f : dom f --> Top -> A. s e. X_ k e. dom f ~P U. ( f ` k ) ( ( cls ` ( Xt_ ` f ) ) ` X_ k e. dom f ( s ` k ) ) = X_ k e. dom f ( ( cls ` ( f ` k ) ) ` ( s ` k ) ) ) )

  proof
    wac
    vf
    cv
    #
    cdm
    #
    ctop
    @0
    wf
    #
    vk
    @1
    vk
    cv
    #
    vs
    cv
    #
    cfv
    #
    cixp
    #
    @0
    cpt
    cfv
    #
    ccl
    cfv
    #
    cfv
    #
    vk
    @1
    @5
    @3
    @0
    cfv
    #
    ccl
    cfv
    #
    cfv
    #
    cixp
    #
    wceq
    #
    vs
    vk
    @1
    @10
    cuni
    #
    cpw
    #
    cixp
    #
    wral
    #
    wi
    #
    vf
    wal
    #
    wac
    @19
    vf
    wac
    @2
    @18
    wac
    @2
    wa
    #
    @14
    vs
    @17
    @4
    @17
    wcel
    #
    @21
    @4
    vx
    @1
    vx
    cv
    #
    @0
    cfv
    #
    cuni
    #
    cpw
    #
    cixp
    #
    wcel
    #
    @14
    @17
    @27
    @4
    vk
    vx
    @1
    @16
    @26
    vk
    vx
    weq
    #
    @15
    @25
    @29
    @10
    @24
    @3
    @23
    @0
    fveq2
    unieqd
    pweqd
    cbvixpv
    eleq2i
    #
    @21
    @28
    wa
    #
    @9
    @6
    vk
    @1
    @10
    cmpt
    #
    cpt
    cfv
    #
    ccl
    cfv
    #
    cfv
    @13
    @31
    @6
    @8
    @34
    @31
    @7
    @33
    ccl
    @31
    @0
    @32
    cpt
    @31
    vk
    @1
    ctop
    @0
    wac
    @2
    @28
    simplr
    #
    feqmptd
    fveq2d
    fveq2d
    fveq1d
    @31
    @1
    @10
    @5
    vk
    @33
    cvv
    @15
    @33
    eqid
    @1
    cvv
    wcel
    #
    @31
    @0
    vf
    vex
    dmex
    #
    a1i
    @31
    @3
    @1
    wcel
    wa
    #
    @10
    ctop
    wcel
    @10
    @15
    ctopon
    cfv
    wcel
    @31
    @1
    ctop
    @3
    @0
    @35
    ffvelrnda
    @10
    @15
    @15
    eqid
    toptopon
    sylib
    @38
    @5
    @15
    @31
    @5
    @16
    wcel
    #
    vk
    @1
    @31
    @22
    @39
    vk
    @1
    wral
    #
    @31
    @28
    @22
    @21
    @28
    simpr
    @30
    sylibr
    @22
    @4
    @1
    wfn
    @40
    vk
    @1
    @16
    @4
    vs
    vex
    elixp
    simprbi
    syl
    r19.21bi
    elpwid
    @31
    vk
    @1
    @5
    ciun
    cvv
    @1
    wacn
    #
    vk
    @1
    @5
    @37
    @3
    @4
    fvex
    iunex
    @31
    wac
    @36
    @41
    cvv
    wceq
    wac
    @2
    @28
    simpll
    @37
    @1
    cvv
    acacni
    sylancl
    syl5eleqr
    ptclsg
    eqtrd
    sylan2b
    ralrimiva
    ex
    alrimiv
    @20
    vg
    cv
    #
    wfun
    #
    c0
    @42
    crn
    #
    wnel
    #
    wa
    #
    vx
    @42
    cdm
    #
    @23
    @42
    cfv
    #
    cixp
    #
    c0
    wne
    #
    wi
    #
    vg
    wal
    wac
    @20
    @51
    vg
    @20
    @46
    @50
    @20
    @46
    wa
    #
    vx
    vy
    @48
    cuni
    #
    cpw
    #
    @54
    vy
    cv
    #
    wcel
    #
    @55
    @48
    @54
    csn
    #
    cun
    #
    wceq
    #
    wi
    #
    vy
    @58
    cpw
    #
    crab
    #
    @48
    @47
    vx
    @47
    @62
    cmpt
    #
    cpt
    cfv
    #
    cvv
    cvv
    @47
    cvv
    wcel
    @52
    @42
    vg
    vex
    #
    dmex
    #
    a1i
    @48
    cvv
    wcel
    @52
    @23
    @47
    wcel
    #
    wa
    #
    @23
    @42
    fvex
    #
    a1i
    @68
    c0
    @44
    wcel
    #
    wn
    #
    @48
    c0
    wne
    @68
    @45
    @71
    @20
    @43
    @45
    @67
    simplrr
    c0
    @44
    df-nel
    sylib
    @68
    @70
    @48
    c0
    @68
    @48
    @44
    wcel
    @48
    c0
    wceq
    @70
    @52
    @47
    @44
    @23
    @42
    @43
    @47
    @44
    @42
    wf
    #
    @20
    @45
    @43
    @47
    @44
    @42
    wfo
    @72
    @42
    funforn
    @47
    @44
    @42
    fof
    sylbi
    ad2antrl
    ffvelrnda
    @48
    c0
    @44
    eleq1
    syl5ibcom
    necon3bd
    mpd
    @54
    eqid
    @62
    eqid
    @64
    eqid
    @52
    @42
    vk
    @47
    @3
    @42
    cfv
    #
    @73
    cuni
    #
    cpw
    #
    csn
    #
    cun
    #
    cpw
    #
    cixp
    #
    wcel
    #
    vk
    @47
    @5
    cixp
    #
    @64
    ccl
    cfv
    #
    cfv
    #
    vk
    @47
    @5
    @75
    @55
    wcel
    #
    @55
    @77
    wceq
    #
    wi
    #
    vy
    @78
    crab
    #
    ccl
    cfv
    #
    cfv
    #
    cixp
    #
    wceq
    #
    vs
    @79
    wral
    #
    @49
    @82
    cfv
    #
    vx
    @47
    @48
    @62
    ccl
    cfv
    #
    cfv
    #
    cixp
    #
    wceq
    #
    @52
    @42
    @47
    wfn
    #
    @73
    @78
    wcel
    #
    vk
    @47
    wral
    @80
    @52
    @43
    @98
    @20
    @43
    @45
    simprl
    @42
    funfn
    sylib
    @99
    vk
    @47
    @99
    @73
    @77
    wss
    @73
    @76
    ssun1
    @73
    @77
    @3
    @42
    fvex
    #
    elpw
    mpbir
    rgenw
    vk
    @47
    @78
    @42
    @65
    elixp
    sylanblrc
    @52
    @20
    @47
    ctop
    @63
    wf
    #
    @92
    @20
    @46
    simpl
    @52
    vx
    @47
    @62
    ctop
    @63
    @62
    ctop
    wcel
    @68
    @58
    @62
    @58
    cvv
    wcel
    @54
    @58
    wcel
    @62
    @58
    ctopon
    cfv
    wcel
    @48
    @57
    @69
    @54
    snex
    unex
    #
    @57
    @58
    @54
    @57
    @48
    ssun2
    @54
    @53
    @48
    @69
    uniex
    pwex
    snid
    sselii
    vy
    @58
    @54
    cvv
    epttop
    mp2an
    topontopi
    a1i
    @63
    eqid
    #
    fmptd
    @19
    @101
    @92
    wi
    vf
    @63
    vx
    @47
    @62
    @66
    mptex
    @0
    @63
    wceq
    #
    @2
    @101
    @18
    @92
    @104
    @1
    @47
    ctop
    @0
    @63
    @104
    id
    @104
    @1
    @63
    cdm
    @47
    @0
    @63
    dmeq
    vx
    @47
    @62
    @63
    @60
    vy
    @61
    @58
    @102
    pwex
    rabex
    @103
    dmmpti
    syl6eq
    #
    feq12d
    @104
    @14
    @91
    vs
    @17
    @79
    @104
    @17
    vk
    @47
    @16
    cixp
    @79
    @104
    vk
    @1
    @47
    @16
    @105
    ixpeq1d
    @104
    vk
    @47
    @16
    @78
    @104
    @3
    @47
    wcel
    #
    wa
    #
    @15
    @77
    @107
    @15
    @87
    cuni
    @77
    @107
    @10
    @87
    @104
    @106
    @10
    @3
    @63
    cfv
    @87
    @3
    @0
    @63
    fveq1
    vx
    @3
    @62
    @87
    @47
    @63
    vx
    vk
    weq
    #
    @60
    @86
    vy
    @61
    @78
    @108
    @58
    @77
    @108
    @48
    @73
    @57
    @76
    @23
    @3
    @42
    fveq2
    #
    @108
    @54
    @75
    @108
    @53
    @74
    @108
    @48
    @73
    @109
    unieqd
    pweqd
    #
    sneqd
    uneq12d
    #
    pweqd
    @108
    @56
    @84
    @59
    @85
    @108
    @54
    @75
    @55
    @110
    eleq1d
    @108
    @58
    @77
    @55
    @111
    eqeq2d
    imbi12d
    rabeqbidv
    @103
    @86
    vy
    @78
    @77
    @73
    @76
    @100
    @75
    snex
    unex
    #
    pwex
    rabex
    fvmpt
    sylan9eq
    #
    unieqd
    @77
    @87
    @77
    cvv
    wcel
    @75
    @77
    wcel
    @87
    @77
    ctopon
    cfv
    wcel
    @112
    @76
    @77
    @75
    @76
    @73
    ssun2
    @75
    @74
    @73
    @100
    uniex
    pwex
    snid
    sselii
    vy
    @77
    @75
    cvv
    epttop
    mp2an
    toponunii
    syl6eqr
    pweqd
    ixpeq2dva
    eqtrd
    @104
    @9
    @83
    @13
    @90
    @104
    @6
    @81
    @8
    @82
    @104
    @7
    @64
    ccl
    @0
    @63
    cpt
    fveq2
    fveq2d
    @104
    vk
    @1
    @47
    @5
    @105
    ixpeq1d
    fveq12d
    @104
    @13
    vk
    @47
    @12
    cixp
    @90
    @104
    vk
    @1
    @47
    @12
    @105
    ixpeq1d
    @104
    vk
    @47
    @12
    @89
    @107
    @5
    @11
    @88
    @107
    @10
    @87
    ccl
    @113
    fveq2d
    fveq1d
    ixpeq2dva
    eqtrd
    eqeq12d
    raleqbidv
    imbi12d
    spcv
    sylc
    @91
    @97
    vs
    @42
    @79
    vs
    vg
    weq
    #
    @83
    @93
    @90
    @96
    @114
    @81
    @49
    @82
    @114
    @81
    vk
    @47
    @73
    cixp
    @49
    @114
    vk
    @47
    @5
    @73
    @3
    @4
    @42
    fveq1
    #
    ixpeq2dv
    vk
    vx
    @47
    @73
    @48
    @3
    @23
    @42
    fveq2
    #
    cbvixpv
    syl6eq
    fveq2d
    @114
    @90
    vk
    @47
    @73
    @88
    cfv
    #
    cixp
    @96
    @114
    vk
    @47
    @89
    @117
    @114
    @5
    @73
    @88
    @115
    fveq2d
    ixpeq2dv
    vk
    vx
    @47
    @117
    @95
    @29
    @73
    @48
    @88
    @94
    @29
    @87
    @62
    ccl
    @29
    @86
    @60
    vy
    @78
    @61
    @29
    @77
    @58
    @29
    @73
    @48
    @76
    @57
    @116
    @29
    @75
    @54
    @29
    @74
    @53
    @29
    @73
    @48
    @116
    unieqd
    pweqd
    #
    sneqd
    uneq12d
    #
    pweqd
    @29
    @84
    @56
    @85
    @59
    @29
    @75
    @54
    @55
    @118
    eleq1d
    @29
    @77
    @58
    @55
    @119
    eqeq2d
    imbi12d
    rabeqbidv
    fveq2d
    @116
    fveq12d
    cbvixpv
    syl6eq
    eqeq12d
    rspcv
    sylc
    dfac14lem
    ex
    alrimiv
    vx
    vg
    dfac9
    sylibr
    impbii
end
