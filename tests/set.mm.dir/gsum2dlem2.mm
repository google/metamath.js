include "csupp.mm"
include "co.mm"
include "cdm.mm"
include "cfn.mm"
include "wcel.mm"
include "cres.mm"
include "cgsu.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "wceq.mm"
include "fsuppimpd.mm"
include "dmfi.mm"
include "syl.mm"
include "wi.mm"
include "c0.mm"
include "cun.mm"
include "reseq2.mm"
include "res0.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "oveq2d.mm"
include "mpteq1.mm"
include "mpt0.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "eqidd.mm"
include "wel.mm"
include "wn.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "oveq1.mm"
include "cvv.mm"
include "eqid.mm"
include "ccmn.mm"
include "adantr.mm"
include "resexg.mm"
include "wf.mm"
include "wss.mm"
include "resss.mm"
include "fssres.mm"
include "sylancl.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "ffun.mm"
include "funres.mm"
include "fex.mm"
include "syl2anc.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ressuppss.mm"
include "ssfi.mm"
include "wb.mm"
include "isfsupp.mm"
include "mpbir2and.mm"
include "cin.mm"
include "simprr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "resindi.mm"
include "3eqtr3g.mm"
include "resundi.mm"
include "a1i.mm"
include "gsumsplit.mm"
include "ssun1.mm"
include "ssres2.mm"
include "resabs1.mm"
include "mp2b.mm"
include "oveq2i.mm"
include "ssun2.mm"
include "oveq12i.mm"
include "simprl.mm"
include "gsum2dlem1.mm"
include "ad2antrr.mm"
include "vex.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "mpteq12dv.mm"
include "eleq1d.mm"
include "chvarv.mm"
include "gsumunsn.mm"
include "c2nd.mm"
include "cxp.mm"
include "ccom.mm"
include "imaexg.mm"
include "cop.mm"
include "elimasn.mm"
include "df-ov.mm"
include "ffvelrnda.mm"
include "syl5eqel.mm"
include "sylan2b.mm"
include "fmptd.mm"
include "funmpt.mm"
include "crn.mm"
include "rnfi.mm"
include "cdif.mm"
include "biimpi.mm"
include "opelrn.mm"
include "con3i.mm"
include "anim12i.mm"
include "eldif.mm"
include "3imtr4i.mm"
include "ssid.mm"
include "suppssr.mm"
include "syl5eq.mm"
include "sylan2.mm"
include "suppss2.mm"
include "mptexg.mm"
include "wf1o.mm"
include "2ndconst.mm"
include "mp1i.mm"
include "gsumf1o.mm"
include "c1st.mm"
include "1st2nd2.mm"
include "xp1st.mm"
include "elsni.mm"
include "opeq1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "mpteq2ia.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "ressn.mm"
include "eqtri.mm"
include "xp2nd.mm"
include "adantl.mm"
include "wfo.mm"
include "fo2nd.mm"
include "fof.mm"
include "ssv.mm"
include "oveq2.mm"
include "fmptco.mm"
include "3eqtr4a.mm"
include "eqtr4d.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "findcard2s.mm"
include "mpcom.mm"

theorem gsum2dlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gsum2d.b: |- B = ( Base ` G )
  assume gsum2d.z: |- .0. = ( 0g ` G )
  assume gsum2d.g: |- ( ph -> G e. CMnd )
  assume gsum2d.a: |- ( ph -> A e. V )
  assume gsum2d.r: |- ( ph -> Rel A )
  assume gsum2d.d: |- ( ph -> D e. W )
  assume gsum2d.s: |- ( ph -> dom A C_ D )
  assume gsum2d.f: |- ( ph -> F : A --> B )
  assume gsum2d.w: |- ( ph -> F finSupp .0. )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint F j
  disjoint F k
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint k ph
  disjoint B j
  disjoint B k
  disjoint D j
  disjoint D k
  disjoint .0. j
  disjoint .0. k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  assert |- ( ph -> ( G gsum ( F |` ( A |` dom ( F supp .0. ) ) ) ) = ( G gsum ( j e. dom ( F supp .0. ) |-> ( G gsum ( k e. ( A " { j } ) |-> ( j F k ) ) ) ) ) )

  proof
    cF
    c.0
    csupp
    co
    #
    cdm
    #
    cfn
    wcel
    #
    wph
    cG
    cF
    cA
    @1
    cres
    #
    cres
    #
    cgsu
    co
    #
    cG
    vj
    @1
    cG
    vk
    cA
    vj
    cv
    #
    csn
    #
    cima
    #
    @6
    vk
    cv
    #
    cF
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wph
    @0
    cfn
    wcel
    #
    @2
    wph
    cF
    c.0
    gsum2d.w
    fsuppimpd
    #
    @0
    dmfi
    syl
    wph
    cG
    cF
    cA
    vx
    cv
    #
    cres
    #
    cres
    #
    cgsu
    co
    #
    cG
    vj
    @18
    @12
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    wph
    cG
    c0
    cgsu
    co
    #
    @25
    wceq
    #
    wi
    wph
    cG
    cF
    cA
    vy
    cv
    #
    cres
    #
    cres
    #
    cgsu
    co
    #
    cG
    vj
    @27
    @12
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    wph
    cG
    cF
    cA
    @27
    vz
    cv
    #
    csn
    #
    cun
    #
    cres
    #
    cres
    #
    cgsu
    co
    #
    cG
    vj
    @36
    @12
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    wph
    @15
    wi
    vx
    vy
    vz
    @1
    @18
    c0
    wceq
    #
    @24
    @26
    wph
    @43
    @21
    @25
    @23
    @25
    @43
    @20
    c0
    cG
    cgsu
    @43
    @20
    cF
    c0
    cres
    c0
    @43
    @19
    c0
    cF
    @43
    @19
    cA
    c0
    cres
    #
    c0
    @18
    c0
    cA
    reseq2
    cA
    res0
    #
    syl6eq
    reseq2d
    cF
    res0
    syl6eq
    oveq2d
    @43
    @22
    c0
    cG
    cgsu
    @43
    @22
    vj
    c0
    @12
    cmpt
    c0
    vj
    @18
    c0
    @12
    mpteq1
    vj
    @12
    mpt0
    syl6eq
    oveq2d
    eqeq12d
    imbi2d
    vx
    vy
    weq
    #
    @24
    @33
    wph
    @46
    @21
    @30
    @23
    @32
    @46
    @20
    @29
    cG
    cgsu
    @46
    @19
    @28
    cF
    @18
    @27
    cA
    reseq2
    reseq2d
    oveq2d
    @46
    @22
    @31
    cG
    cgsu
    vj
    @18
    @27
    @12
    mpteq1
    oveq2d
    eqeq12d
    imbi2d
    @18
    @36
    wceq
    #
    @24
    @42
    wph
    @47
    @21
    @39
    @23
    @41
    @47
    @20
    @38
    cG
    cgsu
    @47
    @19
    @37
    cF
    @18
    @36
    cA
    reseq2
    reseq2d
    oveq2d
    @47
    @22
    @40
    cG
    cgsu
    vj
    @18
    @36
    @12
    mpteq1
    oveq2d
    eqeq12d
    imbi2d
    @18
    @1
    wceq
    #
    @24
    @15
    wph
    @48
    @21
    @5
    @23
    @14
    @48
    @20
    @4
    cG
    cgsu
    @48
    @19
    @3
    cF
    @18
    @1
    cA
    reseq2
    reseq2d
    oveq2d
    @48
    @22
    @13
    cG
    cgsu
    vj
    @18
    @1
    @12
    mpteq1
    oveq2d
    eqeq12d
    imbi2d
    wph
    @25
    eqidd
    @27
    cfn
    wcel
    #
    vz
    vy
    wel
    wn
    #
    wa
    #
    wph
    @33
    @42
    wph
    @51
    @33
    @42
    wi
    @33
    @42
    wph
    @51
    wa
    #
    @30
    cG
    cF
    cA
    @35
    cres
    #
    cres
    #
    cgsu
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @32
    @55
    @56
    co
    #
    wceq
    @30
    @32
    @55
    @56
    oveq1
    @52
    @39
    @57
    @41
    @58
    @52
    @39
    cG
    @38
    @28
    cres
    #
    cgsu
    co
    #
    cG
    @38
    @53
    cres
    #
    cgsu
    co
    #
    @56
    co
    @57
    @52
    @37
    cB
    @28
    @53
    @56
    @38
    cG
    cvv
    c.0
    gsum2d.b
    gsum2d.z
    @56
    eqid
    #
    wph
    cG
    ccmn
    wcel
    @51
    gsum2d.g
    adantr
    #
    wph
    @37
    cvv
    wcel
    #
    @51
    wph
    cA
    cV
    wcel
    #
    @65
    gsum2d.a
    cA
    @36
    cV
    resexg
    syl
    adantr
    wph
    @37
    cB
    @38
    wf
    #
    @51
    wph
    cA
    cB
    cF
    wf
    #
    @37
    cA
    wss
    @67
    gsum2d.f
    cA
    @36
    resss
    cA
    cB
    @37
    cF
    fssres
    sylancl
    adantr
    @52
    @38
    c.0
    cfsupp
    wbr
    #
    @38
    wfun
    #
    @38
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    @70
    @51
    wph
    cF
    wfun
    #
    @70
    wph
    @68
    @73
    gsum2d.f
    cA
    cB
    cF
    ffun
    syl
    @37
    cF
    funres
    syl
    adantr
    @52
    @16
    @71
    @0
    wss
    #
    @72
    wph
    @16
    @51
    @17
    adantr
    wph
    @74
    @51
    wph
    cF
    cvv
    wcel
    #
    c.0
    cvv
    wcel
    #
    @74
    wph
    @68
    @66
    @75
    gsum2d.f
    gsum2d.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    #
    c.0
    cG
    c0g
    cfv
    cvv
    gsum2d.z
    cG
    c0g
    fvex
    eqeltri
    #
    @37
    cF
    cvv
    cvv
    c.0
    ressuppss
    sylancl
    adantr
    @0
    @71
    ssfi
    syl2anc
    wph
    @69
    @70
    @72
    wa
    wb
    #
    @51
    wph
    @38
    cvv
    wcel
    #
    @76
    @79
    wph
    @75
    @80
    @77
    cF
    @37
    cvv
    resexg
    syl
    @78
    @38
    cvv
    cvv
    c.0
    isfsupp
    sylancl
    adantr
    mpbir2and
    @52
    cA
    @27
    @35
    cin
    #
    cres
    @44
    @28
    @53
    cin
    c0
    @52
    @81
    c0
    cA
    @52
    @50
    @81
    c0
    wceq
    wph
    @49
    @50
    simprr
    #
    @27
    @34
    disjsn
    sylibr
    reseq2d
    cA
    @27
    @35
    resindi
    @45
    3eqtr3g
    @37
    @28
    @53
    cun
    wceq
    @52
    cA
    @27
    @35
    resundi
    a1i
    gsumsplit
    @60
    @30
    @62
    @55
    @56
    @59
    @29
    cG
    cgsu
    @27
    @36
    wss
    @28
    @37
    wss
    @59
    @29
    wceq
    @27
    @35
    ssun1
    @27
    @36
    cA
    ssres2
    cF
    @28
    @37
    resabs1
    mp2b
    oveq2i
    @61
    @54
    cG
    cgsu
    @35
    @36
    wss
    @53
    @37
    wss
    @61
    @54
    wceq
    @35
    @27
    ssun2
    @35
    @36
    cA
    ssres2
    cF
    @53
    @37
    resabs1
    mp2b
    oveq2i
    oveq12i
    syl6eq
    @52
    @41
    @32
    cG
    vk
    cA
    @35
    cima
    #
    @34
    @9
    cF
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @56
    co
    @58
    @52
    @27
    cB
    @56
    vj
    cG
    @34
    cvv
    @12
    @86
    gsum2d.b
    @63
    @64
    wph
    @49
    @50
    simprl
    wph
    @12
    cB
    wcel
    #
    @51
    vj
    vy
    wel
    wph
    cA
    cB
    cD
    vj
    vk
    cF
    cG
    cV
    cW
    c.0
    gsum2d.b
    gsum2d.z
    gsum2d.g
    gsum2d.a
    gsum2d.r
    gsum2d.d
    gsum2d.s
    gsum2d.f
    gsum2d.w
    gsum2dlem1
    #
    ad2antrr
    @34
    cvv
    wcel
    @52
    vz
    vex
    a1i
    @82
    wph
    @86
    cB
    wcel
    #
    @51
    wph
    @87
    wi
    wph
    @89
    wi
    vj
    vz
    vj
    vz
    weq
    #
    @87
    @89
    wph
    @90
    @12
    @86
    cB
    @90
    @11
    @85
    cG
    cgsu
    @90
    vk
    @8
    @10
    @83
    @84
    @90
    @7
    @35
    cA
    @6
    @34
    sneq
    #
    imaeq2d
    @6
    @34
    @9
    cF
    oveq1
    mpteq12dv
    oveq2d
    #
    eleq1d
    imbi2d
    @88
    chvarv
    adantr
    @92
    gsumunsn
    @52
    @86
    @55
    @32
    @56
    wph
    @86
    @55
    wceq
    #
    @51
    wph
    @12
    cG
    cF
    cA
    @7
    cres
    #
    cres
    #
    cgsu
    co
    #
    wceq
    #
    wi
    wph
    @93
    wi
    vj
    vz
    @90
    @97
    @93
    wph
    @90
    @12
    @86
    @96
    @55
    @92
    @90
    @95
    @54
    cG
    cgsu
    @90
    @94
    @53
    cF
    @90
    @7
    @35
    cA
    @91
    reseq2d
    reseq2d
    oveq2d
    eqeq12d
    imbi2d
    wph
    @12
    cG
    @11
    c2nd
    @7
    @8
    cxp
    #
    cres
    #
    ccom
    #
    cgsu
    co
    @96
    wph
    @8
    cB
    @98
    @11
    cG
    @99
    cvv
    c.0
    gsum2d.b
    gsum2d.z
    gsum2d.g
    wph
    @66
    @8
    cvv
    wcel
    #
    gsum2d.a
    cA
    @7
    cV
    imaexg
    syl
    #
    wph
    vk
    @8
    @10
    cB
    @11
    @9
    @8
    wcel
    #
    wph
    @6
    @9
    cop
    #
    cA
    wcel
    #
    @10
    cB
    wcel
    cA
    @6
    @9
    vj
    vex
    #
    vk
    vex
    #
    elimasn
    #
    wph
    @105
    wa
    @10
    @104
    cF
    cfv
    #
    cB
    @6
    @9
    cF
    df-ov
    #
    wph
    cA
    cB
    @104
    cF
    gsum2d.f
    ffvelrnda
    syl5eqel
    sylan2b
    @11
    eqid
    fmptd
    wph
    @11
    c.0
    cfsupp
    wbr
    #
    @11
    wfun
    #
    @11
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    @112
    wph
    vk
    @8
    @10
    funmpt
    a1i
    wph
    @0
    crn
    #
    cfn
    wcel
    #
    @113
    @115
    wss
    @114
    wph
    @16
    @116
    @17
    @0
    rnfi
    syl
    wph
    @8
    @10
    vk
    cvv
    @115
    c.0
    @9
    @8
    @115
    cdif
    wcel
    #
    wph
    @104
    cA
    @0
    cdif
    wcel
    #
    @10
    c.0
    wceq
    @103
    @9
    @115
    wcel
    #
    wn
    #
    wa
    @105
    @104
    @0
    wcel
    #
    wn
    #
    wa
    @117
    @118
    @103
    @105
    @120
    @122
    @103
    @105
    @108
    biimpi
    @121
    @119
    @6
    @9
    @0
    @106
    @107
    opelrn
    con3i
    anim12i
    @9
    @8
    @115
    eldif
    @104
    cA
    @0
    eldif
    3imtr4i
    wph
    @118
    wa
    @10
    @109
    c.0
    @110
    wph
    cA
    cB
    cvv
    cF
    cV
    @0
    @104
    c.0
    gsum2d.f
    @0
    @0
    wss
    wph
    @0
    ssid
    a1i
    gsum2d.a
    @76
    wph
    @78
    a1i
    suppssr
    syl5eq
    sylan2
    @102
    suppss2
    @115
    @113
    ssfi
    syl2anc
    wph
    @11
    cvv
    wcel
    #
    @76
    @111
    @112
    @114
    wa
    wb
    wph
    @101
    @123
    @102
    vk
    @8
    @10
    cvv
    mptexg
    syl
    @78
    @11
    cvv
    cvv
    c.0
    isfsupp
    sylancl
    mpbir2and
    @6
    cvv
    wcel
    @98
    @8
    @99
    wf1o
    wph
    @106
    @6
    @8
    cvv
    2ndconst
    mp1i
    gsumf1o
    wph
    @95
    @100
    cG
    cgsu
    wph
    vx
    @98
    @18
    cF
    cfv
    #
    cmpt
    #
    vx
    @98
    @6
    @18
    c2nd
    cfv
    #
    cF
    co
    #
    cmpt
    @95
    @100
    vx
    @98
    @124
    @127
    @18
    @98
    wcel
    #
    @124
    @6
    @126
    cop
    #
    cF
    cfv
    @127
    @128
    @18
    @129
    cF
    @128
    @18
    @18
    c1st
    cfv
    #
    @126
    cop
    @129
    @18
    @7
    @8
    1st2nd2
    @128
    @130
    @6
    @126
    @128
    @130
    @7
    wcel
    @130
    @6
    wceq
    @18
    @7
    @8
    xp1st
    @130
    @6
    elsni
    syl
    opeq1d
    eqtrd
    fveq2d
    @6
    @126
    cF
    df-ov
    syl6eqr
    mpteq2ia
    wph
    @95
    vx
    cA
    @124
    cmpt
    #
    @94
    cres
    #
    @125
    wph
    cF
    @131
    @94
    wph
    vx
    cA
    cB
    cF
    gsum2d.f
    feqmptd
    reseq1d
    @132
    vx
    @94
    @124
    cmpt
    #
    @125
    @94
    cA
    wss
    @132
    @133
    wceq
    cA
    @7
    resss
    vx
    cA
    @94
    @124
    resmpt
    ax-mp
    @94
    @98
    wceq
    @133
    @125
    wceq
    cA
    @6
    ressn
    vx
    @94
    @98
    @124
    mpteq1
    ax-mp
    eqtri
    syl6eq
    wph
    vx
    vk
    @98
    @8
    @126
    @10
    @127
    @99
    @11
    @128
    @126
    @8
    wcel
    wph
    @18
    @7
    @8
    xp2nd
    adantl
    wph
    @99
    vx
    cvv
    @126
    cmpt
    #
    @98
    cres
    #
    vx
    @98
    @126
    cmpt
    #
    wph
    c2nd
    @134
    @98
    wph
    vx
    cvv
    cvv
    c2nd
    cvv
    cvv
    c2nd
    wfo
    cvv
    cvv
    c2nd
    wf
    wph
    fo2nd
    cvv
    cvv
    c2nd
    fof
    mp1i
    feqmptd
    reseq1d
    @98
    cvv
    wss
    @135
    @136
    wceq
    @98
    ssv
    vx
    cvv
    @98
    @126
    resmpt
    ax-mp
    syl6eq
    wph
    @11
    eqidd
    @9
    @126
    @6
    cF
    oveq2
    fmptco
    3eqtr4a
    oveq2d
    eqtr4d
    chvarv
    adantr
    oveq2d
    eqtrd
    eqeq12d
    syl5ibr
    expcom
    a2d
    findcard2s
    mpcom
end
