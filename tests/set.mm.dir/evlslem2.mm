include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cmulr.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cvv.mm"
include "c0g.mm"
include "eqid.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "a1i.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "mplring.mm"
include "syl2anc.mm"
include "adantr.mm"
include "cbs.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "mplelf.mm"
include "ffvelrnda.mm"
include "simpr.mm"
include "mplmon2cl.mm"
include "simprr.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wral.mm"
include "wfun.mm"
include "w3a.mm"
include "csupp.mm"
include "wss.mm"
include "mptex.mm"
include "funmpt.mm"
include "fvex.mm"
include "3pm3.2i.mm"
include "mplelsfi.mm"
include "fsuppimpd.mm"
include "cdif.mm"
include "ssid.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "ifeq1d.mm"
include "ifid.mm"
include "syl6eq.mm"
include "mpteq2dv.mm"
include "wceq.mm"
include "csn.mm"
include "cxp.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "mpl0.mm"
include "fconstmpt.mm"
include "eqtr4d.mm"
include "suppss2.mm"
include "suppssfifsupp.mm"
include "syl12anc.mm"
include "ralrimiva.mm"
include "fveq1.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "adantrr.mm"
include "equequ2.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "cbvmptv.mm"
include "adantrl.mm"
include "syl5eqbr.mm"
include "gsumdixp.mm"
include "fveq2d.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "xpex.mm"
include "cmhm.mm"
include "cghm.mm"
include "ghmmhm.mm"
include "wf.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "mpt2ex.mm"
include "mpt2fun.mm"
include "xpfi.mm"
include "evlslem4.mm"
include "gsummhm.mm"
include "caddc.mm"
include "cof.mm"
include "mplmon2mul.mm"
include "anassrs.mm"
include "eqtrd.mm"
include "3impb.mm"
include "mpt2eq3dva.mm"
include "oveq2d.mm"
include "eqidd.mm"
include "ghmf.mm"
include "feqmptd.mm"
include "fmpt2co.mm"
include "fmptco.mm"
include "oveq12d.mm"
include "ffvelrnd.mm"
include "ghmid.mm"
include "suppssfv.mm"
include "3eqtr4d.mm"
include "3eqtr2d.mm"
include "mplcoe4.mm"
include "fmptd.mm"

theorem evlslem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cI: class I
  let c.0: class .0.
  let vz: setvar z
  assume evlslem2.p: |- P = ( I mPoly R )
  assume evlslem2.b: |- B = ( Base ` P )
  assume evlslem2.m: |- .x. = ( .r ` S )
  assume evlslem2.z: |- .0. = ( 0g ` R )
  assume evlslem2.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume evlslem2.i: |- ( ph -> I e. _V )
  assume evlslem2.r: |- ( ph -> R e. CRing )
  assume evlslem2.s: |- ( ph -> S e. CRing )
  assume evlslem2.e1: |- ( ph -> E e. ( P GrpHom S ) )
  assume evlslem2.e2: |- ( ( ph /\ ( ( x e. B /\ y e. B ) /\ ( j e. D /\ i e. D ) ) ) -> ( E ` ( k e. D |-> if ( k = ( j oF + i ) , ( ( x ` j ) ( .r ` R ) ( y ` i ) ) , .0. ) ) ) = ( ( E ` ( k e. D |-> if ( k = j , ( x ` j ) , .0. ) ) ) .x. ( E ` ( k e. D |-> if ( k = i , ( y ` i ) , .0. ) ) ) ) )

  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph y
  disjoint i j
  disjoint i k
  disjoint i y
  disjoint j k
  disjoint j y
  disjoint k y
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint i x
  disjoint j x
  disjoint k x
  disjoint x y
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D x
  disjoint D y
  disjoint E i
  disjoint E j
  disjoint I h
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint h i
  disjoint h j
  disjoint h k
  disjoint .x. i
  disjoint .x. j
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint R h
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint S i
  disjoint S j
  disjoint .0. h
  disjoint .0. i
  disjoint .0. j
  disjoint .0. k
  disjoint .0. x
  disjoint .0. y
  disjoint h x
  disjoint h y
  disjoint B z
  disjoint i z
  disjoint j z
  disjoint k z
  disjoint x z
  disjoint y z
  disjoint D z
  disjoint E z
  disjoint P z
  disjoint .0. z
  assert |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( E ` ( x ( .r ` P ) y ) ) = ( ( E ` x ) .x. ( E ` y ) ) )

  proof
    wph
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    #
    cP
    vj
    cD
    vk
    cD
    vk
    vj
    weq
    #
    vj
    cv
    #
    @0
    cfv
    #
    c.0
    cif
    #
    cmpt
    #
    cmpt
    #
    cgsu
    co
    #
    cP
    vi
    cD
    vk
    cD
    vk
    vi
    weq
    #
    vi
    cv
    #
    @2
    cfv
    #
    c.0
    cif
    #
    cmpt
    #
    cmpt
    #
    cgsu
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    cE
    cfv
    #
    cS
    cE
    @11
    ccom
    #
    cgsu
    co
    #
    cS
    cE
    @18
    ccom
    #
    cgsu
    co
    #
    c.x
    co
    #
    @0
    @2
    @20
    co
    #
    cE
    cfv
    @0
    cE
    cfv
    #
    @2
    cE
    cfv
    #
    c.x
    co
    @5
    @22
    cP
    vj
    vi
    cD
    cD
    @10
    @17
    @20
    co
    #
    cmpt2
    #
    cgsu
    co
    #
    cE
    cfv
    cS
    cE
    @32
    ccom
    #
    cgsu
    co
    #
    @27
    @5
    @21
    @33
    cE
    @5
    vj
    vi
    cB
    cP
    @20
    cD
    cD
    cvv
    cvv
    @10
    @17
    cP
    c0g
    cfv
    #
    evlslem2.b
    @20
    eqid
    #
    @36
    eqid
    #
    cD
    cvv
    wcel
    #
    @5
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    cI
    cmap
    co
    cD
    evlslem2.d
    cn0
    cI
    cmap
    ovex
    rabex2
    #
    a1i
    #
    @41
    wph
    cP
    crg
    wcel
    #
    @4
    wph
    cI
    cvv
    wcel
    #
    cR
    crg
    wcel
    #
    @42
    evlslem2.i
    wph
    cR
    ccrg
    wcel
    #
    @44
    evlslem2.r
    cR
    crngring
    syl
    #
    cP
    cR
    cI
    cvv
    evlslem2.p
    mplring
    syl2anc
    #
    adantr
    #
    @5
    @7
    cD
    wcel
    #
    wa
    #
    vk
    cB
    cR
    cbs
    cfv
    #
    cD
    cP
    cR
    vh
    cI
    @7
    cvv
    @8
    c.0
    evlslem2.p
    evlslem2.d
    evlslem2.z
    @51
    eqid
    #
    wph
    @43
    @4
    @49
    evlslem2.i
    ad2antrr
    wph
    @44
    @4
    @49
    @46
    ad2antrr
    evlslem2.b
    @5
    cD
    @51
    @7
    @0
    @5
    cB
    cD
    cP
    cR
    vh
    cI
    @51
    @0
    evlslem2.p
    @52
    evlslem2.b
    evlslem2.d
    wph
    @1
    @3
    simprl
    #
    mplelf
    ffvelrnda
    #
    @5
    @49
    simpr
    mplmon2cl
    #
    @5
    @14
    cD
    wcel
    #
    wa
    #
    vk
    cB
    @51
    cD
    cP
    cR
    vh
    cI
    @14
    cvv
    @15
    c.0
    evlslem2.p
    evlslem2.d
    evlslem2.z
    @52
    wph
    @43
    @4
    @56
    evlslem2.i
    ad2antrr
    wph
    @44
    @4
    @56
    @46
    ad2antrr
    evlslem2.b
    @5
    cD
    @51
    @14
    @2
    @5
    cB
    cD
    cP
    cR
    vh
    cI
    @51
    @2
    evlslem2.p
    @52
    evlslem2.b
    evlslem2.d
    wph
    @1
    @3
    simprr
    #
    mplelf
    ffvelrnda
    #
    @5
    @56
    simpr
    mplmon2cl
    #
    wph
    @1
    @11
    @36
    cfsupp
    wbr
    #
    @3
    wph
    @61
    vx
    cB
    wph
    vj
    cD
    vk
    cD
    @6
    @7
    @2
    cfv
    #
    c.0
    cif
    #
    cmpt
    #
    cmpt
    #
    @36
    cfsupp
    wbr
    #
    vy
    cB
    wral
    @61
    vx
    cB
    wral
    wph
    @66
    vy
    cB
    wph
    @3
    wa
    #
    @65
    cvv
    wcel
    #
    @65
    wfun
    #
    @36
    cvv
    wcel
    #
    w3a
    #
    @2
    c.0
    csupp
    co
    #
    cfn
    wcel
    @65
    @36
    csupp
    co
    @72
    wss
    @66
    @71
    @67
    @68
    @69
    @70
    vj
    cD
    @64
    @40
    mptex
    vj
    cD
    @64
    funmpt
    cP
    c0g
    fvex
    #
    3pm3.2i
    a1i
    @67
    @2
    c.0
    @67
    cB
    cP
    cR
    @2
    cI
    ccrg
    c.0
    evlslem2.p
    evlslem2.b
    evlslem2.z
    wph
    @3
    simpr
    #
    wph
    @45
    @3
    evlslem2.r
    adantr
    mplelsfi
    fsuppimpd
    @67
    cD
    @64
    vj
    cvv
    @72
    @36
    @67
    @7
    cD
    @72
    cdif
    wcel
    #
    wa
    #
    @64
    vk
    cD
    c.0
    cmpt
    #
    @36
    @76
    vk
    cD
    @63
    c.0
    @76
    @63
    @6
    c.0
    c.0
    cif
    c.0
    @76
    @6
    @62
    c.0
    c.0
    @67
    cD
    @51
    cvv
    @2
    cvv
    @72
    @7
    c.0
    @67
    cB
    cD
    cP
    cR
    vh
    cI
    @51
    @2
    evlslem2.p
    @52
    evlslem2.b
    evlslem2.d
    @74
    mplelf
    @72
    @72
    wss
    @67
    @72
    ssid
    a1i
    @39
    @67
    @40
    a1i
    #
    c.0
    cvv
    wcel
    @67
    c.0
    cR
    c0g
    cfv
    cvv
    evlslem2.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    suppssr
    ifeq1d
    @6
    c.0
    ifid
    syl6eq
    mpteq2dv
    wph
    @36
    @77
    wceq
    @3
    @75
    wph
    @36
    cD
    c.0
    csn
    cxp
    @77
    wph
    cD
    cP
    cR
    vh
    cI
    c.0
    cvv
    @36
    evlslem2.p
    evlslem2.d
    evlslem2.z
    @38
    evlslem2.i
    wph
    @44
    cR
    cgrp
    wcel
    @46
    cR
    ringgrp
    syl
    mpl0
    vk
    cD
    c.0
    fconstmpt
    syl6eq
    ad2antrr
    eqtr4d
    @78
    suppss2
    @72
    @65
    cvv
    cvv
    @36
    suppssfifsupp
    syl12anc
    #
    ralrimiva
    @66
    @61
    vy
    vx
    cB
    vy
    vx
    weq
    #
    @65
    @11
    @36
    cfsupp
    @80
    vj
    cD
    @64
    @10
    @80
    vk
    cD
    @63
    @9
    @80
    @6
    @62
    @8
    c.0
    @7
    @2
    @0
    fveq1
    ifeq1d
    mpteq2dv
    mpteq2dv
    breq1d
    cbvralv
    sylib
    r19.21bi
    adantrr
    #
    @5
    @18
    @65
    @36
    cfsupp
    vi
    vj
    cD
    @17
    @64
    vi
    vj
    weq
    #
    vk
    cD
    @16
    @63
    @82
    @13
    @6
    @15
    @62
    c.0
    vi
    vj
    vk
    equequ2
    @14
    @7
    @2
    fveq2
    ifbieq1d
    mpteq2dv
    cbvmptv
    wph
    @3
    @66
    @1
    @79
    adantrl
    syl5eqbr
    #
    gsumdixp
    fveq2d
    @5
    cD
    cD
    cxp
    #
    cB
    @32
    cP
    cS
    cE
    cvv
    @36
    evlslem2.b
    @38
    wph
    cP
    ccmn
    wcel
    #
    @4
    wph
    @42
    @85
    @47
    cP
    ringcmn
    syl
    adantr
    #
    @5
    cS
    crg
    wcel
    #
    cS
    cmnd
    wcel
    wph
    @87
    @4
    wph
    cS
    ccrg
    wcel
    @87
    evlslem2.s
    cS
    crngring
    syl
    adantr
    #
    cS
    ringmnd
    syl
    #
    @84
    cvv
    wcel
    @5
    cD
    cD
    @40
    @40
    xpex
    a1i
    wph
    cE
    cP
    cS
    cmhm
    co
    wcel
    #
    @4
    wph
    cE
    cP
    cS
    cghm
    co
    wcel
    #
    @90
    evlslem2.e1
    cP
    cS
    cE
    ghmmhm
    syl
    adantr
    #
    @5
    @31
    cB
    wcel
    #
    vi
    cD
    wral
    vj
    cD
    wral
    @84
    cB
    @32
    wf
    @5
    @93
    vj
    vi
    cD
    cD
    @5
    @49
    @56
    wa
    #
    wa
    #
    @42
    @10
    cB
    wcel
    #
    @17
    cB
    wcel
    #
    @93
    wph
    @42
    @4
    @94
    @47
    ad2antrr
    @5
    @49
    @96
    @56
    @55
    adantrr
    @5
    @56
    @97
    @49
    @60
    adantrl
    cB
    cP
    @20
    @10
    @17
    evlslem2.b
    @37
    ringcl
    syl3anc
    #
    ralrimivva
    vj
    vi
    cD
    cD
    @31
    cB
    @32
    @32
    eqid
    #
    fmpt2
    sylib
    @5
    @32
    cvv
    wcel
    #
    @32
    wfun
    #
    @70
    w3a
    #
    @11
    @36
    csupp
    co
    #
    @18
    @36
    csupp
    co
    #
    cxp
    #
    cfn
    wcel
    #
    @32
    @36
    csupp
    co
    @105
    wss
    @32
    @36
    cfsupp
    wbr
    @102
    @5
    @100
    @101
    @70
    vj
    vi
    cD
    cD
    @31
    @40
    @40
    mpt2ex
    vj
    vi
    cD
    cD
    @31
    @32
    @99
    mpt2fun
    @73
    3pm3.2i
    a1i
    @5
    @103
    cfn
    wcel
    #
    @104
    cfn
    wcel
    #
    @106
    @5
    @11
    @36
    @81
    fsuppimpd
    #
    @5
    @18
    @36
    @83
    fsuppimpd
    #
    @103
    @104
    xpfi
    syl2anc
    @5
    vj
    vi
    cB
    cP
    @20
    cD
    cD
    cvv
    cvv
    @10
    @17
    @36
    evlslem2.b
    @38
    @37
    @48
    @55
    @60
    @41
    @41
    evlslem4
    @105
    @32
    cvv
    cvv
    @36
    suppssfifsupp
    syl12anc
    gsummhm
    @5
    cS
    vj
    vi
    cD
    cD
    @31
    cE
    cfv
    #
    cmpt2
    #
    cgsu
    co
    cS
    vj
    vi
    cD
    cD
    @10
    cE
    cfv
    #
    @17
    cE
    cfv
    #
    c.x
    co
    #
    cmpt2
    #
    cgsu
    co
    #
    @35
    @27
    @5
    @112
    @116
    cS
    cgsu
    @5
    vj
    vi
    cD
    cD
    @111
    @115
    @5
    @49
    @56
    @111
    @115
    wceq
    @95
    @111
    vk
    cD
    vk
    cv
    @7
    @14
    caddc
    cof
    co
    wceq
    @8
    @15
    cR
    cmulr
    cfv
    #
    co
    c.0
    cif
    cmpt
    #
    cE
    cfv
    #
    @115
    @95
    @31
    @119
    cE
    @95
    vk
    @51
    cD
    cP
    cR
    @20
    @118
    vh
    @8
    @15
    cI
    cvv
    @7
    @14
    c.0
    evlslem2.p
    evlslem2.d
    evlslem2.z
    @52
    wph
    @43
    @4
    @94
    evlslem2.i
    ad2antrr
    wph
    @45
    @4
    @94
    evlslem2.r
    ad2antrr
    @37
    @118
    eqid
    @5
    @49
    @56
    simprl
    @5
    @49
    @56
    simprr
    @5
    @49
    @8
    @51
    wcel
    @56
    @54
    adantrr
    @5
    @56
    @15
    @51
    wcel
    @49
    @59
    adantrl
    mplmon2mul
    fveq2d
    wph
    @4
    @94
    @120
    @115
    wceq
    evlslem2.e2
    anassrs
    eqtrd
    3impb
    mpt2eq3dva
    oveq2d
    @5
    @34
    @112
    cS
    cgsu
    @5
    vj
    vi
    vz
    cD
    cD
    cB
    @31
    vz
    cv
    #
    cE
    cfv
    #
    @111
    @32
    cE
    @98
    @5
    @32
    eqidd
    wph
    cE
    vz
    cB
    @122
    cmpt
    wceq
    @4
    wph
    vz
    cB
    cS
    cbs
    cfv
    #
    cE
    wph
    @91
    cB
    @123
    cE
    wf
    #
    evlslem2.e1
    cP
    cS
    cE
    cB
    @123
    evlslem2.b
    @123
    eqid
    #
    ghmf
    syl
    #
    feqmptd
    adantr
    #
    @121
    @31
    cE
    fveq2
    fmpt2co
    oveq2d
    @5
    @27
    cS
    vj
    cD
    @113
    cmpt
    #
    cgsu
    co
    #
    cS
    vi
    cD
    @114
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    @117
    @5
    @24
    @129
    @26
    @131
    c.x
    @5
    @23
    @128
    cS
    cgsu
    @5
    vj
    vz
    cD
    cB
    @10
    @122
    @113
    @11
    cE
    @55
    @5
    @11
    eqidd
    @127
    @121
    @10
    cE
    fveq2
    fmptco
    oveq2d
    @5
    @25
    @130
    cS
    cgsu
    @5
    vi
    vz
    cD
    cB
    @17
    @122
    @114
    @18
    cE
    @60
    @5
    @18
    eqidd
    @127
    @121
    @17
    cE
    fveq2
    fmptco
    oveq2d
    oveq12d
    @5
    vj
    vi
    @123
    cS
    c.x
    cD
    cD
    cvv
    cvv
    @113
    @114
    cS
    c0g
    cfv
    #
    @125
    evlslem2.m
    @132
    eqid
    #
    @41
    @41
    @88
    @50
    cB
    @123
    @10
    cE
    wph
    @124
    @4
    @49
    @126
    ad2antrr
    @55
    ffvelrnd
    @57
    cB
    @123
    @17
    cE
    wph
    @124
    @4
    @56
    @126
    ad2antrr
    @60
    ffvelrnd
    @5
    @128
    cvv
    wcel
    #
    @128
    wfun
    #
    @132
    cvv
    wcel
    #
    w3a
    #
    @107
    @128
    @132
    csupp
    co
    @103
    wss
    #
    @128
    @132
    cfsupp
    wbr
    @137
    @5
    @134
    @135
    @136
    vj
    cD
    @113
    @40
    mptex
    vj
    cD
    @113
    funmpt
    cS
    c0g
    fvex
    #
    3pm3.2i
    a1i
    @109
    wph
    @138
    @4
    wph
    vj
    @10
    cD
    cvv
    cE
    @103
    cvv
    @36
    @132
    @103
    @103
    wss
    wph
    @103
    ssid
    a1i
    wph
    @91
    @36
    cE
    cfv
    @132
    wceq
    evlslem2.e1
    cP
    cS
    cE
    @36
    @132
    @38
    @133
    ghmid
    syl
    #
    @10
    cvv
    wcel
    wph
    @49
    wa
    vk
    cD
    @9
    @40
    mptex
    a1i
    @70
    wph
    @73
    a1i
    #
    suppssfv
    adantr
    @103
    @128
    cvv
    cvv
    @132
    suppssfifsupp
    syl12anc
    @5
    @130
    cvv
    wcel
    #
    @130
    wfun
    #
    @136
    w3a
    #
    @108
    @130
    @132
    csupp
    co
    @104
    wss
    #
    @130
    @132
    cfsupp
    wbr
    @144
    @5
    @142
    @143
    @136
    vi
    cD
    @114
    @40
    mptex
    vi
    cD
    @114
    funmpt
    @139
    3pm3.2i
    a1i
    @110
    wph
    @145
    @4
    wph
    vi
    @17
    cD
    cvv
    cE
    @104
    cvv
    @36
    @132
    @104
    @104
    wss
    wph
    @104
    ssid
    a1i
    @140
    @17
    cvv
    wcel
    wph
    @56
    wa
    vk
    cD
    @16
    @40
    mptex
    a1i
    @141
    suppssfv
    adantr
    @104
    @130
    cvv
    cvv
    @132
    suppssfifsupp
    syl12anc
    gsumdixp
    eqtrd
    3eqtr4d
    3eqtr2d
    @5
    @28
    @21
    cE
    @5
    @0
    @12
    @2
    @19
    @20
    @5
    vk
    cB
    cD
    cP
    cR
    vh
    vj
    cI
    cvv
    @0
    c.0
    evlslem2.p
    evlslem2.d
    evlslem2.z
    evlslem2.b
    wph
    @43
    @4
    evlslem2.i
    adantr
    #
    wph
    @44
    @4
    @46
    adantr
    #
    @53
    mplcoe4
    #
    @5
    vk
    cB
    cD
    cP
    cR
    vh
    vi
    cI
    cvv
    @2
    c.0
    evlslem2.p
    evlslem2.d
    evlslem2.z
    evlslem2.b
    @146
    @147
    @58
    mplcoe4
    #
    oveq12d
    fveq2d
    @5
    @29
    @24
    @30
    @26
    c.x
    @5
    @29
    @12
    cE
    cfv
    @24
    @5
    @0
    @12
    cE
    @148
    fveq2d
    @5
    cD
    cB
    @11
    cP
    cS
    cE
    cvv
    @36
    evlslem2.b
    @38
    @86
    @89
    @41
    @92
    @5
    vj
    cD
    @10
    cB
    @11
    @55
    @11
    eqid
    fmptd
    @81
    gsummhm
    eqtr4d
    @5
    @30
    @19
    cE
    cfv
    @26
    @5
    @2
    @19
    cE
    @149
    fveq2d
    @5
    cD
    cB
    @18
    cP
    cS
    cE
    cvv
    @36
    evlslem2.b
    @38
    @86
    @89
    @41
    @92
    @5
    vi
    cD
    @17
    cB
    @18
    @60
    @18
    eqid
    fmptd
    @83
    gsummhm
    eqtr4d
    oveq12d
    3eqtr4d
end
