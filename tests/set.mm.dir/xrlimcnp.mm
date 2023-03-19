include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "cpnf.mm"
include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "fmptd.mm"
include "adantr.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "ssun2.mm"
include "pnfex.mm"
include "snid.mm"
include "sselii.mm"
include "syl5eleqr.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "crp.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "cnfldtopn.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "cle.mm"
include "clt.mm"
include "cr.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "ssralv.mm"
include "simprl.mm"
include "simplr.mm"
include "rlimi.mm"
include "cioc.mm"
include "cin.mm"
include "cordt.mm"
include "crest.mm"
include "ctop.mm"
include "cvv.mm"
include "letop.mm"
include "a1i.mm"
include "cxr.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "pnfxr.mm"
include "snssd.mm"
include "unssd.mm"
include "eqsstrd.mm"
include "xrex.mm"
include "ssex.mm"
include "syl.mm"
include "iocpnfordt.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "syl6eleqr.mm"
include "rexrd.mm"
include "ltpnf.mm"
include "ubioc1.mm"
include "elind.mm"
include "ccnv.mm"
include "crab.mm"
include "w3a.mm"
include "wb.mm"
include "elioc1.mm"
include "sylancl.mm"
include "simp2.mm"
include "syl6bi.mm"
include "sselda.mm"
include "ltle.mm"
include "syld.mm"
include "rpxr.mm"
include "ad3antrrr.mm"
include "r19.21bi.mm"
include "elbl3.mm"
include "syl22anc.mm"
include "cnmetdval.mm"
include "breq1d.mm"
include "bitrd.mm"
include "biimprd.mm"
include "imim12d.mm"
include "ralimdva.mm"
include "impr.mm"
include "simplrl.mm"
include "blcntr.mm"
include "a1d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "ralsn.mm"
include "sylibr.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "ss2rab.mm"
include "incom.mm"
include "dfin5.mm"
include "eqtri.mm"
include "mptpreima.mm"
include "3sstr4g.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt.mm"
include "inss2.mm"
include "fdm.mm"
include "funimass3.mm"
include "sylancr.mm"
include "simplrr.mm"
include "sstrd.mm"
include "eleq2.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimdvaa.mm"
include "adantlr.mm"
include "mpd.mm"
include "syl5.mm"
include "expdimp.mm"
include "sylbid.mm"
include "ctopon.mm"
include "letopon.mm"
include "resttopon.mm"
include "syl5eqel.mm"
include "cnfldtopon.mm"
include "iscnp.mm"
include "mpbir2and.mm"
include "adantl.mm"
include "blopn.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "cnpimaex.mm"
include "vex.mm"
include "inex1.mm"
include "eleq2i.mm"
include "elrest.mm"
include "syl5bb.mm"
include "rexxfr2d.mm"
include "mpbid.mm"
include "inss1.mm"
include "sseli.mm"
include "pnfnei.mm"
include "sylan2.mm"
include "crn.mm"
include "cres.mm"
include "df-ima.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "rneqi.mm"
include "sseq1i.mm"
include "dfss3.mm"
include "bitri.mm"
include "mpsyl.mm"
include "ralrnmpt.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "sseldd.mm"
include "simprr.mm"
include "pnfge.mm"
include "mpbir3and.mm"
include "adantrr.mm"
include "ex.mm"
include "imim1d.mm"
include "pm5.74da.mm"
include "sylibd.mm"
include "exp4a.mm"
include "ralimdv2.mm"
include "imp.mm"
include "an32s.mm"
include "expr.mm"
include "reximdva.mm"
include "com23.mm"
include "impl.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "rlim2lt.mm"
include "impbida.mm"

theorem xrlimcnp
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cJ: class J
  let cK: class K
  let vk: setvar k
  let vr: setvar r
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume xrlimcnp.a: |- ( ph -> A = ( B u. { +oo } ) )
  assume xrlimcnp.b: |- ( ph -> B C_ RR )
  assume xrlimcnp.r: |- ( ( ph /\ x e. A ) -> R e. CC )
  assume xrlimcnp.c: |- ( x = +oo -> R = C )
  assume xrlimcnp.j: |- J = ( TopOpen ` CCfld )
  assume xrlimcnp.k: |- K = ( ( ordTop ` <_ ) |`t A )

  disjoint B x
  disjoint ph x
  disjoint A x
  disjoint C x
  disjoint k r
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint B r
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint x y
  disjoint B y
  disjoint r z
  disjoint J r
  disjoint w z
  disjoint J w
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint k z
  disjoint K k
  disjoint K r
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint k ph
  disjoint ph r
  disjoint ph w
  disjoint x z
  disjoint ph y
  disjoint ph z
  disjoint A k
  disjoint A r
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint C k
  disjoint C r
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint R k
  disjoint R r
  disjoint R w
  disjoint R y
  disjoint R z
  assert |- ( ph -> ( ( x e. B |-> R ) ~~>r C <-> ( x e. A |-> R ) e. ( ( K CnP J ) ` +oo ) ) )

  proof
    wph
    vx
    cB
    cR
    cmpt
    cC
    crli
    wbr
    #
    vx
    cA
    cR
    cmpt
    #
    cpnf
    cK
    cJ
    ccnp
    co
    cfv
    wcel
    #
    wph
    @0
    wa
    #
    @2
    cA
    cc
    @1
    wf
    #
    cpnf
    @1
    cfv
    #
    vy
    cv
    #
    wcel
    #
    cpnf
    vz
    cv
    #
    wcel
    #
    @1
    @8
    cima
    #
    @6
    wss
    #
    wa
    #
    vz
    cK
    wrex
    #
    wi
    #
    vy
    cJ
    wral
    #
    wph
    @4
    @0
    wph
    vx
    cA
    cR
    cc
    @1
    xrlimcnp.r
    @1
    eqid
    #
    fmptd
    #
    adantr
    @3
    @14
    vy
    cJ
    @3
    @6
    cJ
    wcel
    #
    wa
    #
    @7
    cC
    @6
    wcel
    #
    @13
    @19
    @5
    cC
    @6
    wph
    @5
    cC
    wceq
    #
    @0
    @18
    wph
    cpnf
    cA
    wcel
    #
    cC
    cc
    wcel
    #
    @21
    wph
    cpnf
    cB
    cpnf
    csn
    #
    cun
    #
    cA
    @24
    @25
    cpnf
    @24
    cB
    ssun2
    cpnf
    pnfex
    snid
    sselii
    xrlimcnp.a
    syl5eleqr
    #
    wph
    @22
    cR
    cc
    wcel
    #
    vx
    cA
    wral
    #
    @23
    @26
    wph
    @27
    vx
    cA
    xrlimcnp.r
    ralrimiva
    #
    @27
    @23
    vx
    cpnf
    cA
    vx
    cv
    #
    cpnf
    wceq
    #
    cR
    cC
    cc
    xrlimcnp.c
    eleq1d
    rspcv
    sylc
    #
    vx
    cpnf
    cR
    cC
    cA
    cc
    @1
    xrlimcnp.c
    @16
    fvmptg
    syl2anc
    #
    ad2antrr
    eleq1d
    @3
    @18
    @20
    @13
    @18
    @20
    wa
    cC
    vr
    cv
    #
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    @6
    wss
    #
    vr
    crp
    wrex
    #
    @3
    @13
    @35
    cc
    cxmt
    cfv
    wcel
    #
    @18
    @20
    @38
    cnxmet
    vr
    @6
    @35
    cC
    cJ
    cc
    cJ
    xrlimcnp.j
    cnfldtopn
    #
    mopni2
    mp3an1
    @3
    @37
    @13
    vr
    crp
    @3
    @34
    crp
    wcel
    #
    @37
    wa
    #
    wa
    #
    vk
    cv
    #
    @30
    cle
    wbr
    #
    cR
    cC
    cmin
    co
    cabs
    cfv
    #
    @34
    clt
    wbr
    #
    wi
    #
    vx
    cB
    wral
    #
    vk
    cr
    wrex
    #
    @13
    @43
    vk
    vx
    cB
    cR
    cC
    @34
    cc
    wph
    @27
    vx
    cB
    wral
    #
    @0
    @42
    wph
    cB
    cA
    wss
    #
    @28
    @51
    wph
    @25
    cB
    cA
    cB
    @24
    ssun1
    xrlimcnp.a
    syl5sseqr
    #
    @29
    @27
    vx
    cB
    cA
    ssralv
    sylc
    #
    ad2antrr
    @3
    @41
    @37
    simprl
    wph
    @0
    @42
    simplr
    rlimi
    wph
    @42
    @50
    @13
    wi
    @0
    wph
    @42
    wa
    #
    @49
    @13
    vk
    cr
    @55
    @44
    cr
    wcel
    #
    @49
    wa
    #
    wa
    #
    @44
    cpnf
    cioc
    co
    #
    cA
    cin
    #
    cK
    wcel
    cpnf
    @60
    wcel
    #
    @1
    @60
    cima
    #
    @6
    wss
    #
    @13
    @58
    @60
    cle
    cordt
    cfv
    #
    cA
    crest
    co
    #
    cK
    @58
    @64
    ctop
    wcel
    #
    cA
    cvv
    wcel
    #
    @59
    @64
    wcel
    #
    @60
    @65
    wcel
    @66
    @58
    letop
    a1i
    wph
    @67
    @42
    @57
    wph
    cA
    cxr
    wss
    #
    @67
    wph
    cA
    @25
    cxr
    xrlimcnp.a
    wph
    cB
    @24
    cxr
    wph
    cB
    cr
    cxr
    xrlimcnp.b
    ressxr
    syl6ss
    #
    wph
    cpnf
    cxr
    cpnf
    cxr
    wcel
    #
    wph
    pnfxr
    a1i
    snssd
    unssd
    eqsstrd
    #
    cA
    cxr
    xrex
    ssex
    syl
    #
    ad2antrr
    @68
    @58
    @44
    iocpnfordt
    a1i
    @59
    cA
    @64
    ctop
    cvv
    elrestr
    syl3anc
    xrlimcnp.k
    syl6eleqr
    @58
    @59
    cA
    cpnf
    @58
    @44
    cxr
    wcel
    #
    @71
    @44
    cpnf
    clt
    wbr
    #
    cpnf
    @59
    wcel
    #
    @58
    @44
    @55
    @56
    @49
    simprl
    #
    rexrd
    @71
    @58
    pnfxr
    a1i
    @58
    @56
    @75
    @77
    @44
    ltpnf
    syl
    @44
    cpnf
    ubioc1
    syl3anc
    wph
    @22
    @42
    @57
    @26
    ad2antrr
    elind
    @58
    @62
    @36
    @6
    @58
    @62
    @36
    wss
    #
    @60
    @1
    ccnv
    @36
    cima
    #
    wss
    #
    @58
    @30
    @59
    wcel
    #
    vx
    cA
    crab
    #
    cR
    @36
    wcel
    #
    vx
    cA
    crab
    #
    @60
    @79
    @58
    @81
    @83
    wi
    #
    vx
    cA
    wral
    #
    @82
    @84
    wss
    @58
    @86
    @85
    vx
    @25
    wral
    #
    @58
    @85
    vx
    cB
    wral
    #
    @85
    vx
    @24
    wral
    #
    @87
    @55
    @56
    @49
    @88
    @55
    @56
    wa
    #
    @48
    @85
    vx
    cB
    @90
    @30
    cB
    wcel
    #
    wa
    #
    @81
    @45
    @47
    @83
    @92
    @81
    @44
    @30
    clt
    wbr
    #
    @45
    @92
    @81
    @30
    cxr
    wcel
    #
    @93
    @30
    cpnf
    cle
    wbr
    #
    w3a
    #
    @93
    @92
    @74
    @71
    @81
    @96
    wb
    #
    @92
    @44
    @55
    @56
    @91
    simplr
    #
    rexrd
    pnfxr
    @44
    cpnf
    @30
    elioc1
    #
    sylancl
    @94
    @93
    @95
    simp2
    syl6bi
    @92
    @56
    @30
    cr
    wcel
    @93
    @45
    wi
    @98
    @90
    cB
    cr
    @30
    wph
    cB
    cr
    wss
    @42
    @56
    xrlimcnp.b
    ad2antrr
    sselda
    @44
    @30
    ltle
    syl2anc
    syld
    @92
    @83
    @47
    @92
    @83
    cR
    cC
    @35
    co
    #
    @34
    clt
    wbr
    #
    @47
    @92
    @39
    @34
    cxr
    wcel
    #
    @23
    @27
    @83
    @101
    wb
    #
    @39
    @92
    cnxmet
    a1i
    @92
    @41
    @102
    @55
    @41
    @56
    @91
    wph
    @41
    @37
    simprl
    ad2antrr
    @34
    rpxr
    #
    syl
    wph
    @23
    @42
    @56
    @91
    @32
    ad3antrrr
    #
    @90
    @27
    vx
    cB
    wph
    @51
    @42
    @56
    @54
    ad2antrr
    r19.21bi
    #
    cR
    @35
    cC
    @34
    cc
    elbl3
    #
    syl22anc
    @92
    @100
    @46
    @34
    clt
    @92
    @27
    @23
    @100
    @46
    wceq
    #
    @106
    @105
    cR
    cC
    @35
    @35
    eqid
    cnmetdval
    #
    syl2anc
    breq1d
    bitrd
    biimprd
    imim12d
    ralimdva
    impr
    @58
    @76
    cC
    @36
    wcel
    #
    wi
    #
    @89
    @58
    @110
    @76
    @58
    @39
    @23
    @41
    @110
    @39
    @58
    cnxmet
    a1i
    wph
    @23
    @42
    @57
    @32
    ad2antrr
    wph
    @41
    @37
    @57
    simplrl
    @35
    cC
    @34
    cc
    blcntr
    #
    syl3anc
    a1d
    @85
    @111
    vx
    cpnf
    pnfex
    @31
    @81
    @76
    @83
    @110
    @30
    cpnf
    @59
    eleq1
    @31
    cR
    cC
    @36
    xrlimcnp.c
    eleq1d
    imbi12d
    ralsn
    sylibr
    @85
    vx
    cB
    @24
    ralunb
    sylanbrc
    @58
    @85
    vx
    cA
    @25
    wph
    cA
    @25
    wceq
    @42
    @57
    xrlimcnp.a
    ad2antrr
    raleqdv
    mpbird
    @81
    @83
    vx
    cA
    ss2rab
    sylibr
    @60
    cA
    @59
    cin
    @82
    @59
    cA
    incom
    vx
    cA
    @59
    dfin5
    eqtri
    vx
    cA
    cR
    @36
    @1
    @16
    mptpreima
    3sstr4g
    @58
    @1
    wfun
    @60
    @1
    cdm
    #
    wss
    @78
    @80
    wb
    vx
    cA
    cR
    funmpt
    @58
    cA
    @60
    @113
    @59
    cA
    inss2
    @58
    @4
    @113
    cA
    wceq
    wph
    @4
    @42
    @57
    @17
    ad2antrr
    cA
    cc
    @1
    fdm
    syl
    syl5sseqr
    @60
    @36
    @1
    funimass3
    sylancr
    mpbird
    wph
    @41
    @37
    @57
    simplrr
    sstrd
    @12
    @61
    @63
    wa
    vz
    @60
    cK
    @8
    @60
    wceq
    #
    @9
    @61
    @11
    @63
    @8
    @60
    cpnf
    eleq2
    @114
    @10
    @62
    @6
    @8
    @60
    @1
    imaeq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    rexlimdvaa
    adantlr
    mpd
    rexlimdvaa
    syl5
    expdimp
    sylbid
    ralrimiva
    wph
    @2
    @4
    @15
    wa
    wb
    #
    @0
    wph
    cK
    cA
    ctopon
    cfv
    #
    wcel
    cJ
    cc
    ctopon
    cfv
    wcel
    #
    @22
    @115
    wph
    cK
    @65
    @116
    xrlimcnp.k
    wph
    @64
    cxr
    ctopon
    cfv
    wcel
    @69
    @65
    @116
    wcel
    letopon
    @72
    cA
    @64
    cxr
    resttopon
    sylancr
    syl5eqel
    @117
    wph
    cJ
    xrlimcnp.j
    cnfldtopon
    a1i
    @26
    vz
    vy
    cpnf
    @1
    cK
    cJ
    cA
    cc
    iscnp
    syl3anc
    adantr
    mpbir2and
    wph
    @2
    wa
    #
    @0
    @93
    @47
    wi
    #
    vx
    cB
    wral
    #
    vk
    cr
    wrex
    #
    vr
    crp
    wral
    #
    @118
    @121
    vr
    crp
    @118
    @41
    wa
    #
    cpnf
    vw
    cv
    #
    cA
    cin
    #
    wcel
    #
    @1
    @125
    cima
    #
    @36
    wss
    #
    wa
    #
    vw
    @64
    wrex
    #
    @121
    @123
    @9
    @10
    @36
    wss
    #
    wa
    #
    vz
    cK
    wrex
    #
    @130
    @123
    @2
    @36
    cJ
    wcel
    #
    @5
    @36
    wcel
    @133
    wph
    @2
    @41
    simplr
    @123
    @39
    @23
    @102
    @134
    @39
    @123
    cnxmet
    a1i
    #
    wph
    @23
    @2
    @41
    @32
    ad2antrr
    #
    @41
    @102
    @118
    @104
    adantl
    @35
    cC
    @34
    cJ
    cc
    @40
    blopn
    syl3anc
    @123
    @5
    cC
    @36
    wph
    @21
    @2
    @41
    @33
    ad2antrr
    @123
    @39
    @23
    @41
    @110
    @135
    @136
    @118
    @41
    simpr
    @112
    syl3anc
    eqeltrd
    vz
    @36
    cpnf
    @1
    cK
    cJ
    cnpimaex
    syl3anc
    @123
    @132
    @129
    vz
    vw
    @125
    cK
    @64
    cvv
    @125
    cvv
    wcel
    @123
    @124
    @64
    wcel
    #
    wa
    @124
    cA
    vw
    vex
    inex1
    a1i
    @8
    cK
    wcel
    @8
    @65
    wcel
    #
    @123
    @8
    @125
    wceq
    #
    vw
    @64
    wrex
    #
    cK
    @65
    @8
    xrlimcnp.k
    eleq2i
    @123
    @66
    @67
    @138
    @140
    wb
    letop
    wph
    @67
    @2
    @41
    @73
    ad2antrr
    vw
    @8
    cA
    @64
    ctop
    cvv
    elrest
    sylancr
    syl5bb
    @139
    @132
    @129
    wb
    @123
    @139
    @9
    @126
    @131
    @128
    @8
    @125
    cpnf
    eleq2
    @139
    @10
    @127
    @36
    @8
    @125
    @1
    imaeq2
    sseq1d
    anbi12d
    adantl
    rexxfr2d
    mpbid
    wph
    @41
    @130
    @121
    wi
    @2
    wph
    @41
    wa
    #
    @129
    @121
    vw
    @64
    @141
    @137
    wa
    @126
    @128
    @121
    @141
    @137
    @126
    @128
    @121
    wi
    #
    @137
    @126
    wa
    @59
    @124
    wss
    #
    vk
    cr
    wrex
    #
    @141
    @142
    @126
    @137
    cpnf
    @124
    wcel
    @144
    @125
    @124
    cpnf
    @124
    cA
    inss1
    sseli
    vk
    @124
    pnfnei
    sylan2
    @141
    @128
    @144
    @121
    @141
    @128
    @83
    vx
    @125
    wral
    #
    @144
    @121
    wi
    #
    @128
    @8
    @36
    wcel
    #
    vz
    vx
    @125
    cR
    cmpt
    #
    crn
    #
    wral
    #
    @141
    @145
    @128
    @149
    @36
    wss
    @150
    @127
    @149
    @36
    @127
    @1
    @125
    cres
    #
    crn
    @149
    @1
    @125
    df-ima
    @151
    @148
    @125
    cA
    wss
    #
    @151
    @148
    wceq
    @124
    cA
    inss2
    #
    vx
    cA
    @125
    cR
    resmpt
    ax-mp
    rneqi
    eqtri
    sseq1i
    vz
    @149
    @36
    dfss3
    bitri
    @141
    @150
    @145
    @141
    @27
    vx
    @125
    wral
    #
    @150
    @145
    wb
    @152
    @141
    @28
    @154
    @153
    wph
    @28
    @41
    @29
    adantr
    @27
    vx
    @125
    cA
    ssralv
    mpsyl
    @147
    @83
    vx
    vz
    @125
    cR
    @148
    cc
    @148
    eqid
    @8
    cR
    @36
    eleq1
    ralrnmpt
    syl
    biimpd
    syl5bi
    @141
    @145
    @146
    @141
    @145
    wa
    #
    @143
    @120
    vk
    cr
    @155
    @56
    @143
    @120
    @141
    @56
    @143
    wa
    #
    @145
    @120
    @141
    @156
    wa
    #
    @145
    @120
    @157
    @83
    @119
    vx
    @125
    cB
    @157
    @30
    @125
    wcel
    #
    @83
    wi
    #
    @91
    @93
    @47
    @157
    @159
    @91
    @93
    wa
    #
    @83
    wi
    @160
    @47
    wi
    @157
    @160
    @158
    @83
    @157
    @160
    @158
    @157
    @160
    wa
    #
    @124
    cA
    @30
    @161
    @59
    @124
    @30
    @141
    @56
    @143
    @160
    simplrr
    @161
    @81
    @94
    @93
    @95
    @161
    cB
    cxr
    @30
    wph
    cB
    cxr
    wss
    @41
    @156
    @160
    @70
    ad3antrrr
    @157
    @91
    @93
    simprl
    sseldd
    #
    @157
    @91
    @93
    simprr
    @161
    @94
    @95
    @162
    @30
    pnfge
    syl
    @161
    @74
    @71
    @97
    @161
    @44
    @141
    @56
    @143
    @160
    simplrl
    rexrd
    pnfxr
    @99
    sylancl
    mpbir3and
    sseldd
    @157
    @91
    @30
    cA
    wcel
    @93
    @157
    cB
    cA
    @30
    wph
    @52
    @41
    @156
    @53
    ad2antrr
    sselda
    adantrr
    elind
    ex
    imim1d
    @157
    @160
    @83
    @47
    @161
    @83
    @101
    @47
    @161
    @39
    @102
    @23
    @27
    @103
    @39
    @161
    cnxmet
    a1i
    @141
    @102
    @156
    @160
    @41
    @102
    wph
    @104
    adantl
    ad2antrr
    wph
    @23
    @41
    @156
    @160
    @32
    ad3antrrr
    #
    @157
    @91
    @27
    @93
    @157
    @27
    vx
    cB
    wph
    @51
    @41
    @156
    @54
    ad2antrr
    r19.21bi
    adantrr
    #
    @107
    syl22anc
    @161
    @100
    @46
    @34
    clt
    @161
    @27
    @23
    @108
    @164
    @163
    @109
    syl2anc
    breq1d
    bitrd
    pm5.74da
    sylibd
    exp4a
    ralimdv2
    imp
    an32s
    expr
    reximdva
    ex
    syld
    com23
    syl5
    impl
    expimpd
    rexlimdva
    adantlr
    mpd
    ralrimiva
    wph
    @0
    @122
    wb
    @2
    wph
    vr
    vk
    vx
    cB
    cR
    cC
    @54
    xrlimcnp.b
    @32
    rlim2lt
    adantr
    mpbird
    impbida
end
