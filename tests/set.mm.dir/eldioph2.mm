include "cn0.mm"
include "wcel.mm"
include "cvv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "cmzp.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "cz.mm"
include "cmap.mm"
include "cres.mm"
include "cmpt.mm"
include "wceq.mm"
include "wrex.mm"
include "cfn.mm"
include "cc0.mm"
include "cab.mm"
include "cdioph.mm"
include "mzpcompact2.mm"
include "3ad2ant3.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "ad2antll.mm"
include "wi.mm"
include "cun.mm"
include "wf1o.mm"
include "cid.mm"
include "cuz.mm"
include "simplll.mm"
include "simplrl.mm"
include "fzfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "ssun2.mm"
include "a1i.mm"
include "eldioph2lem1.mm"
include "syl3anc.mm"
include "ccnv.mm"
include "ccom.mm"
include "f1ococnv2.mm"
include "ad2antrl.mm"
include "reseq1d.mm"
include "ssun1.mm"
include "resabs1.mm"
include "ax-mp.mm"
include "syl6req.mm"
include "resco.mm"
include "syl6eq.mm"
include "adantr.mm"
include "coeq2d.mm"
include "coires1.mm"
include "coass.mm"
include "eqcomi.mm"
include "3eqtr3g.mm"
include "fveq2d.mm"
include "wf.mm"
include "ovexd.mm"
include "simpr.mm"
include "wf1.mm"
include "f1of1.mm"
include "simprr.mm"
include "ad2antrr.mm"
include "unssd.mm"
include "f1ss.mm"
include "syl2anc.mm"
include "f1f.mm"
include "syl.mm"
include "mapco2g.mm"
include "coeq1.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqtr4d.mm"
include "mpteq2dva.mm"
include "fveq1d.mm"
include "ad3antrrr.mm"
include "diophrw.mm"
include "eqtrd.mm"
include "simp-5l.mm"
include "simplrr.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "fssres.mm"
include "mzprename.mm"
include "eldioph.mm"
include "eqeltrd.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "exp31.mm"
include "3adant3.mm"
include "imp31.mm"
include "adantrr.mm"

theorem eldioph2
  let vu: setvar u
  let vt: setvar t
  let cP: class P
  let cS: class S
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vd: setvar d

  disjoint P t
  disjoint P u
  disjoint t u
  disjoint S t
  disjoint S u
  disjoint N t
  disjoint N u
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P e
  disjoint P g
  disjoint P h
  disjoint a b
  disjoint a c
  disjoint a e
  disjoint a t
  disjoint a u
  disjoint a g
  disjoint a h
  disjoint b c
  disjoint b e
  disjoint b t
  disjoint b u
  disjoint b g
  disjoint b h
  disjoint c e
  disjoint c t
  disjoint c u
  disjoint c g
  disjoint c h
  disjoint e t
  disjoint e u
  disjoint e g
  disjoint e h
  disjoint g t
  disjoint h t
  disjoint g u
  disjoint h u
  disjoint g h
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint S g
  disjoint S h
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint d e
  disjoint d t
  disjoint d u
  disjoint d g
  disjoint d h
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N d
  disjoint N e
  disjoint N g
  disjoint N h
  assert |- ( ( N e. NN0 /\ ( S e. _V /\ ( 1 ... N ) C_ S ) /\ P e. ( mzPoly ` S ) ) -> { t | E. u e. ( NN0 ^m S ) ( t = ( u |` ( 1 ... N ) ) /\ ( P ` u ) = 0 ) } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    cS
    cvv
    wcel
    #
    c1
    cN
    cfz
    co
    #
    cS
    wss
    #
    wa
    #
    cP
    cS
    cmzp
    cfv
    wcel
    #
    w3a
    #
    va
    cv
    #
    cS
    wss
    #
    cP
    ve
    cz
    cS
    cmap
    co
    #
    ve
    cv
    #
    @7
    cres
    #
    vb
    cv
    #
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vb
    @7
    cmzp
    cfv
    #
    wrex
    va
    cfn
    wrex
    #
    vt
    cv
    #
    vu
    cv
    #
    @2
    cres
    wceq
    #
    @20
    cP
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vu
    cn0
    cS
    cmap
    co
    #
    wrex
    #
    vt
    cab
    #
    cN
    cdioph
    cfv
    #
    wcel
    #
    @5
    @0
    @18
    @4
    cP
    cS
    va
    vb
    ve
    mzpcompact2
    3ad2ant3
    @6
    @16
    @29
    va
    vb
    cfn
    @17
    @6
    @7
    cfn
    wcel
    #
    @12
    @17
    wcel
    #
    wa
    #
    wa
    #
    @16
    @29
    @33
    @16
    wa
    @27
    @21
    @20
    @14
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vu
    @25
    wrex
    #
    vt
    cab
    #
    @28
    @15
    @27
    @38
    wceq
    @33
    @8
    @15
    @26
    @37
    vt
    @15
    @24
    @36
    vu
    @25
    @15
    @23
    @35
    @21
    @15
    @22
    @34
    cc0
    @20
    cP
    @14
    fveq1
    eqeq1d
    anbi2d
    rexbidv
    abbidv
    ad2antll
    @33
    @8
    @38
    @28
    wcel
    #
    @15
    @6
    @32
    @8
    @39
    @0
    @4
    @32
    @8
    @39
    wi
    wi
    @5
    @0
    @4
    wa
    #
    @32
    @8
    @39
    @40
    @32
    wa
    #
    @8
    wa
    #
    c1
    vc
    cv
    #
    cfz
    co
    #
    @7
    @2
    cun
    #
    vd
    cv
    #
    wf1o
    #
    @46
    @2
    cres
    cid
    @2
    cres
    wceq
    #
    wa
    #
    vd
    cvv
    wrex
    vc
    cN
    cuz
    cfv
    #
    wrex
    #
    @39
    @42
    @0
    @45
    cfn
    wcel
    #
    @2
    @45
    wss
    #
    @51
    @0
    @4
    @32
    @8
    simplll
    @42
    @30
    @2
    cfn
    wcel
    @52
    @40
    @30
    @31
    @8
    simplrl
    c1
    cN
    fzfi
    @7
    @2
    unfi
    sylancl
    @53
    @42
    @2
    @7
    ssun2
    a1i
    @45
    vd
    cN
    vc
    eldioph2lem1
    syl3anc
    @42
    @49
    @39
    vc
    vd
    @50
    cvv
    @42
    @43
    @50
    wcel
    #
    @46
    cvv
    wcel
    #
    wa
    #
    wa
    #
    @49
    @39
    @57
    @49
    wa
    #
    @38
    @19
    vg
    cv
    #
    @2
    cres
    wceq
    @59
    vh
    cz
    @44
    cmap
    co
    #
    vh
    cv
    #
    @46
    ccnv
    #
    @7
    cres
    #
    ccom
    #
    @12
    cfv
    #
    cmpt
    #
    cfv
    cc0
    wceq
    wa
    vg
    cn0
    @44
    cmap
    co
    wrex
    vt
    cab
    #
    @28
    @58
    @38
    @21
    @20
    ve
    @9
    @10
    @46
    ccom
    #
    @66
    cfv
    #
    cmpt
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vu
    @25
    wrex
    #
    vt
    cab
    #
    @67
    @58
    @37
    @74
    vt
    @58
    @36
    @73
    vu
    @25
    @58
    @35
    @72
    @21
    @58
    @34
    @71
    cc0
    @58
    @20
    @14
    @70
    @58
    ve
    @9
    @13
    @69
    @58
    @10
    @9
    wcel
    #
    wa
    #
    @13
    @68
    @63
    ccom
    #
    @12
    cfv
    #
    @69
    @77
    @11
    @78
    @12
    @77
    @10
    cid
    @7
    cres
    #
    ccom
    @10
    @46
    @63
    ccom
    #
    ccom
    #
    @11
    @78
    @77
    @80
    @81
    @10
    @58
    @80
    @81
    wceq
    @76
    @58
    @80
    @46
    @62
    ccom
    #
    @7
    cres
    #
    @81
    @58
    @84
    cid
    @45
    cres
    #
    @7
    cres
    #
    @80
    @58
    @83
    @85
    @7
    @47
    @83
    @85
    wceq
    @57
    @48
    @44
    @45
    @46
    f1ococnv2
    ad2antrl
    reseq1d
    @7
    @45
    wss
    #
    @86
    @80
    wceq
    @7
    @2
    ssun1
    #
    cid
    @7
    @45
    resabs1
    ax-mp
    syl6req
    @46
    @62
    @7
    resco
    syl6eq
    adantr
    coeq2d
    @10
    @7
    coires1
    @78
    @82
    @10
    @46
    @63
    coass
    eqcomi
    3eqtr3g
    fveq2d
    @77
    @68
    @60
    wcel
    #
    @69
    @79
    wceq
    @77
    @44
    cvv
    wcel
    #
    @76
    @44
    cS
    @46
    wf
    #
    @89
    @77
    c1
    @43
    cfz
    ovexd
    @58
    @76
    simpr
    @58
    @91
    @76
    @58
    @44
    cS
    @46
    wf1
    #
    @91
    @58
    @44
    @45
    @46
    wf1
    #
    @45
    cS
    wss
    #
    @92
    @47
    @93
    @57
    @48
    @44
    @45
    @46
    f1of1
    ad2antrl
    @42
    @94
    @56
    @49
    @42
    @7
    @2
    cS
    @41
    @8
    simpr
    @40
    @3
    @32
    @8
    @0
    @1
    @3
    simprr
    ad2antrr
    unssd
    ad2antrr
    @44
    @45
    cS
    @46
    f1ss
    syl2anc
    #
    @44
    cS
    @46
    f1f
    syl
    adantr
    @10
    cz
    cS
    @46
    @44
    mapco2g
    syl3anc
    vh
    @68
    @65
    @79
    @60
    @66
    @61
    @68
    wceq
    @64
    @78
    @12
    @61
    @68
    @63
    coeq1
    fveq2d
    @66
    eqid
    @78
    @12
    fvex
    fvmpt
    syl
    eqtr4d
    mpteq2dva
    fveq1d
    eqeq1d
    anbi2d
    rexbidv
    abbidv
    @58
    @1
    @92
    @48
    @75
    @67
    wceq
    @41
    @1
    @8
    @56
    @49
    @0
    @1
    @3
    @32
    simplrl
    ad3antrrr
    @95
    @57
    @47
    @48
    simprr
    @66
    cS
    @44
    @46
    @2
    vt
    vu
    vg
    ve
    diophrw
    syl3anc
    eqtrd
    @58
    @0
    @54
    @66
    @44
    cmzp
    cfv
    wcel
    #
    @67
    @28
    wcel
    @0
    @4
    @32
    @8
    @56
    @49
    simp-5l
    @42
    @54
    @55
    @49
    simplrl
    @58
    @90
    @31
    @7
    @44
    @63
    wf
    #
    @96
    @58
    c1
    @43
    cfz
    ovexd
    @42
    @31
    @56
    @49
    @40
    @30
    @31
    @8
    simplrr
    ad2antrr
    @47
    @97
    @57
    @48
    @47
    @45
    @44
    @62
    wf
    #
    @87
    @97
    @47
    @45
    @44
    @62
    wf1o
    @98
    @44
    @45
    @46
    f1ocnv
    @45
    @44
    @62
    f1of
    syl
    @88
    @45
    @44
    @7
    @62
    fssres
    sylancl
    ad2antrl
    vh
    @63
    @12
    @7
    @44
    mzprename
    syl3anc
    vg
    vt
    @66
    @43
    cN
    eldioph
    syl3anc
    eqeltrd
    ex
    rexlimdvva
    mpd
    exp31
    3adant3
    imp31
    adantrr
    eqeltrd
    ex
    rexlimdvva
    mpd
end
