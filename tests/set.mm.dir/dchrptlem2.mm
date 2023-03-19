include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "c1.mm"
include "wne.mm"
include "wrex.mm"
include "cmulr.mm"
include "co.mm"
include "cur.mm"
include "fveq2.mm"
include "wa.mm"
include "wceq.mm"
include "cc.mm"
include "cz.mm"
include "crn.mm"
include "cdprd.mm"
include "wf.mm"
include "cdm.mm"
include "zex.mm"
include "mptex.mm"
include "rnex.mm"
include "dmmpti.mm"
include "a1i.mm"
include "dpjf.mm"
include "feq2d.mm"
include "mpbid.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "fvmpt3i.mm"
include "syl.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "sylib.mm"
include "cexp.mm"
include "dchrptlem1.mm"
include "cneg.mm"
include "c2.mm"
include "cdiv.mm"
include "ccxp.mm"
include "neg1cn.mm"
include "cr.mm"
include "cn.mm"
include "2re.mm"
include "cgrp.mm"
include "cfn.mm"
include "crg.mm"
include "cn0.mm"
include "ccrg.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "3syl.mm"
include "unitgrp.mm"
include "wss.mm"
include "znfi.mm"
include "unitss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "chash.mm"
include "cfzo.mm"
include "cword.mm"
include "wrdf.mm"
include "fdm.mm"
include "ffvelrnd.mm"
include "unitgrpbas.mm"
include "odcl2.mm"
include "syl3anc.mm"
include "nndivre.mm"
include "sylancr.mm"
include "recnd.mm"
include "cxpcl.mm"
include "syl5eqel.mm"
include "ad2antrr.mm"
include "neg1ne0.mm"
include "cxpne0d.mm"
include "neeq1i.mm"
include "sylibr.mm"
include "simprl.mm"
include "expclzd.mm"
include "eqeltrd.mm"
include "rexlimddv.mm"
include "cmul.mm"
include "wral.mm"
include "ralrimiva.mm"
include "weq.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "simprr.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "reeanv.mm"
include "caddc.mm"
include "simprll.mm"
include "simprlr.mm"
include "expaddz.mm"
include "syl22anc.mm"
include "simpll.mm"
include "unitmulcl.mm"
include "zaddcld.mm"
include "simprrl.mm"
include "simprrr.mm"
include "oveq12d.mm"
include "cghm.mm"
include "cress.mm"
include "dpjghm.mm"
include "cvv.mm"
include "cmgp.mm"
include "eqeltri.mm"
include "ressid.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "cplusg.mm"
include "cui.mm"
include "fvex.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ghmlin.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "3eqtr4d.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "id.mm"
include "1unit.mm"
include "0zd.mm"
include "c0g.mm"
include "ghmid.mm"
include "unitgrpid.mm"
include "fveq2d.mm"
include "mulg0.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "dchrelbasd.mm"
include "sseldi.mm"
include "eleq1.mm"
include "ifbieq1d.mm"
include "c0ex.mm"
include "ifex.mm"
include "iftrued.mm"
include "wi.mm"
include "oveq1i.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "oddvds.mm"
include "root1eq1.mm"
include "syl2anc.mm"
include "eqeq12d.mm"
include "3bitr4d.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "eqnetrd.mm"
include "rexlimdvaa.mm"
include "mpdan.mm"
include "mpd.mm"
include "fveq1.mm"
include "neeq1d.mm"
include "rspcev.mm"

theorem dchrptlem2
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let cC: class C
  let vi: setvar i
  let cM: class M
  assume dchrpt.g: |- G = ( DChr ` N )
  assume dchrpt.z: |- Z = ( Z/nZ ` N )
  assume dchrpt.d: |- D = ( Base ` G )
  assume dchrpt.b: |- B = ( Base ` Z )
  assume dchrpt.1: |- .1. = ( 1r ` Z )
  assume dchrpt.n: |- ( ph -> N e. NN )
  assume dchrpt.n1: |- ( ph -> A =/= .1. )
  assume dchrpt.u: |- U = ( Unit ` Z )
  assume dchrpt.h: |- H = ( ( mulGrp ` Z ) |`s U )
  assume dchrpt.m: |- .x. = ( .g ` H )
  assume dchrpt.s: |- S = ( k e. dom W |-> ran ( n e. ZZ |-> ( n .x. ( W ` k ) ) ) )
  assume dchrpt.au: |- ( ph -> A e. U )
  assume dchrpt.w: |- ( ph -> W e. Word U )
  assume dchrpt.2: |- ( ph -> H dom DProd S )
  assume dchrpt.3: |- ( ph -> ( H DProd S ) = U )
  assume dchrpt.p: |- P = ( H dProj S )
  assume dchrpt.o: |- O = ( od ` H )
  assume dchrpt.t: |- T = ( -u 1 ^c ( 2 / ( O ` ( W ` I ) ) ) )
  assume dchrpt.i: |- ( ph -> I e. dom W )
  assume dchrpt.4: |- ( ph -> ( ( P ` I ) ` A ) =/= .1. )
  assume dchrpt.5: |- X = ( u e. U |-> ( iota h E. m e. ZZ ( ( ( P ` I ) ` u ) = ( m .x. ( W ` I ) ) /\ h = ( T ^ m ) ) ) )

  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h x
  disjoint .1. h
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint .1. k
  disjoint m n
  disjoint m x
  disjoint .1. m
  disjoint n x
  disjoint .1. n
  disjoint .1. x
  disjoint h u
  disjoint A h
  disjoint k u
  disjoint A k
  disjoint m u
  disjoint A m
  disjoint n u
  disjoint A n
  disjoint u x
  disjoint A u
  disjoint A x
  disjoint I h
  disjoint I k
  disjoint I m
  disjoint I u
  disjoint B x
  disjoint G x
  disjoint H h
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H u
  disjoint H x
  disjoint N x
  disjoint W h
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W u
  disjoint W x
  disjoint .x. h
  disjoint .x. k
  disjoint .x. m
  disjoint .x. n
  disjoint .x. u
  disjoint .x. x
  disjoint X x
  disjoint P h
  disjoint P m
  disjoint P u
  disjoint S h
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S x
  disjoint Z h
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z u
  disjoint Z x
  disjoint D x
  disjoint h ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint T h
  disjoint T m
  disjoint T u
  disjoint U h
  disjoint U m
  disjoint U u
  disjoint U x
  disjoint a b
  disjoint a h
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint .1. a
  disjoint b h
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint .1. b
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint A a
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint A b
  disjoint h v
  disjoint h w
  disjoint k v
  disjoint k w
  disjoint m v
  disjoint m w
  disjoint n v
  disjoint n w
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint w x
  disjoint A w
  disjoint I a
  disjoint I b
  disjoint I v
  disjoint v y
  disjoint B v
  disjoint x y
  disjoint B y
  disjoint C h
  disjoint C m
  disjoint C u
  disjoint a i
  disjoint H a
  disjoint h i
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i x
  disjoint H i
  disjoint W a
  disjoint b i
  disjoint W b
  disjoint i v
  disjoint W i
  disjoint W v
  disjoint .x. a
  disjoint .x. b
  disjoint .x. v
  disjoint a y
  disjoint X a
  disjoint b y
  disjoint X b
  disjoint X v
  disjoint X y
  disjoint P a
  disjoint P b
  disjoint P v
  disjoint S a
  disjoint S i
  disjoint Z a
  disjoint Z b
  disjoint h y
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint u y
  disjoint Z v
  disjoint w y
  disjoint Z w
  disjoint Z y
  disjoint D a
  disjoint D w
  disjoint M h
  disjoint M m
  disjoint a ph
  disjoint b ph
  disjoint i w
  disjoint i y
  disjoint i ph
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint U a
  disjoint U b
  disjoint U v
  disjoint U y
  assert |- ( ph -> E. x e. D ( x ` A ) =/= 1 )

  proof
    wph
    vv
    cB
    vv
    cv
    #
    cU
    wcel
    #
    @0
    cX
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    cD
    wcel
    cA
    @4
    cfv
    #
    c1
    wne
    #
    cA
    vx
    cv
    #
    cfv
    #
    c1
    wne
    #
    vx
    cD
    wrex
    wph
    vx
    vy
    @7
    cX
    cfv
    #
    cB
    vy
    cv
    #
    cX
    cfv
    #
    cD
    cU
    vv
    @7
    @11
    cZ
    cmulr
    cfv
    #
    co
    #
    cX
    cfv
    #
    cG
    cN
    @2
    cZ
    cur
    cfv
    #
    cX
    cfv
    #
    cZ
    dchrpt.g
    dchrpt.z
    dchrpt.b
    dchrpt.u
    dchrpt.n
    dchrpt.d
    @0
    @7
    cX
    fveq2
    @0
    @11
    cX
    fveq2
    @0
    @14
    cX
    fveq2
    @0
    @16
    cX
    fveq2
    wph
    @1
    wa
    #
    @0
    cI
    cP
    cfv
    #
    cfv
    #
    va
    cv
    #
    cI
    cW
    cfv
    #
    c.x
    co
    #
    wceq
    #
    @2
    cc
    wcel
    va
    cz
    @18
    @20
    va
    cz
    @23
    cmpt
    #
    crn
    #
    wcel
    @24
    va
    cz
    wrex
    #
    @18
    @20
    cI
    cS
    cfv
    #
    @26
    wph
    cU
    @28
    @0
    @19
    wph
    cH
    cS
    cdprd
    co
    #
    @28
    @19
    wf
    cU
    @28
    @19
    wf
    wph
    cP
    cS
    cH
    cW
    cdm
    #
    cI
    dchrpt.2
    cS
    cdm
    @30
    wceq
    wph
    vk
    @30
    vn
    cz
    vn
    cv
    #
    vk
    cv
    #
    cW
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    crn
    #
    cS
    @35
    vn
    cz
    @34
    zex
    mptex
    rnex
    #
    dchrpt.s
    dmmpti
    a1i
    #
    dchrpt.p
    dchrpt.i
    dpjf
    wph
    @29
    cU
    @28
    @19
    dchrpt.3
    feq2d
    mpbid
    ffvelrnda
    @18
    cI
    @30
    wcel
    #
    @28
    @26
    wceq
    wph
    @39
    @1
    dchrpt.i
    adantr
    vk
    cI
    @36
    @26
    @30
    cS
    @32
    cI
    wceq
    #
    @35
    @25
    @40
    @35
    va
    cz
    @21
    @33
    c.x
    co
    #
    cmpt
    @25
    vn
    va
    cz
    @34
    @41
    @31
    @21
    @33
    c.x
    oveq1
    cbvmptv
    @40
    va
    cz
    @41
    @23
    @40
    @33
    @22
    @21
    c.x
    @32
    cI
    cW
    fveq2
    oveq2d
    mpteq2dv
    syl5eq
    rneqd
    dchrpt.s
    @37
    fvmpt3i
    syl
    eleqtrd
    va
    cz
    @23
    @20
    @25
    @25
    eqid
    @21
    @22
    c.x
    ovex
    elrnmpti
    sylib
    #
    @18
    @21
    cz
    wcel
    #
    @24
    wa
    #
    wa
    #
    @2
    cT
    @21
    cexp
    co
    #
    cc
    wph
    vu
    cA
    cB
    @0
    cD
    cP
    cS
    cT
    c.x
    cU
    c.1
    vh
    vk
    vm
    vn
    cG
    cH
    cI
    @21
    cN
    cO
    cW
    cX
    cZ
    dchrpt.g
    dchrpt.z
    dchrpt.d
    dchrpt.b
    dchrpt.1
    dchrpt.n
    dchrpt.n1
    dchrpt.u
    dchrpt.h
    dchrpt.m
    dchrpt.s
    dchrpt.au
    dchrpt.w
    dchrpt.2
    dchrpt.3
    dchrpt.p
    dchrpt.o
    dchrpt.t
    dchrpt.i
    dchrpt.4
    dchrpt.5
    dchrptlem1
    @45
    cT
    @21
    wph
    cT
    cc
    wcel
    #
    @1
    @44
    wph
    cT
    c1
    cneg
    #
    c2
    @22
    cO
    cfv
    #
    cdiv
    co
    #
    ccxp
    co
    #
    cc
    dchrpt.t
    wph
    @48
    cc
    wcel
    #
    @50
    cc
    wcel
    @51
    cc
    wcel
    neg1cn
    wph
    @50
    wph
    c2
    cr
    wcel
    @49
    cn
    wcel
    #
    @50
    cr
    wcel
    2re
    wph
    cH
    cgrp
    wcel
    #
    cU
    cfn
    wcel
    #
    @22
    cU
    wcel
    #
    @53
    wph
    cZ
    crg
    wcel
    #
    @54
    wph
    cN
    cn0
    wcel
    cZ
    ccrg
    wcel
    @57
    wph
    cN
    dchrpt.n
    nnnn0d
    cN
    cZ
    dchrpt.z
    zncrng
    cZ
    crngring
    3syl
    #
    cZ
    cU
    cH
    dchrpt.u
    dchrpt.h
    unitgrp
    syl
    #
    wph
    cB
    cfn
    wcel
    #
    cU
    cB
    wss
    @55
    wph
    cN
    cn
    wcel
    @60
    dchrpt.n
    cB
    cN
    cZ
    dchrpt.z
    dchrpt.b
    znfi
    syl
    cB
    cZ
    cU
    dchrpt.b
    dchrpt.u
    unitss
    #
    cB
    cU
    ssfi
    sylancl
    wph
    cc0
    cW
    chash
    cfv
    cfzo
    co
    #
    cU
    cI
    cW
    wph
    cW
    cU
    cword
    wcel
    @62
    cU
    cW
    wf
    #
    dchrpt.w
    cU
    cW
    wrdf
    syl
    #
    wph
    cI
    @30
    @62
    dchrpt.i
    wph
    @63
    @30
    @62
    wceq
    @64
    @62
    cU
    cW
    fdm
    syl
    eleqtrd
    ffvelrnd
    #
    @22
    cH
    cO
    cU
    cZ
    cU
    cH
    dchrpt.u
    dchrpt.h
    unitgrpbas
    #
    dchrpt.o
    odcl2
    syl3anc
    #
    c2
    @49
    nndivre
    sylancr
    recnd
    #
    @48
    @50
    cxpcl
    sylancr
    syl5eqel
    #
    ad2antrr
    wph
    cT
    cc0
    wne
    #
    @1
    @44
    wph
    @51
    cc0
    wne
    @70
    wph
    @48
    @50
    @52
    wph
    neg1cn
    a1i
    @48
    cc0
    wne
    wph
    neg1ne0
    a1i
    @68
    cxpne0d
    cT
    @51
    cc0
    dchrpt.t
    neeq1i
    sylibr
    #
    ad2antrr
    @18
    @43
    @24
    simprl
    expclzd
    eqeltrd
    rexlimddv
    wph
    @7
    cU
    wcel
    #
    @11
    cU
    wcel
    #
    wa
    #
    wa
    #
    @7
    @19
    cfv
    #
    @23
    wceq
    #
    va
    cz
    wrex
    #
    @11
    @19
    cfv
    #
    vb
    cv
    #
    @22
    c.x
    co
    #
    wceq
    #
    vb
    cz
    wrex
    #
    @15
    @10
    @12
    cmul
    co
    #
    wceq
    #
    @75
    @72
    @27
    vv
    cU
    wral
    #
    @78
    wph
    @72
    @73
    simprl
    #
    wph
    @86
    @74
    wph
    @27
    vv
    cU
    @42
    ralrimiva
    #
    adantr
    #
    @27
    @78
    vv
    @7
    cU
    vv
    vx
    weq
    #
    @24
    @77
    va
    cz
    @90
    @20
    @76
    @23
    @0
    @7
    @19
    fveq2
    eqeq1d
    rexbidv
    rspcv
    sylc
    @75
    @73
    @86
    @83
    wph
    @72
    @73
    simprr
    #
    @89
    @27
    @83
    vv
    @11
    cU
    vv
    vy
    weq
    #
    @27
    @79
    @23
    wceq
    #
    va
    cz
    wrex
    @83
    @92
    @24
    @93
    va
    cz
    @92
    @20
    @79
    @23
    @0
    @11
    @19
    fveq2
    eqeq1d
    rexbidv
    @93
    @82
    va
    vb
    cz
    va
    vb
    weq
    @23
    @81
    @79
    @21
    @80
    @22
    c.x
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    rspcv
    sylc
    @78
    @83
    wa
    @77
    @82
    wa
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    @75
    @85
    @77
    @82
    va
    vb
    cz
    cz
    reeanv
    @75
    @94
    @85
    va
    vb
    cz
    cz
    @75
    @43
    @80
    cz
    wcel
    #
    wa
    #
    @94
    @85
    @75
    @96
    @94
    wa
    #
    wa
    #
    cT
    @21
    @80
    caddc
    co
    #
    cexp
    co
    #
    @46
    cT
    @80
    cexp
    co
    #
    cmul
    co
    #
    @15
    @84
    @98
    @47
    @70
    @43
    @95
    @100
    @102
    wceq
    wph
    @47
    @74
    @97
    @69
    ad2antrr
    wph
    @70
    @74
    @97
    @71
    ad2antrr
    @75
    @43
    @95
    @94
    simprll
    #
    @75
    @43
    @95
    @94
    simprlr
    #
    cT
    @21
    @80
    expaddz
    syl22anc
    @98
    wph
    @14
    cU
    wcel
    #
    @99
    cz
    wcel
    @14
    @19
    cfv
    #
    @99
    @22
    c.x
    co
    #
    wceq
    @15
    @100
    wceq
    wph
    @74
    @97
    simpll
    #
    @98
    @57
    @72
    @73
    @105
    wph
    @57
    @74
    @97
    @58
    ad2antrr
    @75
    @72
    @97
    @87
    adantr
    #
    @75
    @73
    @97
    @91
    adantr
    #
    cZ
    @13
    cU
    @7
    @11
    dchrpt.u
    @13
    eqid
    #
    unitmulcl
    syl3anc
    @98
    @21
    @80
    @103
    @104
    zaddcld
    @98
    @76
    @79
    @13
    co
    #
    @23
    @81
    @13
    co
    #
    @106
    @107
    @98
    @76
    @23
    @79
    @81
    @13
    @75
    @96
    @77
    @82
    simprrl
    #
    @75
    @96
    @77
    @82
    simprrr
    #
    oveq12d
    @98
    @19
    cH
    cH
    cghm
    co
    #
    wcel
    #
    @72
    @73
    @106
    @112
    wceq
    wph
    @117
    @74
    @97
    wph
    @19
    cH
    @29
    cress
    co
    #
    cH
    cghm
    co
    @116
    wph
    cP
    cS
    cH
    @30
    cI
    dchrpt.2
    @38
    dchrpt.p
    dchrpt.i
    dpjghm
    wph
    @118
    cH
    cH
    cghm
    wph
    @118
    cH
    cU
    cress
    co
    #
    cH
    wph
    @29
    cU
    cH
    cress
    dchrpt.3
    oveq2d
    cH
    cvv
    wcel
    @119
    cH
    wceq
    cH
    cZ
    cmgp
    cfv
    #
    cU
    cress
    co
    cvv
    dchrpt.h
    @120
    cU
    cress
    ovex
    eqeltri
    cU
    cH
    cvv
    @66
    ressid
    ax-mp
    syl6eq
    oveq1d
    eleqtrd
    #
    ad2antrr
    @109
    @110
    @13
    @13
    cH
    cH
    @7
    @19
    @11
    cU
    @66
    cU
    cvv
    wcel
    @13
    cH
    cplusg
    cfv
    wceq
    cU
    cZ
    cui
    cfv
    cvv
    dchrpt.u
    cZ
    cui
    fvex
    eqeltri
    cU
    @13
    @120
    cH
    cvv
    dchrpt.h
    cZ
    @13
    @120
    @120
    eqid
    @111
    mgpplusg
    ressplusg
    ax-mp
    #
    @122
    ghmlin
    syl3anc
    @98
    @54
    @43
    @95
    @56
    @107
    @113
    wceq
    wph
    @54
    @74
    @97
    @59
    ad2antrr
    @103
    @104
    wph
    @56
    @74
    @97
    @65
    ad2antrr
    cU
    @13
    c.x
    cH
    @21
    @80
    @22
    @66
    dchrpt.m
    @122
    mulgdir
    syl13anc
    3eqtr4d
    wph
    vu
    cA
    cB
    @14
    cD
    cP
    cS
    cT
    c.x
    cU
    c.1
    vh
    vk
    vm
    vn
    cG
    cH
    cI
    @99
    cN
    cO
    cW
    cX
    cZ
    dchrpt.g
    dchrpt.z
    dchrpt.d
    dchrpt.b
    dchrpt.1
    dchrpt.n
    dchrpt.n1
    dchrpt.u
    dchrpt.h
    dchrpt.m
    dchrpt.s
    dchrpt.au
    dchrpt.w
    dchrpt.2
    dchrpt.3
    dchrpt.p
    dchrpt.o
    dchrpt.t
    dchrpt.i
    dchrpt.4
    dchrpt.5
    dchrptlem1
    syl22anc
    @98
    @10
    @46
    @12
    @101
    cmul
    @98
    wph
    @72
    @43
    @77
    @10
    @46
    wceq
    @108
    @109
    @103
    @114
    wph
    vu
    cA
    cB
    @7
    cD
    cP
    cS
    cT
    c.x
    cU
    c.1
    vh
    vk
    vm
    vn
    cG
    cH
    cI
    @21
    cN
    cO
    cW
    cX
    cZ
    dchrpt.g
    dchrpt.z
    dchrpt.d
    dchrpt.b
    dchrpt.1
    dchrpt.n
    dchrpt.n1
    dchrpt.u
    dchrpt.h
    dchrpt.m
    dchrpt.s
    dchrpt.au
    dchrpt.w
    dchrpt.2
    dchrpt.3
    dchrpt.p
    dchrpt.o
    dchrpt.t
    dchrpt.i
    dchrpt.4
    dchrpt.5
    dchrptlem1
    syl22anc
    @98
    wph
    @73
    @95
    @82
    @12
    @101
    wceq
    @108
    @110
    @104
    @115
    wph
    vu
    cA
    cB
    @11
    cD
    cP
    cS
    cT
    c.x
    cU
    c.1
    vh
    vk
    vm
    vn
    cG
    cH
    cI
    @80
    cN
    cO
    cW
    cX
    cZ
    dchrpt.g
    dchrpt.z
    dchrpt.d
    dchrpt.b
    dchrpt.1
    dchrpt.n
    dchrpt.n1
    dchrpt.u
    dchrpt.h
    dchrpt.m
    dchrpt.s
    dchrpt.au
    dchrpt.w
    dchrpt.2
    dchrpt.3
    dchrpt.p
    dchrpt.o
    dchrpt.t
    dchrpt.i
    dchrpt.4
    dchrpt.5
    dchrptlem1
    syl22anc
    oveq12d
    3eqtr4d
    expr
    rexlimdvva
    syl5bir
    mp2and
    wph
    @17
    cT
    cc0
    cexp
    co
    #
    c1
    wph
    wph
    @16
    cU
    wcel
    #
    cc0
    cz
    wcel
    @16
    @19
    cfv
    #
    cc0
    @22
    c.x
    co
    #
    wceq
    @17
    @123
    wceq
    wph
    id
    wph
    @57
    @124
    @58
    cZ
    cU
    @16
    dchrpt.u
    @16
    eqid
    #
    1unit
    syl
    wph
    0zd
    wph
    cH
    c0g
    cfv
    #
    @19
    cfv
    #
    @128
    @125
    @126
    wph
    @117
    @129
    @128
    wceq
    @121
    cH
    cH
    @19
    @128
    @128
    @128
    eqid
    #
    @130
    ghmid
    syl
    wph
    @16
    @128
    @19
    wph
    @57
    @16
    @128
    wceq
    @58
    cZ
    cU
    @16
    cH
    dchrpt.u
    dchrpt.h
    @127
    unitgrpid
    syl
    #
    fveq2d
    wph
    @56
    @126
    @128
    wceq
    @65
    cU
    c.x
    cH
    @22
    @128
    @66
    @130
    dchrpt.m
    mulg0
    syl
    3eqtr4d
    wph
    vu
    cA
    cB
    @16
    cD
    cP
    cS
    cT
    c.x
    cU
    c.1
    vh
    vk
    vm
    vn
    cG
    cH
    cI
    cc0
    cN
    cO
    cW
    cX
    cZ
    dchrpt.g
    dchrpt.z
    dchrpt.d
    dchrpt.b
    dchrpt.1
    dchrpt.n
    dchrpt.n1
    dchrpt.u
    dchrpt.h
    dchrpt.m
    dchrpt.s
    dchrpt.au
    dchrpt.w
    dchrpt.2
    dchrpt.3
    dchrpt.p
    dchrpt.o
    dchrpt.t
    dchrpt.i
    dchrpt.4
    dchrpt.5
    dchrptlem1
    syl22anc
    wph
    cT
    @69
    exp0d
    eqtrd
    dchrelbasd
    wph
    @5
    cA
    cX
    cfv
    #
    c1
    wph
    @5
    cA
    cU
    wcel
    #
    @132
    cc0
    cif
    #
    @132
    wph
    cA
    cB
    wcel
    @5
    @134
    wceq
    wph
    cU
    cB
    cA
    @61
    dchrpt.au
    sseldi
    vv
    cA
    @3
    @134
    cB
    @4
    @0
    cA
    wceq
    #
    @1
    @133
    @2
    @132
    cc0
    @0
    cA
    cU
    eleq1
    @0
    cA
    cX
    fveq2
    ifbieq1d
    @4
    eqid
    @1
    @2
    cc0
    @0
    cX
    fvex
    c0ex
    ifex
    fvmpt3i
    syl
    wph
    @133
    @132
    cc0
    dchrpt.au
    iftrued
    eqtrd
    wph
    cA
    @19
    cfv
    #
    @23
    wceq
    #
    va
    cz
    wrex
    #
    @132
    c1
    wne
    #
    wph
    @133
    @86
    @138
    dchrpt.au
    @88
    @27
    @138
    vv
    cA
    cU
    @135
    @24
    @137
    va
    cz
    @135
    @20
    @136
    @23
    @0
    cA
    @19
    fveq2
    eqeq1d
    rexbidv
    rspcv
    sylc
    wph
    @133
    @138
    @139
    wi
    dchrpt.au
    wph
    @133
    wa
    #
    @137
    @139
    va
    cz
    @140
    @43
    @137
    wa
    #
    wa
    #
    @132
    @51
    @21
    cexp
    co
    #
    c1
    @142
    @132
    @46
    @143
    wph
    vu
    cA
    cB
    cA
    cD
    cP
    cS
    cT
    c.x
    cU
    c.1
    vh
    vk
    vm
    vn
    cG
    cH
    cI
    @21
    cN
    cO
    cW
    cX
    cZ
    dchrpt.g
    dchrpt.z
    dchrpt.d
    dchrpt.b
    dchrpt.1
    dchrpt.n
    dchrpt.n1
    dchrpt.u
    dchrpt.h
    dchrpt.m
    dchrpt.s
    dchrpt.au
    dchrpt.w
    dchrpt.2
    dchrpt.3
    dchrpt.p
    dchrpt.o
    dchrpt.t
    dchrpt.i
    dchrpt.4
    dchrpt.5
    dchrptlem1
    cT
    @51
    @21
    cexp
    dchrpt.t
    oveq1i
    syl6eq
    @142
    @143
    c1
    wne
    @136
    c.1
    wne
    #
    wph
    @144
    @133
    @141
    dchrpt.4
    ad2antrr
    @142
    @143
    c1
    @136
    c.1
    @142
    @49
    @21
    cdvds
    wbr
    #
    @23
    @128
    wceq
    #
    @143
    c1
    wceq
    #
    @136
    c.1
    wceq
    @142
    @54
    @56
    @43
    @145
    @146
    wb
    wph
    @54
    @133
    @141
    @59
    ad2antrr
    wph
    @56
    @133
    @141
    @65
    ad2antrr
    @140
    @43
    @137
    simprl
    #
    @22
    c.x
    cH
    @21
    cO
    cU
    @128
    @66
    dchrpt.o
    dchrpt.m
    @130
    oddvds
    syl3anc
    @142
    @53
    @43
    @147
    @145
    wb
    wph
    @53
    @133
    @141
    @67
    ad2antrr
    @148
    @21
    @49
    root1eq1
    syl2anc
    @142
    @136
    @23
    c.1
    @128
    @140
    @43
    @137
    simprr
    wph
    c.1
    @128
    wceq
    @133
    @141
    wph
    c.1
    @16
    @128
    dchrpt.1
    @131
    syl5eq
    ad2antrr
    eqeq12d
    3bitr4d
    necon3bid
    mpbird
    eqnetrd
    rexlimdvaa
    mpdan
    mpd
    eqnetrd
    @9
    @6
    vx
    @4
    cD
    @7
    @4
    wceq
    @8
    @5
    c1
    cA
    @7
    @4
    fveq1
    neeq1d
    rspcev
    syl2anc
end
