include "cv.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "csb.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "wcel.mm"
include "wa.mm"
include "gsumbagdiaglem.mm"
include "wf.mm"
include "wral.mm"
include "ccom.mm"
include "anassrs.mm"
include "eqid.mm"
include "fmptd.mm"
include "wf1o.mm"
include "adantr.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "simpr.mm"
include "psrbagconcl.mm"
include "syl3anc.mm"
include "sseldi.mm"
include "psrbagconf1o.mm"
include "syl2anc.mm"
include "f1of.mm"
include "syl.mm"
include "fco.mm"
include "cfv.mm"
include "cn0.mm"
include "wceq.mm"
include "psrbagf.mm"
include "ffvelrnda.mm"
include "cc.mm"
include "nn0cn.mm"
include "sub32.mm"
include "syl3an.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "ovexd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"
include "eqeltrrd.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "a1i.mm"
include "csbeq1.mm"
include "fmptco.mm"
include "feq1d.mm"
include "mpbid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "anasss.mm"
include "syldan.mm"
include "gsumbagdiag.mm"
include "cxp.mm"
include "cfn.mm"
include "c0g.mm"
include "psrbaglefi.mm"
include "syl5eqel.mm"
include "xpfi.mm"
include "wn.mm"
include "simprl.mm"
include "simpld.mm"
include "brxp.mm"
include "sylanbrc.mm"
include "pm2.24d.mm"
include "impr.mm"
include "gsum2d2.mm"
include "3eqtr3d.mm"
include "ccnv.mm"
include "ccmn.mm"
include "wfun.mm"
include "csupp.mm"
include "wss.mm"
include "cfsupp.mm"
include "cn.mm"
include "cima.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "rabexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "funmpt.mm"
include "fvexd.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmmptss.mm"
include "sstri.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "gsumcl.mm"
include "f1ocnv.mm"
include "cid.mm"
include "cres.mm"
include "coass.mm"
include "f1ococnv2.mm"
include "coeq2d.mm"
include "syl5eq.mm"
include "eqidd.mm"
include "breq2.mm"
include "rabbidv.mm"
include "csbie.mm"
include "oveq1.mm"
include "csbeq1d.mm"
include "syl5eqr.mm"
include "mpteq12dv.mm"
include "oveq2d.mm"
include "coeq1d.mm"
include "coires1.mm"
include "ssid.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "mp1i.mm"
include "gsumf1o.mm"
include "eqtrd.mm"

theorem psrass1lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  let vm: setvar m
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume psrbag.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrbagconf1o.1: |- S = { y e. D | y oR <_ F }
  assume gsumbagdiag.i: |- ( ph -> I e. V )
  assume gsumbagdiag.f: |- ( ph -> F e. D )
  assume gsumbagdiag.b: |- B = ( Base ` G )
  assume gsumbagdiag.g: |- ( ph -> G e. CMnd )
  assume gsumbagdiag.x: |- ( ( ph /\ ( j e. S /\ k e. { x e. D | x oR <_ ( F oF - j ) } ) ) -> X e. B )
  assume psrass1lem.y: |- ( k = ( n oF - j ) -> X = Y )

  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G f
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint V n
  disjoint V x
  disjoint V y
  disjoint I f
  disjoint I n
  disjoint I x
  disjoint I y
  disjoint j ph
  disjoint k ph
  disjoint S j
  disjoint S k
  disjoint S n
  disjoint S x
  disjoint B j
  disjoint B k
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint X f
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y k
  disjoint Y x
  disjoint Y y
  disjoint f m
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f z
  disjoint j m
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k z
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G m
  disjoint V m
  disjoint V z
  disjoint I m
  disjoint I w
  disjoint I z
  disjoint m ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint S m
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint B m
  disjoint D m
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint X m
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint Y m
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  assert |- ( ph -> ( G gsum ( n e. S |-> ( G gsum ( j e. { x e. D | x oR <_ n } |-> Y ) ) ) ) = ( G gsum ( j e. S |-> ( G gsum ( k e. { x e. D | x oR <_ ( F oF - j ) } |-> X ) ) ) ) )

  proof
    wph
    cG
    vm
    cS
    cG
    vj
    vx
    cv
    #
    cF
    vm
    cv
    #
    cmin
    cof
    #
    co
    #
    cle
    cofr
    #
    wbr
    #
    vx
    cD
    crab
    #
    vk
    @3
    vj
    cv
    #
    @2
    co
    #
    cX
    csb
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
    cG
    vj
    cS
    cG
    vm
    @0
    cF
    @7
    @2
    co
    #
    @4
    wbr
    #
    vx
    cD
    crab
    #
    @9
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
    cG
    vn
    cS
    cG
    vj
    @0
    vn
    cv
    #
    @4
    wbr
    #
    vx
    cD
    crab
    #
    cY
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
    cG
    vj
    cS
    cG
    vk
    @16
    cX
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    wph
    cG
    vm
    vj
    cS
    @6
    @9
    cmpt2
    cgsu
    co
    cG
    vj
    vm
    cS
    @16
    @9
    cmpt2
    cgsu
    co
    @13
    @20
    wph
    vx
    vy
    cB
    cD
    cS
    vf
    vm
    vj
    cF
    cG
    cI
    cV
    @9
    psrbag.d
    psrbagconf1o.1
    gsumbagdiag.i
    gsumbagdiag.f
    gsumbagdiag.b
    gsumbagdiag.g
    wph
    @1
    cS
    wcel
    #
    @7
    @6
    wcel
    #
    wa
    #
    @7
    cS
    wcel
    #
    @1
    @16
    wcel
    #
    wa
    #
    @9
    cB
    wcel
    #
    wph
    vx
    vy
    cD
    cS
    vf
    cF
    cI
    cV
    @1
    @7
    psrbag.d
    psrbagconf1o.1
    gsumbagdiag.i
    gsumbagdiag.f
    gsumbagdiaglem
    #
    wph
    @34
    @35
    @37
    wph
    @34
    wa
    #
    @37
    vm
    @16
    @39
    @16
    cB
    @17
    wf
    #
    @37
    vm
    @16
    wral
    @39
    @16
    cB
    @28
    vm
    @16
    @14
    @1
    @2
    co
    #
    cmpt
    #
    ccom
    #
    wf
    #
    @40
    @39
    @16
    cB
    @28
    wf
    @16
    @16
    @42
    wf
    #
    @44
    @39
    vk
    @16
    cX
    cB
    @28
    wph
    @34
    vk
    cv
    @16
    wcel
    cX
    cB
    wcel
    gsumbagdiag.x
    anassrs
    @28
    eqid
    #
    fmptd
    #
    @39
    @16
    @16
    @42
    wf1o
    #
    @45
    @39
    cI
    cV
    wcel
    #
    @14
    cD
    wcel
    #
    @48
    wph
    @49
    @34
    gsumbagdiag.i
    adantr
    #
    @39
    cS
    cD
    @14
    cS
    vy
    cv
    cF
    @4
    wbr
    #
    vy
    cD
    crab
    #
    cD
    psrbagconf1o.1
    @52
    vy
    cD
    ssrab2
    eqsstri
    #
    @39
    @49
    cF
    cD
    wcel
    #
    @34
    @14
    cS
    wcel
    @51
    wph
    @55
    @34
    gsumbagdiag.f
    adantr
    #
    wph
    @34
    simpr
    #
    vy
    cD
    cS
    vf
    cF
    cI
    cV
    @7
    psrbag.d
    psrbagconf1o.1
    psrbagconcl
    syl3anc
    sseldi
    #
    vm
    vx
    cD
    @16
    vf
    @14
    cI
    cV
    psrbag.d
    @16
    eqid
    #
    psrbagconf1o
    syl2anc
    #
    @16
    @16
    @42
    f1of
    syl
    @16
    @16
    cB
    @28
    @42
    fco
    syl2anc
    @39
    @16
    cB
    @43
    @17
    @39
    vm
    vn
    @16
    @16
    @8
    vk
    @21
    cX
    csb
    #
    @9
    @42
    @28
    @39
    @35
    wa
    #
    @41
    @8
    @16
    @62
    vz
    cI
    vz
    cv
    #
    cF
    cfv
    #
    @63
    @7
    cfv
    #
    cmin
    co
    #
    @63
    @1
    cfv
    #
    cmin
    co
    #
    cmpt
    vz
    cI
    @64
    @67
    cmin
    co
    #
    @65
    cmin
    co
    #
    cmpt
    @41
    @8
    @62
    vz
    cI
    @68
    @70
    @62
    @63
    cI
    wcel
    wa
    #
    @64
    cn0
    wcel
    #
    @65
    cn0
    wcel
    #
    @67
    cn0
    wcel
    #
    @68
    @70
    wceq
    #
    @62
    cI
    cn0
    @63
    cF
    @62
    @49
    @55
    cI
    cn0
    cF
    wf
    @39
    @49
    @35
    @51
    adantr
    #
    @39
    @55
    @35
    @56
    adantr
    cD
    vf
    cF
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    #
    ffvelrnda
    #
    @62
    cI
    cn0
    @63
    @7
    @62
    @49
    @7
    cD
    wcel
    cI
    cn0
    @7
    wf
    @76
    @62
    cS
    cD
    @7
    @54
    @39
    @34
    @35
    @57
    adantr
    sseldi
    cD
    vf
    @7
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    #
    ffvelrnda
    #
    @62
    cI
    cn0
    @63
    @1
    @62
    @49
    @1
    cD
    wcel
    cI
    cn0
    @1
    wf
    @76
    @62
    @16
    cD
    @1
    @15
    vx
    cD
    ssrab2
    @39
    @35
    simpr
    #
    sseldi
    cD
    vf
    @1
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    #
    ffvelrnda
    #
    @72
    @64
    cc
    wcel
    @73
    @65
    cc
    wcel
    @74
    @67
    cc
    wcel
    @75
    @64
    nn0cn
    @65
    nn0cn
    @67
    nn0cn
    @64
    @65
    @67
    sub32
    syl3an
    syl3anc
    mpteq2dva
    @62
    vz
    cI
    @66
    @67
    cmin
    @14
    @1
    cV
    cvv
    cn0
    @76
    @71
    @64
    @65
    cmin
    ovexd
    @83
    @62
    vz
    cI
    @64
    @65
    cmin
    cF
    @7
    cV
    cn0
    cn0
    @76
    @78
    @80
    @62
    vz
    cI
    cn0
    cF
    @77
    feqmptd
    #
    @62
    vz
    cI
    cn0
    @7
    @79
    feqmptd
    #
    offval2
    @62
    vz
    cI
    cn0
    @1
    @82
    feqmptd
    #
    offval2
    @62
    vz
    cI
    @69
    @65
    cmin
    @3
    @7
    cV
    cvv
    cn0
    @76
    @71
    @64
    @67
    cmin
    ovexd
    @80
    @62
    vz
    cI
    @64
    @67
    cmin
    cF
    @1
    cV
    cn0
    cn0
    @76
    @78
    @83
    @84
    @86
    offval2
    @85
    offval2
    3eqtr4d
    #
    @62
    @49
    @50
    @35
    @41
    @16
    wcel
    @76
    @39
    @50
    @35
    @58
    adantr
    @81
    vx
    cD
    @16
    vf
    @14
    cI
    cV
    @1
    psrbag.d
    @59
    psrbagconcl
    syl3anc
    eqeltrrd
    @39
    vm
    @16
    @41
    @8
    @87
    mpteq2dva
    @28
    vn
    @16
    @61
    cmpt
    wceq
    @39
    vk
    vn
    @16
    cX
    @61
    vn
    cX
    nfcv
    vk
    @21
    cX
    nfcsb1v
    vk
    @21
    cX
    csbeq1a
    cbvmpt
    a1i
    vk
    @21
    @8
    cX
    csbeq1
    fmptco
    #
    feq1d
    mpbid
    vm
    @16
    cB
    @9
    @17
    @17
    eqid
    fmpt
    sylibr
    r19.21bi
    anasss
    #
    syldan
    #
    gsumbagdiag
    wph
    cS
    cB
    @6
    cS
    cS
    cxp
    #
    vm
    vj
    cG
    cfn
    cfn
    @9
    cG
    c0g
    cfv
    #
    gsumbagdiag.b
    @92
    eqid
    #
    gsumbagdiag.g
    wph
    cS
    @53
    cfn
    psrbagconf1o.1
    wph
    @49
    @55
    @53
    cfn
    wcel
    gsumbagdiag.i
    gsumbagdiag.f
    vy
    cD
    vf
    cF
    cI
    cV
    psrbag.d
    psrbaglefi
    syl2anc
    syl5eqel
    #
    wph
    @31
    wa
    #
    @49
    @3
    cD
    wcel
    @6
    cfn
    wcel
    #
    wph
    @49
    @31
    gsumbagdiag.i
    adantr
    #
    @95
    cS
    cD
    @3
    @54
    @95
    @49
    @55
    @31
    @3
    cS
    wcel
    @97
    wph
    @55
    @31
    gsumbagdiag.f
    adantr
    wph
    @31
    simpr
    vy
    cD
    cS
    vf
    cF
    cI
    cV
    @1
    psrbag.d
    psrbagconf1o.1
    psrbagconcl
    syl3anc
    #
    sseldi
    vx
    cD
    vf
    @3
    cI
    cV
    psrbag.d
    psrbaglefi
    syl2anc
    #
    @90
    wph
    cS
    cfn
    wcel
    #
    @100
    @91
    cfn
    wcel
    @94
    @94
    cS
    cS
    xpfi
    syl2anc
    #
    wph
    @33
    @1
    @7
    @91
    wbr
    #
    wn
    @9
    @92
    wceq
    #
    wph
    @33
    wa
    #
    @102
    @103
    @104
    @31
    @34
    @102
    wph
    @31
    @32
    simprl
    @104
    @34
    @35
    @38
    simpld
    @1
    @7
    cS
    cS
    brxp
    sylanbrc
    pm2.24d
    impr
    gsum2d2
    wph
    cS
    cB
    @16
    @91
    vj
    vm
    cG
    cfn
    cfn
    @9
    @92
    gsumbagdiag.b
    @93
    gsumbagdiag.g
    @94
    @39
    @49
    @50
    @16
    cfn
    wcel
    #
    @51
    @58
    vx
    cD
    vf
    @14
    cI
    cV
    psrbag.d
    psrbaglefi
    syl2anc
    #
    @89
    @101
    wph
    @36
    @7
    @1
    @91
    wbr
    #
    wn
    @103
    wph
    @36
    wa
    #
    @107
    @103
    @108
    @34
    @31
    @107
    wph
    @34
    @35
    simprl
    @108
    @31
    @32
    wph
    vx
    vy
    cD
    cS
    vf
    cF
    cI
    cV
    @7
    @1
    psrbag.d
    psrbagconf1o.1
    gsumbagdiag.i
    gsumbagdiag.f
    gsumbagdiaglem
    simpld
    @7
    @1
    cS
    cS
    brxp
    sylanbrc
    pm2.24d
    impr
    gsum2d2
    3eqtr3d
    wph
    @27
    cG
    @26
    vm
    cS
    @3
    cmpt
    #
    ccom
    #
    cgsu
    co
    @13
    wph
    cS
    cB
    cS
    @26
    cG
    @109
    cfn
    @92
    gsumbagdiag.b
    @93
    gsumbagdiag.g
    @94
    wph
    cS
    cB
    @12
    @109
    ccnv
    #
    ccom
    #
    wf
    #
    cS
    cB
    @26
    wf
    wph
    cS
    cB
    @12
    wf
    cS
    cS
    @111
    wf
    #
    @113
    wph
    vm
    cS
    @11
    cB
    @12
    @95
    @6
    cB
    @10
    cG
    cfn
    @92
    gsumbagdiag.b
    @93
    wph
    cG
    ccmn
    wcel
    #
    @31
    gsumbagdiag.g
    adantr
    @99
    @95
    vj
    @6
    @9
    cB
    @10
    wph
    @31
    @32
    @37
    @90
    anassrs
    @10
    eqid
    #
    fmptd
    @95
    @10
    cvv
    wcel
    #
    @10
    wfun
    #
    @92
    cvv
    wcel
    #
    @96
    @10
    @92
    csupp
    co
    #
    @6
    wss
    #
    @10
    @92
    cfsupp
    wbr
    @95
    cD
    cvv
    wcel
    #
    @6
    cvv
    wcel
    @117
    @122
    @95
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    cD
    psrbag.d
    cn0
    cI
    cmap
    ovex
    rabex2
    #
    a1i
    @5
    vx
    cD
    cvv
    rabexg
    vj
    @6
    @9
    cvv
    mptexg
    3syl
    @118
    @95
    vj
    @6
    @9
    funmpt
    a1i
    @95
    cG
    c0g
    fvexd
    @99
    @121
    @95
    @120
    @10
    cdm
    @6
    @10
    @92
    suppssdm
    vj
    @6
    @9
    @10
    @116
    dmmptss
    sstri
    a1i
    @6
    @10
    cvv
    cvv
    @92
    suppssfifsupp
    syl32anc
    gsumcl
    @12
    eqid
    fmptd
    wph
    cS
    cS
    @109
    wf1o
    #
    cS
    cS
    @111
    wf1o
    @114
    wph
    @49
    @55
    @124
    gsumbagdiag.i
    gsumbagdiag.f
    vm
    vy
    cD
    cS
    vf
    cF
    cI
    cV
    psrbag.d
    psrbagconf1o.1
    psrbagconf1o
    syl2anc
    #
    cS
    cS
    @109
    f1ocnv
    cS
    cS
    @111
    f1of
    3syl
    cS
    cS
    cB
    @12
    @111
    fco
    syl2anc
    wph
    cS
    cB
    @112
    @26
    wph
    @110
    @111
    ccom
    #
    @26
    cid
    cS
    cres
    #
    ccom
    #
    @112
    @26
    wph
    @126
    @26
    @109
    @111
    ccom
    #
    ccom
    @128
    @26
    @109
    @111
    coass
    wph
    @129
    @127
    @26
    wph
    @124
    @129
    @127
    wceq
    @125
    cS
    cS
    @109
    f1ococnv2
    syl
    coeq2d
    syl5eq
    wph
    @110
    @12
    @111
    wph
    vm
    vn
    cS
    cS
    @3
    @25
    @11
    @109
    @26
    @98
    wph
    @109
    eqidd
    wph
    @26
    eqidd
    @21
    @3
    wceq
    #
    @24
    @10
    cG
    cgsu
    @130
    vj
    @23
    cY
    @6
    @9
    @130
    @22
    @5
    vx
    cD
    @21
    @3
    @0
    @4
    breq2
    rabbidv
    @130
    cY
    vk
    @21
    @7
    @2
    co
    #
    cX
    csb
    @9
    vk
    @131
    cX
    cY
    @21
    @7
    @2
    ovex
    psrass1lem.y
    csbie
    @130
    vk
    @131
    @8
    cX
    @21
    @3
    @7
    @2
    oveq1
    csbeq1d
    syl5eqr
    mpteq12dv
    oveq2d
    fmptco
    #
    coeq1d
    @128
    @26
    wceq
    wph
    @128
    @26
    cS
    cres
    #
    @26
    @26
    cS
    coires1
    cS
    cS
    wss
    @133
    @26
    wceq
    cS
    ssid
    vn
    cS
    cS
    @25
    resmpt
    ax-mp
    eqtri
    a1i
    3eqtr3d
    feq1d
    mpbid
    wph
    @26
    cvv
    wcel
    #
    @26
    wfun
    #
    @119
    @100
    @26
    @92
    csupp
    co
    #
    cS
    wss
    #
    @26
    @92
    cfsupp
    wbr
    wph
    cS
    cvv
    wcel
    @134
    wph
    cS
    @53
    cvv
    psrbagconf1o.1
    @122
    @53
    cvv
    wcel
    wph
    @123
    @52
    vy
    cD
    cvv
    rabexg
    mp1i
    syl5eqel
    vn
    cS
    @25
    cvv
    mptexg
    syl
    @135
    wph
    vn
    cS
    @25
    funmpt
    a1i
    wph
    cG
    c0g
    fvexd
    @94
    @137
    wph
    @136
    @26
    cdm
    cS
    @26
    @92
    suppssdm
    vn
    cS
    @25
    @26
    @26
    eqid
    dmmptss
    sstri
    a1i
    cS
    @26
    cvv
    cvv
    @92
    suppssfifsupp
    syl32anc
    @125
    gsumf1o
    wph
    @110
    @12
    cG
    cgsu
    @132
    oveq2d
    eqtrd
    wph
    @30
    @19
    cG
    cgsu
    wph
    vj
    cS
    @29
    @18
    @39
    @29
    cG
    @43
    cgsu
    co
    @18
    @39
    @16
    cB
    @16
    @28
    cG
    @42
    cfn
    @92
    gsumbagdiag.b
    @93
    wph
    @115
    @34
    gsumbagdiag.g
    adantr
    @106
    @47
    @39
    @28
    cvv
    wcel
    #
    @28
    wfun
    #
    @119
    @105
    @28
    @92
    csupp
    co
    #
    @16
    wss
    #
    @28
    @92
    cfsupp
    wbr
    @39
    @122
    @16
    cvv
    wcel
    @138
    @122
    @39
    @123
    a1i
    @15
    vx
    cD
    cvv
    rabexg
    vk
    @16
    cX
    cvv
    mptexg
    3syl
    @139
    @39
    vk
    @16
    cX
    funmpt
    a1i
    @39
    cG
    c0g
    fvexd
    @106
    @141
    @39
    @140
    @28
    cdm
    @16
    @28
    @92
    suppssdm
    vk
    @16
    cX
    @28
    @46
    dmmptss
    sstri
    a1i
    @16
    @28
    cvv
    cvv
    @92
    suppssfifsupp
    syl32anc
    @60
    gsumf1o
    @39
    @43
    @17
    cG
    cgsu
    @88
    oveq2d
    eqtrd
    mpteq2dva
    oveq2d
    3eqtr4d
end
