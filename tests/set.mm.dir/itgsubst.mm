include "cv.mm"
include "cicc.mm"
include "co.mm"
include "cmpt.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "cdit.mm"
include "cmul.mm"
include "wceq.mm"
include "cioo.mm"
include "ccncf.mm"
include "cr.mm"
include "wss.mm"
include "cc.mm"
include "ioossre.mm"
include "ax-resscn.mm"
include "cncfss.mm"
include "mp2an.mm"
include "sseldi.mm"
include "evthicc.mm"
include "clt.mm"
include "wcel.mm"
include "cq.mm"
include "cxr.mm"
include "ressxr.mm"
include "sstri.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "adantr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "eliooord.mm"
include "simprd.mm"
include "qbtwnxr.mm"
include "syl3anc.mm"
include "qre.mm"
include "ad2antrl.mm"
include "ad2antrr.mm"
include "rexrd.mm"
include "simpld.mm"
include "simprrl.mm"
include "xrlttrd.mm"
include "simprrr.mm"
include "w3a.mm"
include "wb.mm"
include "elioo2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "anass.mm"
include "wi.mm"
include "ffvelrnda.mm"
include "simplr.mm"
include "xrlelttr.mm"
include "mpan2d.mm"
include "ralimdva.mm"
include "imp.mm"
include "an32s.mm"
include "sylanbr.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "rexlimdvaa.mm"
include "xrltletr.mm"
include "mpand.mm"
include "ancom.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "r19.26.mm"
include "3biant1d.mm"
include "simplrl.mm"
include "simplrr.mm"
include "bitr4d.mm"
include "ralbidva.mm"
include "nffvmpt1.mm"
include "nfel1.mm"
include "nfv.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "simpr.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "fvmpt2.mm"
include "syl5bb.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "syl5eqelr.mm"
include "cibl.mm"
include "cin.mm"
include "cdv.mm"
include "oveq2i.mm"
include "3eqtr3g.mm"
include "csbeq1.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprr.mm"
include "rspc.mm"
include "mpan9.mm"
include "itgsubstlem.mm"
include "cbvditg.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "ditgeq1.mm"
include "3syl.mm"
include "ditgeq2.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "csbeq1d.mm"
include "oveq12d.mm"
include "nfcsb.mm"
include "nfov.mm"
include "citg.mm"
include "ioossicc.mm"
include "sseli.mm"
include "sylan2.mm"
include "oveq1d.mm"
include "itgeq2dv.mm"
include "ditgpos.mm"
include "3eqtr4d.mm"
include "3eqtr3d.mm"
include "expr.mm"
include "sylbid.mm"
include "syl5bir.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "syl2and.mm"

theorem itgsubst
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vv: setvar v
  let cM: class M
  let cN: class N
  assume itgsubst.x: |- ( ph -> X e. RR )
  assume itgsubst.y: |- ( ph -> Y e. RR )
  assume itgsubst.le: |- ( ph -> X <_ Y )
  assume itgsubst.z: |- ( ph -> Z e. RR* )
  assume itgsubst.w: |- ( ph -> W e. RR* )
  assume itgsubst.a: |- ( ph -> ( x e. ( X [,] Y ) |-> A ) e. ( ( X [,] Y ) -cn-> ( Z (,) W ) ) )
  assume itgsubst.b: |- ( ph -> ( x e. ( X (,) Y ) |-> B ) e. ( ( ( X (,) Y ) -cn-> CC ) i^i L^1 ) )
  assume itgsubst.c: |- ( ph -> ( u e. ( Z (,) W ) |-> C ) e. ( ( Z (,) W ) -cn-> CC ) )
  assume itgsubst.da: |- ( ph -> ( RR _D ( x e. ( X [,] Y ) |-> A ) ) = ( x e. ( X (,) Y ) |-> B ) )
  assume itgsubst.e: |- ( u = A -> C = E )
  assume itgsubst.k: |- ( x = X -> A = K )
  assume itgsubst.l: |- ( x = Y -> A = L )

  disjoint E u
  disjoint u x
  disjoint K u
  disjoint K x
  disjoint ph u
  disjoint ph x
  disjoint X u
  disjoint X x
  disjoint Y u
  disjoint Y x
  disjoint A u
  disjoint C x
  disjoint W u
  disjoint W x
  disjoint L u
  disjoint L x
  disjoint Z u
  disjoint Z x
  disjoint m n
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint m u
  disjoint E m
  disjoint n u
  disjoint E n
  disjoint u y
  disjoint u z
  disjoint E y
  disjoint E z
  disjoint m x
  disjoint K m
  disjoint n x
  disjoint K n
  disjoint x z
  disjoint K z
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint M t
  disjoint u v
  disjoint M u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint M v
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint m t
  disjoint m v
  disjoint m ph
  disjoint n t
  disjoint n v
  disjoint n ph
  disjoint ph t
  disjoint ph v
  disjoint ph y
  disjoint ph z
  disjoint X m
  disjoint X n
  disjoint X t
  disjoint X v
  disjoint X y
  disjoint X z
  disjoint Y m
  disjoint Y n
  disjoint Y t
  disjoint Y v
  disjoint Y y
  disjoint Y z
  disjoint A m
  disjoint A n
  disjoint A t
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint W m
  disjoint W n
  disjoint W v
  disjoint W y
  disjoint W z
  disjoint L m
  disjoint L n
  disjoint L z
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Z m
  disjoint Z n
  disjoint Z v
  disjoint Z y
  disjoint Z z
  assert |- ( ph -> S_ [ K -> L ] C _d u = S_ [ X -> Y ] ( E x. B ) _d x )

  proof
    wph
    vz
    cv
    #
    vx
    cX
    cY
    cicc
    co
    #
    cA
    cmpt
    #
    cfv
    #
    vy
    cv
    #
    @2
    cfv
    #
    cle
    wbr
    #
    vz
    @1
    wral
    #
    vy
    @1
    wrex
    #
    @5
    @3
    cle
    wbr
    #
    vz
    @1
    wral
    #
    vy
    @1
    wrex
    #
    wa
    vu
    cK
    cL
    cC
    cdit
    #
    vx
    cX
    cY
    cE
    cB
    cmul
    co
    #
    cdit
    #
    wceq
    #
    wph
    vy
    vz
    vy
    vz
    cX
    cY
    @2
    itgsubst.x
    itgsubst.y
    itgsubst.le
    wph
    @1
    cZ
    cW
    cioo
    co
    #
    ccncf
    co
    #
    @1
    cr
    ccncf
    co
    #
    @2
    @16
    cr
    wss
    cr
    cc
    wss
    @17
    @18
    wss
    cZ
    cW
    ioossre
    #
    ax-resscn
    @1
    @16
    cr
    cncfss
    mp2an
    itgsubst.a
    sseldi
    evthicc
    wph
    @8
    @3
    vn
    cv
    #
    clt
    wbr
    #
    vz
    @1
    wral
    #
    vn
    @16
    wrex
    #
    @11
    vm
    cv
    #
    @3
    clt
    wbr
    #
    vz
    @1
    wral
    #
    vm
    @16
    wrex
    #
    @15
    wph
    @7
    @23
    vy
    @1
    wph
    @4
    @1
    wcel
    #
    @7
    wa
    #
    wa
    #
    @5
    @20
    clt
    wbr
    #
    @20
    cW
    clt
    wbr
    #
    wa
    #
    vn
    cq
    wrex
    #
    @23
    @30
    @5
    cxr
    wcel
    #
    cW
    cxr
    wcel
    #
    @5
    cW
    clt
    wbr
    #
    @34
    @30
    @16
    cxr
    @5
    @16
    cr
    cxr
    @19
    ressxr
    sstri
    #
    @30
    @1
    @16
    @4
    @2
    wph
    @1
    @16
    @2
    wf
    #
    @29
    wph
    @2
    @17
    wcel
    @39
    itgsubst.a
    @1
    @16
    @2
    cncff
    syl
    #
    adantr
    wph
    @28
    @7
    simprl
    ffvelrnd
    #
    sseldi
    #
    wph
    @36
    @29
    itgsubst.w
    adantr
    @30
    cZ
    @5
    clt
    wbr
    #
    @37
    @30
    @5
    @16
    wcel
    #
    @43
    @37
    wa
    #
    @41
    @5
    cZ
    cW
    eliooord
    #
    syl
    #
    simprd
    vn
    @5
    cW
    qbtwnxr
    syl3anc
    @30
    @33
    @22
    vn
    cq
    @16
    @30
    @20
    cq
    wcel
    #
    @33
    wa
    #
    @20
    @16
    wcel
    #
    @22
    wa
    @30
    @49
    wa
    #
    @50
    @22
    @51
    @50
    @20
    cr
    wcel
    #
    cZ
    @20
    clt
    wbr
    #
    @32
    @48
    @52
    @30
    @33
    @20
    qre
    #
    ad2antrl
    #
    @51
    cZ
    @5
    @20
    wph
    cZ
    cxr
    wcel
    #
    @29
    @49
    itgsubst.z
    ad2antrr
    #
    @30
    @35
    @49
    @42
    adantr
    @51
    @20
    @55
    rexrd
    @30
    @43
    @49
    @30
    @43
    @37
    @47
    simpld
    adantr
    @30
    @48
    @31
    @32
    simprrl
    xrlttrd
    @30
    @48
    @31
    @32
    simprrr
    @51
    @56
    @36
    @50
    @52
    @53
    @32
    w3a
    wb
    @57
    wph
    @36
    @29
    @49
    itgsubst.w
    ad2antrr
    cZ
    cW
    @20
    elioo2
    syl2anc
    mpbir3and
    @30
    wph
    @28
    wa
    #
    @7
    wa
    @49
    @22
    wph
    @28
    @7
    anass
    @58
    @49
    @7
    @22
    @58
    @49
    wa
    #
    @7
    @22
    @59
    @6
    @21
    vz
    @1
    @59
    @0
    @1
    wcel
    #
    wa
    #
    @6
    @31
    @21
    @59
    @31
    @60
    @58
    @48
    @31
    @32
    simprrl
    adantr
    @61
    @3
    cxr
    wcel
    #
    @35
    @20
    cxr
    wcel
    #
    @6
    @31
    wa
    @21
    wi
    @61
    @16
    cxr
    @3
    @38
    @59
    @1
    @16
    @0
    @2
    wph
    @39
    @28
    @49
    @40
    ad2antrr
    #
    ffvelrnda
    sseldi
    @59
    @35
    @60
    @59
    @16
    cxr
    @5
    @38
    @59
    @1
    @16
    @4
    @2
    @64
    wph
    @28
    @49
    simplr
    ffvelrnd
    sseldi
    adantr
    @61
    @20
    @59
    @52
    @60
    @48
    @52
    @58
    @33
    @54
    ad2antrl
    adantr
    rexrd
    @3
    @5
    @20
    xrlelttr
    syl3anc
    mpan2d
    ralimdva
    imp
    an32s
    sylanbr
    jca
    ex
    reximdv2
    mpd
    rexlimdvaa
    wph
    @10
    @27
    vy
    @1
    wph
    @28
    @10
    wa
    #
    wa
    #
    cZ
    @24
    clt
    wbr
    #
    @24
    @5
    clt
    wbr
    #
    wa
    #
    vm
    cq
    wrex
    #
    @27
    @66
    @56
    @35
    @43
    @70
    wph
    @56
    @65
    itgsubst.z
    adantr
    @66
    @16
    cxr
    @5
    @38
    @66
    @1
    @16
    @4
    @2
    wph
    @39
    @65
    @40
    adantr
    wph
    @28
    @10
    simprl
    ffvelrnd
    #
    sseldi
    #
    @66
    @43
    @37
    @66
    @44
    @45
    @71
    @46
    syl
    #
    simpld
    vm
    cZ
    @5
    qbtwnxr
    syl3anc
    @66
    @69
    @26
    vm
    cq
    @16
    @66
    @24
    cq
    wcel
    #
    @69
    wa
    #
    @24
    @16
    wcel
    #
    @26
    wa
    @66
    @75
    wa
    #
    @76
    @26
    @77
    @76
    @24
    cr
    wcel
    #
    @67
    @24
    cW
    clt
    wbr
    #
    @74
    @78
    @66
    @69
    @24
    qre
    #
    ad2antrl
    #
    @66
    @74
    @67
    @68
    simprrl
    @77
    @24
    @5
    cW
    @77
    @24
    @81
    rexrd
    @66
    @35
    @75
    @72
    adantr
    wph
    @36
    @65
    @75
    itgsubst.w
    ad2antrr
    #
    @66
    @74
    @67
    @68
    simprrr
    @66
    @37
    @75
    @66
    @43
    @37
    @73
    simprd
    adantr
    xrlttrd
    @77
    @56
    @36
    @76
    @78
    @67
    @79
    w3a
    wb
    wph
    @56
    @65
    @75
    itgsubst.z
    ad2antrr
    @82
    cZ
    cW
    @24
    elioo2
    syl2anc
    mpbir3and
    @66
    @58
    @10
    wa
    @75
    @26
    wph
    @28
    @10
    anass
    @58
    @75
    @10
    @26
    @58
    @75
    wa
    #
    @10
    @26
    @83
    @9
    @25
    vz
    @1
    @83
    @60
    wa
    #
    @68
    @9
    @25
    @83
    @68
    @60
    @58
    @74
    @67
    @68
    simprrr
    adantr
    @84
    @24
    cxr
    wcel
    #
    @35
    @62
    @68
    @9
    wa
    @25
    wi
    @84
    @24
    @83
    @78
    @60
    @74
    @78
    @58
    @69
    @80
    ad2antrl
    adantr
    rexrd
    @83
    @35
    @60
    @83
    @16
    cxr
    @5
    @38
    @83
    @1
    @16
    @4
    @2
    wph
    @39
    @28
    @75
    @40
    ad2antrr
    #
    wph
    @28
    @75
    simplr
    ffvelrnd
    sseldi
    adantr
    @84
    @16
    cxr
    @3
    @38
    @83
    @1
    @16
    @0
    @2
    @86
    ffvelrnda
    sseldi
    @24
    @5
    @3
    xrltletr
    syl3anc
    mpand
    ralimdva
    imp
    an32s
    sylanbr
    jca
    ex
    reximdv2
    mpd
    rexlimdvaa
    @23
    @27
    wa
    #
    @26
    @22
    wa
    #
    vn
    @16
    wrex
    vm
    @16
    wrex
    #
    wph
    @15
    @87
    @27
    @23
    wa
    @89
    @23
    @27
    ancom
    @26
    @22
    vm
    vn
    @16
    @16
    reeanv
    bitr4i
    wph
    @88
    @15
    vm
    vn
    @16
    @16
    @88
    @25
    @21
    wa
    #
    vz
    @1
    wral
    #
    wph
    @76
    @50
    wa
    #
    wa
    #
    @15
    @25
    @21
    vz
    @1
    r19.26
    @93
    @91
    @3
    @24
    @20
    cioo
    co
    #
    wcel
    #
    vz
    @1
    wral
    #
    @15
    @93
    @90
    @95
    vz
    @1
    @93
    @60
    wa
    #
    @90
    @3
    cr
    wcel
    #
    @25
    @21
    w3a
    #
    @95
    @97
    @21
    @25
    @98
    @97
    @16
    cr
    @3
    @19
    @93
    @1
    @16
    @0
    @2
    wph
    @39
    @92
    @40
    adantr
    ffvelrnda
    sseldi
    3biant1d
    @97
    @85
    @63
    @95
    @99
    wb
    @97
    @16
    cxr
    @24
    @38
    wph
    @76
    @50
    @60
    simplrl
    sseldi
    @97
    @16
    cxr
    @20
    @38
    wph
    @76
    @50
    @60
    simplrr
    sseldi
    @24
    @20
    @3
    elioo2
    syl2anc
    bitr4d
    ralbidva
    @93
    @96
    cA
    @94
    wcel
    #
    vx
    @1
    wral
    #
    @15
    wph
    @96
    @101
    wb
    @92
    @96
    vx
    cv
    #
    @2
    cfv
    #
    @94
    wcel
    #
    vx
    @1
    wral
    wph
    @101
    @95
    @104
    vz
    vx
    @1
    vx
    @3
    @94
    vx
    @1
    cA
    @0
    nffvmpt1
    nfel1
    @104
    vz
    nfv
    vz
    vx
    weq
    @3
    @103
    @94
    @0
    @102
    @2
    fveq2
    eleq1d
    cbvral
    wph
    @104
    @100
    vx
    @1
    wph
    @102
    @1
    wcel
    #
    wa
    #
    @103
    cA
    @94
    @106
    @105
    cA
    @16
    wcel
    #
    @103
    cA
    wceq
    wph
    @105
    simpr
    wph
    @107
    vx
    @1
    wph
    @39
    @107
    vx
    @1
    wral
    @40
    vx
    @1
    @16
    cA
    @2
    @2
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    #
    vx
    @1
    cA
    @16
    @2
    @108
    fvmpt2
    syl2anc
    eleq1d
    ralbidva
    syl5bb
    adantr
    wph
    @92
    @101
    @15
    wph
    @92
    @101
    wa
    #
    wa
    #
    vv
    vx
    cX
    cA
    csb
    #
    vx
    cY
    cA
    csb
    #
    vu
    vv
    cv
    #
    cC
    csb
    #
    cdit
    #
    vy
    cX
    cY
    vu
    vx
    @4
    cA
    csb
    #
    cC
    csb
    #
    vx
    @4
    cB
    csb
    #
    cmul
    co
    #
    cdit
    #
    @12
    @14
    @111
    vy
    vv
    @117
    @119
    @115
    @118
    @112
    @113
    @24
    @20
    cW
    cX
    cY
    cZ
    wph
    cX
    cr
    wcel
    #
    @110
    itgsubst.x
    adantr
    wph
    cY
    cr
    wcel
    #
    @110
    itgsubst.y
    adantr
    wph
    cX
    cY
    cle
    wbr
    @110
    itgsubst.le
    adantr
    wph
    @56
    @110
    itgsubst.z
    adantr
    wph
    @36
    @110
    itgsubst.w
    adantr
    wph
    vy
    @1
    @117
    cmpt
    #
    @17
    wcel
    @110
    wph
    @124
    @2
    @17
    vx
    vy
    @1
    cA
    @117
    vy
    cA
    nfcv
    vx
    @4
    cA
    nfcsb1v
    #
    vx
    @4
    cA
    csbeq1a
    #
    cbvmpt
    #
    itgsubst.a
    syl5eqelr
    adantr
    wph
    vy
    cX
    cY
    cioo
    co
    #
    @119
    cmpt
    #
    @128
    cc
    ccncf
    co
    cibl
    cin
    #
    wcel
    @110
    wph
    @129
    vx
    @128
    cB
    cmpt
    #
    @130
    vx
    vy
    @128
    cB
    @119
    vy
    cB
    nfcv
    vx
    @4
    cB
    nfcsb1v
    #
    vx
    @4
    cB
    csbeq1a
    #
    cbvmpt
    #
    itgsubst.b
    syl5eqelr
    adantr
    wph
    vv
    @16
    @115
    cmpt
    #
    @16
    cc
    ccncf
    co
    #
    wcel
    @110
    wph
    @135
    vu
    @16
    cC
    cmpt
    @136
    vu
    vv
    @16
    cC
    @115
    vv
    cC
    nfcv
    #
    vu
    @114
    cC
    nfcsb1v
    #
    vu
    @114
    cC
    csbeq1a
    #
    cbvmpt
    itgsubst.c
    syl5eqelr
    adantr
    wph
    cr
    @124
    cdv
    co
    #
    @129
    wceq
    @110
    wph
    cr
    @2
    cdv
    co
    @131
    @140
    @129
    itgsubst.da
    @2
    @124
    cr
    cdv
    @127
    oveq2i
    @134
    3eqtr3g
    adantr
    vu
    @114
    @117
    cC
    csbeq1
    vx
    @4
    cX
    cA
    csbeq1
    vx
    @4
    cY
    cA
    csbeq1
    wph
    @76
    @50
    @101
    simprll
    wph
    @76
    @50
    @101
    simprlr
    @111
    @101
    @28
    @117
    @94
    wcel
    #
    wph
    @92
    @101
    simprr
    @100
    @141
    vx
    @4
    @1
    vx
    @117
    @94
    @125
    nfel1
    vx
    vy
    weq
    #
    cA
    @117
    @94
    @126
    eleq1d
    rspc
    mpan9
    itgsubstlem
    wph
    @116
    @12
    wceq
    @110
    wph
    @116
    vu
    @112
    @113
    cC
    cdit
    #
    @12
    vu
    vv
    @112
    @113
    cC
    @115
    @139
    @137
    @138
    cbvditg
    wph
    @143
    vu
    cK
    @113
    cC
    cdit
    #
    @12
    wph
    @122
    @112
    cK
    wceq
    @143
    @144
    wceq
    itgsubst.x
    vx
    cX
    cA
    cK
    cr
    @122
    vx
    cK
    nfcvd
    itgsubst.k
    csbiegf
    vu
    @112
    cK
    @113
    cC
    ditgeq1
    3syl
    wph
    @123
    @113
    cL
    wceq
    @144
    @12
    wceq
    itgsubst.y
    vx
    cY
    cA
    cL
    cr
    @123
    vx
    cL
    nfcvd
    itgsubst.l
    csbiegf
    vu
    @113
    cL
    cK
    cC
    ditgeq2
    3syl
    eqtrd
    syl5eqr
    adantr
    wph
    @121
    @14
    wceq
    @110
    wph
    @121
    vx
    cX
    cY
    vu
    cA
    cC
    csb
    #
    cB
    cmul
    co
    #
    cdit
    #
    @14
    vx
    vy
    cX
    cY
    @146
    @120
    @142
    @145
    @118
    cB
    @119
    cmul
    @142
    vu
    cA
    @117
    cC
    @126
    csbeq1d
    @133
    oveq12d
    vy
    @146
    nfcv
    vx
    @118
    @119
    cmul
    vx
    vu
    @117
    cC
    @125
    vx
    cC
    nfcv
    nfcsb
    vx
    cmul
    nfcv
    @132
    nfov
    cbvditg
    wph
    vx
    @128
    @146
    citg
    vx
    @128
    @13
    citg
    @147
    @14
    wph
    vx
    @128
    @146
    @13
    wph
    @102
    @128
    wcel
    #
    wa
    #
    @145
    cE
    cB
    cmul
    @149
    @107
    @145
    cE
    wceq
    @148
    wph
    @105
    @107
    @128
    @1
    @102
    cX
    cY
    ioossicc
    sseli
    @109
    sylan2
    vu
    cA
    cC
    cE
    @16
    @107
    vu
    cE
    nfcvd
    itgsubst.e
    csbiegf
    syl
    oveq1d
    itgeq2dv
    wph
    vx
    cX
    cY
    @146
    itgsubst.le
    ditgpos
    wph
    vx
    cX
    cY
    @13
    itgsubst.le
    ditgpos
    3eqtr4d
    syl5eqr
    adantr
    3eqtr3d
    expr
    sylbid
    sylbid
    syl5bir
    rexlimdvva
    syl5bi
    syl2and
    mpd
end
