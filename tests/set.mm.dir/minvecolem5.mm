include "cn.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cdiv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "wcel.mm"
include "csqrt.mm"
include "wn.mm"
include "clt.mm"
include "cc0.mm"
include "nnrecgt0.mm"
include "adantl.mm"
include "cr.mm"
include "nnrecre.mm"
include "cinf.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "minvecolem1.mm"
include "adantr.mm"
include "simp1d.mm"
include "simp2d.mm"
include "0re.mm"
include "simp3d.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "infrecl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "resqcld.mm"
include "ltaddposd.mm"
include "mpbid.mm"
include "readdcld.mm"
include "sqge0d.mm"
include "addgegt0d.mm"
include "elrpd.mm"
include "rpge0d.mm"
include "resqrtth.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "rpsqrtcld.mm"
include "rpred.mm"
include "wb.mm"
include "0red.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "syl6breqr.mm"
include "sqrtge0d.mm"
include "lt2sqd.mm"
include "ltnled.mm"
include "breq2i.mm"
include "syl5bb.mm"
include "cmpt.mm"
include "crn.mm"
include "raleqi.mm"
include "cvv.mm"
include "fvex.mm"
include "rgenw.mm"
include "eqid.mm"
include "breq2.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "bitri.mm"
include "syl6bb.mm"
include "mtbid.mm"
include "rexnal.mm"
include "sylibr.mm"
include "cnv.mm"
include "ccphlo.mm"
include "phnv.mm"
include "syl.mm"
include "ad2antrr.mm"
include "css.mm"
include "ccbn.mm"
include "cin.mm"
include "inss1.mm"
include "sseldi.mm"
include "sspba.mm"
include "sselda.mm"
include "nvmcl.mm"
include "nvcl.mm"
include "letrid.mm"
include "ord.mm"
include "nvge0.mm"
include "le2sqd.mm"
include "breq1d.mm"
include "bitrd.mm"
include "notbid.mm"
include "imsdval.mm"
include "oveq1d.mm"
include "3imtr4d.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "cba.mm"
include "eqeltri.mm"
include "nnenom.mm"
include "oveq2.mm"
include "axcc4.mm"
include "clm.mm"
include "cmin.mm"
include "simprl.mm"
include "simprr.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "minvecolem4.mm"
include "exlimddv.mm"

theorem minvecolem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let cJ: class J
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vw: setvar w
  let cK: class K
  let cL: class L
  let vf: setvar f
  let cT: class T
  assume minveco.x: |- X = ( BaseSet ` U )
  assume minveco.m: |- M = ( -v ` U )
  assume minveco.n: |- N = ( normCV ` U )
  assume minveco.y: |- Y = ( BaseSet ` W )
  assume minveco.u: |- ( ph -> U e. CPreHilOLD )
  assume minveco.w: |- ( ph -> W e. ( ( SubSp ` U ) i^i CBan ) )
  assume minveco.a: |- ( ph -> A e. X )
  assume minveco.d: |- D = ( IndMet ` U )
  assume minveco.j: |- J = ( MetOpen ` D )
  assume minveco.r: |- R = ran ( y e. Y |-> ( N ` ( A M y ) ) )
  assume minveco.s: |- S = inf ( R , RR , < )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint S x
  disjoint S y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint U x
  disjoint U y
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint Y x
  disjoint Y y
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint n w
  disjoint J n
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint K y
  disjoint L y
  disjoint f j
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint M f
  disjoint j w
  disjoint M j
  disjoint M w
  disjoint N f
  disjoint N j
  disjoint N w
  disjoint f k
  disjoint f n
  disjoint f ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph w
  disjoint R w
  disjoint S f
  disjoint S k
  disjoint S n
  disjoint S w
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A n
  disjoint A w
  disjoint D f
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D w
  disjoint U w
  disjoint W w
  disjoint T n
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X w
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y n
  disjoint Y w
  assert |- ( ph -> E. x e. Y A. y e. Y ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) )

  proof
    wph
    cn
    cY
    vf
    cv
    #
    wf
    #
    cA
    vn
    cv
    #
    @0
    cfv
    #
    cD
    co
    #
    c2
    cexp
    co
    #
    cS
    c2
    cexp
    co
    #
    c1
    @2
    cdiv
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    vn
    cn
    wral
    #
    wa
    #
    cA
    vx
    cv
    #
    cM
    co
    cN
    cfv
    cA
    vy
    cv
    #
    cM
    co
    #
    cN
    cfv
    #
    cle
    wbr
    vy
    cY
    wral
    vx
    cY
    wrex
    vf
    wph
    cA
    @13
    cD
    co
    #
    c2
    cexp
    co
    #
    @8
    cle
    wbr
    #
    vy
    cY
    wrex
    #
    vn
    cn
    wral
    @11
    vf
    wex
    wph
    @19
    vn
    cn
    wph
    @2
    cn
    wcel
    #
    wa
    #
    @8
    csqrt
    cfv
    #
    @15
    cle
    wbr
    #
    wn
    #
    vy
    cY
    wrex
    #
    @19
    @21
    @23
    vy
    cY
    wral
    #
    wn
    @25
    @21
    @22
    cS
    cle
    wbr
    #
    @26
    @21
    cS
    @22
    clt
    wbr
    #
    @27
    wn
    @21
    @28
    @6
    @22
    c2
    cexp
    co
    #
    clt
    wbr
    @21
    @6
    @8
    @29
    clt
    @21
    cc0
    @7
    clt
    wbr
    #
    @6
    @8
    clt
    wbr
    @20
    @30
    wph
    @2
    nnrecgt0
    adantl
    #
    @21
    @7
    @6
    @20
    @7
    cr
    wcel
    wph
    @2
    nnrecre
    adantl
    #
    @21
    cS
    @21
    cS
    cR
    cr
    clt
    cinf
    #
    cr
    minveco.s
    @21
    cR
    cr
    wss
    #
    cR
    c0
    wne
    #
    @12
    vw
    cv
    #
    cle
    wbr
    #
    vw
    cR
    wral
    #
    vx
    cr
    wrex
    #
    @33
    cr
    wcel
    @21
    @34
    @35
    cc0
    @36
    cle
    wbr
    #
    vw
    cR
    wral
    #
    wph
    @34
    @35
    @41
    w3a
    @20
    wph
    vy
    vw
    cA
    cD
    cR
    cU
    cJ
    cM
    cN
    cW
    cX
    cY
    minveco.x
    minveco.m
    minveco.n
    minveco.y
    minveco.u
    minveco.w
    minveco.a
    minveco.d
    minveco.j
    minveco.r
    minvecolem1
    adantr
    #
    simp1d
    #
    @21
    @34
    @35
    @41
    @42
    simp2d
    #
    @21
    cc0
    cr
    wcel
    #
    @41
    @39
    0re
    @21
    @34
    @35
    @41
    @42
    simp3d
    #
    @38
    @41
    vx
    cc0
    cr
    @12
    cc0
    wceq
    @37
    @40
    vw
    cR
    @12
    cc0
    @36
    cle
    breq1
    ralbidv
    rspcev
    sylancr
    #
    vx
    vw
    cR
    infrecl
    syl3anc
    syl5eqel
    #
    resqcld
    #
    ltaddposd
    mpbid
    @21
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    @29
    @8
    wceq
    #
    @21
    @6
    @7
    @49
    @32
    readdcld
    #
    @21
    @8
    @21
    @8
    @52
    @21
    @6
    @7
    @49
    @32
    @21
    cS
    @48
    sqge0d
    @31
    addgegt0d
    elrpd
    #
    rpge0d
    #
    @8
    resqrtth
    syl2anc
    #
    breqtrrd
    @21
    cS
    @22
    @48
    @21
    @22
    @21
    @8
    @53
    rpsqrtcld
    rpred
    #
    @21
    cc0
    @33
    cS
    cle
    @21
    cc0
    @33
    cle
    wbr
    #
    @41
    @46
    @21
    @34
    @35
    @39
    @45
    @57
    @41
    wb
    @43
    @44
    @47
    @21
    0red
    vx
    vw
    vw
    cR
    cc0
    infregelb
    syl31anc
    mpbird
    minveco.s
    syl6breqr
    @21
    @8
    @52
    @54
    sqrtge0d
    #
    lt2sqd
    mpbird
    @21
    cS
    @22
    @48
    @56
    ltnled
    mpbid
    @21
    @27
    @22
    @36
    cle
    wbr
    #
    vw
    cR
    wral
    #
    @26
    @27
    @22
    @33
    cle
    wbr
    #
    @21
    @60
    cS
    @33
    @22
    cle
    minveco.s
    breq2i
    @21
    @34
    @35
    @39
    @22
    cr
    wcel
    #
    @61
    @60
    wb
    @43
    @44
    @47
    @56
    vx
    vw
    vw
    cR
    @22
    infregelb
    syl31anc
    syl5bb
    @60
    @59
    vw
    vy
    cY
    @15
    cmpt
    #
    crn
    #
    wral
    #
    @26
    @59
    vw
    cR
    @64
    minveco.r
    raleqi
    @15
    cvv
    wcel
    #
    vy
    cY
    wral
    @65
    @26
    wb
    @66
    vy
    cY
    @14
    cN
    fvex
    rgenw
    @59
    @23
    vy
    vw
    cY
    @15
    @63
    cvv
    @63
    eqid
    @36
    @15
    @22
    cle
    breq2
    ralrnmpt
    ax-mp
    bitri
    syl6bb
    mtbid
    @23
    vy
    cY
    rexnal
    sylibr
    @21
    @24
    @18
    vy
    cY
    @21
    @13
    cY
    wcel
    #
    wa
    #
    @8
    @15
    c2
    cexp
    co
    #
    cle
    wbr
    #
    wn
    @69
    @8
    cle
    wbr
    #
    @24
    @18
    @68
    @70
    @71
    @68
    @8
    @69
    @21
    @50
    @67
    @52
    adantr
    @68
    @15
    @68
    cU
    cnv
    wcel
    #
    @14
    cX
    wcel
    #
    @15
    cr
    wcel
    wph
    @72
    @20
    @67
    wph
    cU
    ccphlo
    wcel
    #
    @72
    minveco.u
    cU
    phnv
    syl
    #
    ad2antrr
    #
    @68
    @72
    cA
    cX
    wcel
    #
    @13
    cX
    wcel
    #
    @73
    @76
    wph
    @77
    @20
    @67
    minveco.a
    ad2antrr
    #
    @21
    cY
    cX
    @13
    wph
    cY
    cX
    wss
    #
    @20
    wph
    @72
    cW
    cU
    css
    cfv
    #
    wcel
    @80
    @75
    wph
    @81
    ccbn
    cin
    #
    @81
    cW
    @81
    ccbn
    inss1
    minveco.w
    sseldi
    cU
    @81
    cW
    cX
    cY
    minveco.x
    minveco.y
    @81
    eqid
    sspba
    syl2anc
    adantr
    sselda
    #
    cA
    @13
    cU
    cM
    cX
    minveco.x
    minveco.m
    nvmcl
    syl3anc
    #
    @14
    cU
    cN
    cX
    minveco.x
    minveco.n
    nvcl
    syl2anc
    #
    resqcld
    letrid
    ord
    @68
    @23
    @70
    @68
    @23
    @29
    @69
    cle
    wbr
    @70
    @68
    @22
    @15
    @21
    @62
    @67
    @56
    adantr
    @85
    @21
    cc0
    @22
    cle
    wbr
    @67
    @58
    adantr
    @68
    @72
    @73
    cc0
    @15
    cle
    wbr
    @76
    @84
    @14
    cU
    cN
    cX
    minveco.x
    minveco.n
    nvge0
    syl2anc
    le2sqd
    @68
    @29
    @8
    @69
    cle
    @21
    @51
    @67
    @55
    adantr
    breq1d
    bitrd
    notbid
    @68
    @17
    @69
    @8
    cle
    @68
    @16
    @15
    c2
    cexp
    @68
    @72
    @77
    @78
    @16
    @15
    wceq
    @76
    @79
    @83
    cA
    @13
    cD
    cU
    cM
    cN
    cX
    minveco.x
    minveco.m
    minveco.n
    minveco.d
    imsdval
    syl3anc
    oveq1d
    breq1d
    3imtr4d
    reximdva
    mpd
    ralrimiva
    @18
    @9
    vy
    cY
    vf
    vn
    cn
    cY
    cW
    cba
    cfv
    cvv
    minveco.y
    cW
    cba
    fvex
    eqeltri
    nnenom
    @13
    @3
    wceq
    #
    @17
    @5
    @8
    cle
    @86
    @16
    @4
    c2
    cexp
    @13
    @3
    cA
    cD
    oveq2
    oveq1d
    breq1d
    axcc4
    syl
    wph
    @11
    wa
    #
    vx
    vy
    cA
    cD
    cR
    cS
    c1
    cA
    @0
    cJ
    clm
    cfv
    cfv
    cD
    co
    cS
    caddc
    co
    c2
    cdiv
    co
    c2
    cexp
    co
    @6
    cmin
    co
    cdiv
    co
    #
    cU
    vk
    @0
    cJ
    cM
    cN
    cW
    cX
    cY
    minveco.x
    minveco.m
    minveco.n
    minveco.y
    wph
    @74
    @11
    minveco.u
    adantr
    wph
    cW
    @82
    wcel
    @11
    minveco.w
    adantr
    wph
    @77
    @11
    minveco.a
    adantr
    minveco.d
    minveco.j
    minveco.r
    minveco.s
    wph
    @1
    @10
    simprl
    @87
    @10
    vk
    cv
    #
    cn
    wcel
    cA
    @89
    @0
    cfv
    #
    cD
    co
    #
    c2
    cexp
    co
    #
    @6
    c1
    @89
    cdiv
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    wph
    @1
    @10
    simprr
    @9
    @95
    vn
    @89
    cn
    @2
    @89
    wceq
    #
    @5
    @92
    @8
    @94
    cle
    @96
    @4
    @91
    c2
    cexp
    @96
    @3
    @90
    cA
    cD
    @2
    @89
    @0
    fveq2
    oveq2d
    oveq1d
    @96
    @7
    @93
    @6
    caddc
    @2
    @89
    c1
    cdiv
    oveq2
    oveq2d
    breq12d
    rspccva
    sylan
    @88
    eqid
    minvecolem4
    exlimddv
end
