include "cca.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "c4.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "cn0.mm"
include "4re.mm"
include "4pos.mm"
include "elrpii.mm"
include "cz.mm"
include "simpr.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "rpdivcl.mm"
include "sylancr.mm"
include "rprege0.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "4syl.mm"
include "cmul.mm"
include "cme.mm"
include "ccphlo.mm"
include "cnv.mm"
include "phnv.mm"
include "imsmet.mm"
include "3syl.mm"
include "ad2antrr.mm"
include "wss.mm"
include "css.mm"
include "syl.mm"
include "ccbn.mm"
include "cin.mm"
include "inss1.mm"
include "sseldi.mm"
include "eqid.mm"
include "sspba.mm"
include "syl2anc.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "eluznn.mm"
include "sylan.mm"
include "metcl.mm"
include "syl3anc.mm"
include "resqcld.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "rpmulcl.mm"
include "rpred.mm"
include "rpge0d.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "breq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "cinf.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "minvecolem1.mm"
include "0re.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mpan.mm"
include "3anim3i.mm"
include "infrecl.mm"
include "syl5eqel.mm"
include "nnrecred.mm"
include "readdcld.mm"
include "adantlr.mm"
include "eluzle.mm"
include "adantl.mm"
include "wb.mm"
include "rpregt0d.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "lerec.mm"
include "mpbid.mm"
include "leadd2dd.mm"
include "letrd.mm"
include "minvecolem2.mm"
include "cc.mm"
include "rpcnne0.mm"
include "ax-mp.mm"
include "recdiv.mm"
include "flltp1.mm"
include "eqbrtrd.mm"
include "ltrec1d.mm"
include "pm3.2i.mm"
include "ltmuldiv2.mm"
include "mp3an3.mm"
include "mpbird.mm"
include "lelttrd.mm"
include "metge0.mm"
include "ad2antlr.mm"
include "lt2sq.mm"
include "syl21anc.mm"
include "breq1d.mm"
include "raleqbidv.mm"
include "nnuz.mm"
include "cxmt.mm"
include "imsxmet.mm"
include "1zzd.mm"
include "eqidd.mm"
include "fssd.mm"
include "iscauf.mm"

theorem minvecolem3
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vx: setvar x
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
  assume minveco.f: |- ( ph -> F : NN --> Y )
  assume minveco.1: |- ( ( ph /\ n e. NN ) -> ( ( A D ( F ` n ) ) ^ 2 ) <_ ( ( S ^ 2 ) + ( 1 / n ) ) )

  disjoint n y
  disjoint F n
  disjoint F y
  disjoint J n
  disjoint J y
  disjoint M y
  disjoint N y
  disjoint n ph
  disjoint ph y
  disjoint S n
  disjoint S y
  disjoint A n
  disjoint A y
  disjoint D n
  disjoint D y
  disjoint U y
  disjoint W y
  disjoint X n
  disjoint Y n
  disjoint Y y
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint n x
  disjoint x y
  disjoint F x
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint n w
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint J x
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
  disjoint M x
  disjoint N f
  disjoint N j
  disjoint N w
  disjoint N x
  disjoint f k
  disjoint f n
  disjoint f ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint ph w
  disjoint ph x
  disjoint R w
  disjoint R x
  disjoint S f
  disjoint S k
  disjoint S w
  disjoint S x
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A w
  disjoint A x
  disjoint D f
  disjoint D j
  disjoint D k
  disjoint D w
  disjoint D x
  disjoint U w
  disjoint U x
  disjoint W w
  disjoint W x
  disjoint T n
  disjoint X j
  disjoint X k
  disjoint X w
  disjoint X x
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y w
  disjoint Y x
  assert |- ( ph -> F e. ( Cau ` D ) )

  proof
    wph
    cF
    cD
    cca
    cfv
    wcel
    vj
    cv
    #
    cF
    cfv
    #
    vn
    cv
    #
    cF
    cfv
    #
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vn
    @0
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    wph
    @9
    vx
    crp
    wph
    @5
    crp
    wcel
    #
    wa
    #
    c4
    @5
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cn
    wcel
    #
    @15
    cF
    cfv
    #
    @3
    cD
    co
    #
    @5
    clt
    wbr
    #
    vn
    @15
    cuz
    cfv
    #
    wral
    #
    @9
    @11
    @13
    crp
    wcel
    #
    @13
    cr
    wcel
    #
    cc0
    @13
    cle
    wbr
    wa
    @14
    cn0
    wcel
    @16
    @11
    c4
    crp
    wcel
    #
    @12
    crp
    wcel
    #
    @22
    c4
    4re
    4pos
    elrpii
    #
    @11
    @10
    c2
    cz
    wcel
    @25
    wph
    @10
    simpr
    2z
    @5
    c2
    rpexpcl
    sylancl
    #
    c4
    @12
    rpdivcl
    sylancr
    #
    @13
    rprege0
    @13
    flge0nn0
    @14
    nn0p1nn
    4syl
    #
    @11
    @19
    vn
    @20
    @11
    @2
    @20
    wcel
    #
    wa
    #
    @19
    @18
    c2
    cexp
    co
    #
    @12
    clt
    wbr
    #
    @31
    @32
    c4
    c1
    @15
    cdiv
    co
    #
    cmul
    co
    #
    @12
    @31
    @18
    @31
    cD
    cX
    cme
    cfv
    wcel
    #
    @17
    cX
    wcel
    #
    @3
    cX
    wcel
    #
    @18
    cr
    wcel
    #
    wph
    @36
    @10
    @30
    wph
    cU
    ccphlo
    wcel
    #
    cU
    cnv
    wcel
    #
    @36
    minveco.u
    cU
    phnv
    #
    cD
    cU
    cX
    minveco.x
    minveco.d
    imsmet
    3syl
    ad2antrr
    #
    @31
    cY
    cX
    @17
    wph
    cY
    cX
    wss
    #
    @10
    @30
    wph
    @41
    cW
    cU
    css
    cfv
    #
    wcel
    @44
    wph
    @40
    @41
    minveco.u
    @42
    syl
    wph
    @45
    ccbn
    cin
    #
    @45
    cW
    @45
    ccbn
    inss1
    minveco.w
    sseldi
    cU
    @45
    cW
    cX
    cY
    minveco.x
    minveco.y
    @45
    eqid
    sspba
    syl2anc
    #
    ad2antrr
    #
    @31
    cn
    cY
    @15
    cF
    wph
    cn
    cY
    cF
    wf
    #
    @10
    @30
    minveco.f
    ad2antrr
    #
    @11
    @16
    @30
    @29
    adantr
    #
    ffvelrnd
    #
    sseldd
    #
    @31
    cY
    cX
    @3
    @48
    @31
    cn
    cY
    @2
    cF
    @50
    @11
    @16
    @30
    @2
    cn
    wcel
    #
    @29
    @2
    @15
    eluznn
    sylan
    #
    ffvelrnd
    sseldd
    #
    @17
    @3
    cD
    cX
    metcl
    syl3anc
    #
    resqcld
    @31
    @35
    @31
    @24
    @34
    crp
    wcel
    #
    @35
    crp
    wcel
    @26
    @31
    @15
    @31
    @15
    @51
    nnrpd
    #
    rpreccld
    c4
    @34
    rpmulcl
    sylancr
    rpred
    @31
    @12
    @11
    @25
    @30
    @27
    adantr
    #
    rpred
    #
    @31
    vy
    cA
    @34
    cD
    cR
    cS
    cU
    cJ
    @17
    @3
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
    @40
    @10
    @30
    minveco.u
    ad2antrr
    wph
    cW
    @46
    wcel
    @10
    @30
    minveco.w
    ad2antrr
    wph
    cA
    cX
    wcel
    #
    @10
    @30
    minveco.a
    ad2antrr
    #
    minveco.d
    minveco.j
    minveco.r
    minveco.s
    @31
    @34
    @11
    @58
    @30
    @11
    @15
    @11
    @15
    @29
    nnrpd
    rpreccld
    adantr
    #
    rpred
    #
    @31
    @34
    @64
    rpge0d
    @52
    @11
    @30
    @54
    @3
    cY
    wcel
    @55
    @11
    cn
    cY
    @2
    cF
    wph
    @49
    @10
    minveco.f
    adantr
    ffvelrnda
    syldan
    #
    @31
    @16
    cA
    @3
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
    cA
    @17
    cD
    co
    #
    c2
    cexp
    co
    #
    @69
    @34
    caddc
    co
    #
    cle
    wbr
    #
    @51
    wph
    @73
    @10
    @30
    wph
    @72
    vn
    cn
    minveco.1
    ralrimiva
    ad2antrr
    @72
    @77
    vn
    @15
    cn
    @2
    @15
    wceq
    #
    @68
    @75
    @71
    @76
    cle
    @78
    @67
    @74
    c2
    cexp
    @78
    @3
    @17
    cA
    cD
    @2
    @15
    cF
    fveq2
    oveq2d
    oveq1d
    @78
    @70
    @34
    @69
    caddc
    @2
    @15
    c1
    cdiv
    oveq2
    oveq2d
    breq12d
    rspcv
    sylc
    @31
    @68
    @71
    @76
    @31
    @67
    @31
    @36
    @62
    @38
    @67
    cr
    wcel
    @43
    @63
    @31
    cY
    cX
    @3
    @48
    @66
    sseldd
    cA
    @3
    cD
    cX
    metcl
    syl3anc
    resqcld
    @31
    @69
    @70
    wph
    @69
    cr
    wcel
    @10
    @30
    wph
    cS
    wph
    cS
    cR
    cr
    clt
    cinf
    #
    cr
    minveco.s
    wph
    cR
    cr
    wss
    #
    cR
    c0
    wne
    #
    cc0
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
    w3a
    @80
    @81
    @5
    @82
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
    w3a
    @79
    cr
    wcel
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
    @84
    @87
    @80
    @81
    cc0
    cr
    wcel
    @84
    @87
    0re
    @86
    @84
    vx
    cc0
    cr
    @5
    cc0
    wceq
    @85
    @83
    vw
    cR
    @5
    cc0
    @82
    cle
    breq1
    ralbidv
    rspcev
    mpan
    3anim3i
    vx
    vw
    cR
    infrecl
    3syl
    syl5eqel
    resqcld
    ad2antrr
    #
    @31
    @2
    @55
    nnrecred
    #
    readdcld
    @31
    @69
    @34
    @88
    @65
    readdcld
    @11
    @30
    @54
    @72
    @55
    wph
    @54
    @72
    @10
    minveco.1
    adantlr
    syldan
    @31
    @70
    @34
    @69
    @89
    @65
    @88
    @31
    @15
    @2
    cle
    wbr
    #
    @70
    @34
    cle
    wbr
    #
    @30
    @90
    @11
    @15
    @2
    eluzle
    adantl
    @31
    @15
    cr
    wcel
    cc0
    @15
    clt
    wbr
    wa
    @2
    cr
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    wa
    #
    @90
    @91
    wb
    @31
    @15
    @59
    rpregt0d
    @31
    @54
    @94
    @55
    @54
    @92
    @93
    @2
    nnre
    @2
    nngt0
    jca
    syl
    @15
    @2
    lerec
    syl2anc
    mpbid
    leadd2dd
    letrd
    minvecolem2
    @31
    @35
    @12
    clt
    wbr
    #
    @34
    @12
    c4
    cdiv
    co
    #
    clt
    wbr
    #
    @31
    @96
    @15
    @31
    @25
    @24
    @96
    crp
    wcel
    @60
    @26
    @12
    c4
    rpdivcl
    sylancl
    @59
    @31
    c1
    @96
    cdiv
    co
    #
    @13
    @15
    clt
    @31
    @12
    cc
    wcel
    @12
    cc0
    wne
    wa
    #
    c4
    cc
    wcel
    c4
    cc0
    wne
    wa
    #
    @98
    @13
    wceq
    @31
    @25
    @99
    @60
    @12
    rpcnne0
    syl
    @24
    @100
    @26
    c4
    rpcnne0
    ax-mp
    @12
    c4
    recdiv
    sylancl
    @31
    @23
    @13
    @15
    clt
    wbr
    @31
    @13
    @11
    @22
    @30
    @28
    adantr
    rpred
    @13
    flltp1
    syl
    eqbrtrd
    ltrec1d
    @31
    @34
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    @95
    @97
    wb
    #
    @65
    @61
    @101
    @102
    c4
    cr
    wcel
    #
    cc0
    c4
    clt
    wbr
    #
    wa
    @103
    @104
    @105
    4re
    4pos
    pm3.2i
    @34
    @12
    c4
    ltmuldiv2
    mp3an3
    syl2anc
    mpbird
    lelttrd
    @31
    @39
    cc0
    @18
    cle
    wbr
    #
    @5
    cr
    wcel
    cc0
    @5
    cle
    wbr
    wa
    #
    @19
    @33
    wb
    @57
    @31
    @36
    @37
    @38
    @106
    @43
    @53
    @56
    @17
    @3
    cD
    cX
    metge0
    syl3anc
    @10
    @107
    wph
    @30
    @5
    rprege0
    ad2antlr
    @18
    @5
    lt2sq
    syl21anc
    mpbird
    ralrimiva
    @8
    @21
    vj
    @15
    cn
    @0
    @15
    wceq
    #
    @6
    @19
    vn
    @7
    @20
    @0
    @15
    cuz
    fveq2
    @108
    @4
    @18
    @5
    clt
    @108
    @1
    @17
    @3
    cD
    @0
    @15
    cF
    fveq2
    oveq1d
    breq1d
    raleqbidv
    rspcev
    syl2anc
    ralrimiva
    wph
    vx
    @3
    @1
    cD
    vj
    vn
    cF
    c1
    cX
    cn
    nnuz
    wph
    @40
    @41
    cD
    cX
    cxmt
    cfv
    wcel
    minveco.u
    @42
    cD
    cU
    cX
    minveco.x
    minveco.d
    imsxmet
    3syl
    wph
    1zzd
    wph
    @54
    wa
    @3
    eqidd
    wph
    @0
    cn
    wcel
    wa
    @1
    eqidd
    wph
    cn
    cY
    cX
    cF
    minveco.f
    @47
    fssd
    iscauf
    mpbird
end
