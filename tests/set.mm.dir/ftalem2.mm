include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "wi.mm"
include "cc.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cc0.mm"
include "crp.mm"
include "c1.mm"
include "cfz.mm"
include "csu.mm"
include "cn0.mm"
include "cply.mm"
include "wcel.mm"
include "wf.mm"
include "coef3.mm"
include "syl.mm"
include "nnnn0d.mm"
include "ffvelrnd.mm"
include "wne.mm"
include "nnne0d.mm"
include "wceq.mm"
include "c0p.mm"
include "dgreq0.mm"
include "cdgr.mm"
include "fveq2.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "syl6bir.mm"
include "necon3d.mm"
include "mpd.mm"
include "absrpcld.mm"
include "rphalfcld.mm"
include "fveq2d.mm"
include "cbvsumv.mm"
include "oveq1i.mm"
include "ftalem1.mm"
include "wa.mm"
include "cle.mm"
include "cif.mm"
include "plyf.mm"
include "0cn.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "abscld.mm"
include "rerpdivcld.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "simpr.mm"
include "1re.mm"
include "ifcl.mm"
include "ifcld.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "max1.mm"
include "sylancr.mm"
include "syl2anc.mm"
include "syl6breqr.mm"
include "letrd.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "max2.mm"
include "abscl.mm"
include "adantl.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "imim1d.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "expcld.mm"
include "mulcld.mm"
include "subcld.mm"
include "rehalfcld.mm"
include "ltsub2d.mm"
include "absmuld.mm"
include "absexpd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "recnd.mm"
include "adantrr.mm"
include "reexpcld.mm"
include "2cnd.mm"
include "2ne0.mm"
include "div23d.mm"
include "breq2d.mm"
include "caddc.mm"
include "2halvesd.mm"
include "pncand.mm"
include "eqtr3d.mm"
include "breq1d.mm"
include "3bitr3d.mm"
include "abs2difd.mm"
include "abssubd.mm"
include "nncand.mm"
include "3brtr3d.mm"
include "resubcld.mm"
include "ltletr.mm"
include "mpan2d.mm"
include "sylbid.mm"
include "rpred.mm"
include "remulcld.mm"
include "eqeltrrd.mm"
include "simprr.mm"
include "lelttrd.mm"
include "syl5eqbrr.mm"
include "ltdivmuld.mm"
include "mpbid.mm"
include "exp1d.mm"
include "ltled.mm"
include "cn.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "leexp2ad.mm"
include "eqbrtrrd.mm"
include "lemul2d.mm"
include "breqtrrd.mm"
include "lttr.mm"
include "syld.mm"
include "expr.mm"
include "a2d.mm"
include "ralimdva.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"

theorem ftalem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cN: class N
  let vs: setvar s
  let vr: setvar r
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let cD: class D
  let cE: class E
  let cK: class K
  let vw: setvar w
  let vy: setvar y
  let cJ: class J
  let cR: class R
  let cX: class X
  assume ftalem.1: |- A = ( coeff ` F )
  assume ftalem.2: |- N = ( deg ` F )
  assume ftalem.3: |- ( ph -> F e. ( Poly ` S ) )
  assume ftalem.4: |- ( ph -> N e. NN )
  assume ftalem2.5: |- U = if ( if ( 1 <_ s , s , 1 ) <_ T , T , if ( 1 <_ s , s , 1 ) )
  assume ftalem2.6: |- T = ( ( abs ` ( F ` 0 ) ) / ( ( abs ` ( A ` N ) ) / 2 ) )

  disjoint r s
  disjoint r x
  disjoint A r
  disjoint s x
  disjoint A s
  disjoint A x
  disjoint N r
  disjoint N s
  disjoint N x
  disjoint F r
  disjoint F s
  disjoint F x
  disjoint ph s
  disjoint ph x
  disjoint S s
  disjoint T r
  disjoint T x
  disjoint U r
  disjoint U x
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k x
  disjoint A k
  disjoint n r
  disjoint n s
  disjoint n x
  disjoint A n
  disjoint s z
  disjoint D s
  disjoint x z
  disjoint D x
  disjoint D z
  disjoint E r
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint s w
  disjoint s y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J s
  disjoint J x
  disjoint J z
  disjoint k ph
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint S k
  disjoint T k
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X s
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> E. r e. RR+ A. x e. CC ( r < ( abs ` x ) -> ( abs ` ( F ` 0 ) ) < ( abs ` ( F ` x ) ) ) )

  proof
    wph
    vs
    cv
    #
    vx
    cv
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    @1
    cF
    cfv
    #
    cN
    cA
    cfv
    #
    @1
    cN
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @5
    cabs
    cfv
    #
    c2
    cdiv
    co
    #
    @2
    cN
    cexp
    co
    #
    cmul
    co
    #
    clt
    wbr
    #
    wi
    #
    vx
    cc
    wral
    #
    vs
    cr
    wrex
    vr
    cv
    #
    @2
    clt
    wbr
    #
    cc0
    cF
    cfv
    #
    cabs
    cfv
    #
    @4
    cabs
    cfv
    #
    clt
    wbr
    #
    wi
    #
    vx
    cc
    wral
    #
    vr
    crp
    wrex
    #
    wph
    vx
    cA
    cS
    cc0
    cN
    c1
    cmin
    co
    cfz
    co
    #
    vn
    cv
    #
    cA
    cfv
    #
    cabs
    cfv
    #
    vn
    csu
    #
    @11
    cdiv
    co
    vk
    @11
    cF
    cN
    vs
    ftalem.1
    ftalem.2
    ftalem.3
    ftalem.4
    wph
    @10
    wph
    @5
    wph
    cn0
    cc
    cN
    cA
    wph
    cF
    cS
    cply
    cfv
    wcel
    #
    cn0
    cc
    cA
    wf
    ftalem.3
    cA
    cS
    cF
    ftalem.1
    coef3
    syl
    wph
    cN
    ftalem.4
    nnnn0d
    #
    ffvelrnd
    #
    wph
    cN
    cc0
    wne
    @5
    cc0
    wne
    wph
    cN
    ftalem.4
    nnne0d
    wph
    @5
    cc0
    cN
    cc0
    wph
    @31
    @5
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wi
    ftalem.3
    @31
    @34
    cF
    c0p
    wceq
    #
    @35
    cA
    cS
    cF
    cN
    ftalem.2
    ftalem.1
    dgreq0
    @36
    cN
    cF
    cdgr
    cfv
    #
    cc0
    ftalem.2
    @36
    @37
    c0p
    cdgr
    cfv
    cc0
    cF
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    syl5eq
    syl6bir
    syl
    necon3d
    mpd
    absrpcld
    rphalfcld
    #
    @30
    @26
    vk
    cv
    #
    cA
    cfv
    #
    cabs
    cfv
    #
    vk
    csu
    @11
    cdiv
    @26
    @29
    @41
    vn
    vk
    @27
    @39
    wceq
    @28
    @40
    cabs
    @27
    @39
    cA
    fveq2
    fveq2d
    cbvsumv
    oveq1i
    ftalem1
    wph
    @16
    @25
    vs
    cr
    wph
    @0
    cr
    wcel
    #
    wa
    #
    cU
    crp
    wcel
    @16
    cU
    @2
    clt
    wbr
    #
    @22
    wi
    #
    vx
    cc
    wral
    #
    @25
    @43
    cU
    @43
    cU
    c1
    @0
    cle
    wbr
    #
    @0
    c1
    cif
    #
    cT
    cle
    wbr
    #
    cT
    @48
    cif
    #
    cr
    ftalem2.5
    @43
    @49
    cT
    @48
    cr
    wph
    cT
    cr
    wcel
    #
    @42
    wph
    cT
    @20
    @11
    cdiv
    co
    #
    cr
    ftalem2.6
    wph
    @20
    @11
    wph
    @19
    wph
    cc
    cc
    cF
    wf
    #
    cc0
    cc
    wcel
    @19
    cc
    wcel
    wph
    @31
    @53
    ftalem.3
    cS
    cF
    plyf
    syl
    #
    0cn
    cc
    cc
    cc0
    cF
    ffvelrn
    sylancl
    abscld
    #
    @38
    rerpdivcld
    syl5eqel
    adantr
    #
    @43
    @42
    c1
    cr
    wcel
    #
    @48
    cr
    wcel
    #
    wph
    @42
    simpr
    #
    1re
    @47
    @0
    c1
    cr
    ifcl
    sylancl
    #
    ifcld
    syl5eqel
    #
    @43
    cc0
    c1
    cU
    @43
    0red
    @43
    1red
    #
    @61
    cc0
    c1
    clt
    wbr
    @43
    0lt1
    a1i
    @43
    c1
    @48
    cU
    @62
    @60
    @61
    @43
    @57
    @42
    c1
    @48
    cle
    wbr
    1re
    @59
    c1
    @0
    max1
    sylancr
    @43
    @48
    @50
    cU
    cle
    @43
    @58
    @51
    @48
    @50
    cle
    wbr
    @60
    @56
    @48
    cT
    max1
    syl2anc
    ftalem2.5
    syl6breqr
    #
    letrd
    #
    ltletrd
    elrpd
    @43
    @15
    @45
    vx
    cc
    @43
    @1
    cc
    wcel
    #
    wa
    #
    @15
    @44
    @14
    wi
    @45
    @66
    @44
    @3
    @14
    @66
    @0
    cU
    cle
    wbr
    #
    @44
    @3
    @43
    @67
    @65
    @43
    @0
    @48
    cU
    @59
    @60
    @61
    @43
    @57
    @42
    @0
    @48
    cle
    wbr
    1re
    @59
    c1
    @0
    max2
    sylancr
    @63
    letrd
    adantr
    @66
    @42
    cU
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @67
    @44
    wa
    @3
    wi
    @43
    @42
    @65
    @59
    adantr
    @43
    @68
    @65
    @61
    adantr
    @65
    @69
    @43
    @1
    abscl
    adantl
    #
    @0
    cU
    @2
    lelttr
    syl3anc
    mpand
    imim1d
    @66
    @44
    @14
    @22
    @43
    @65
    @44
    @14
    @22
    wi
    @43
    @65
    @44
    wa
    #
    wa
    #
    @14
    @7
    cabs
    cfv
    #
    c2
    cdiv
    co
    #
    @21
    clt
    wbr
    #
    @22
    @72
    @14
    @74
    @73
    @9
    cmin
    co
    #
    clt
    wbr
    #
    @75
    @72
    @9
    @74
    clt
    wbr
    @73
    @74
    cmin
    co
    #
    @76
    clt
    wbr
    @14
    @77
    @72
    @9
    @74
    @73
    @72
    @8
    @72
    @4
    @7
    @72
    cc
    cc
    @1
    cF
    wph
    @53
    @42
    @71
    @54
    ad2antrr
    @43
    @65
    @44
    simprl
    #
    ffvelrnd
    #
    @72
    @5
    @6
    wph
    @5
    cc
    wcel
    @42
    @71
    @33
    ad2antrr
    #
    @72
    @1
    cN
    @79
    wph
    cN
    cn0
    wcel
    @42
    @71
    @32
    ad2antrr
    #
    expcld
    #
    mulcld
    #
    subcld
    abscld
    #
    @72
    @73
    @72
    @7
    @84
    abscld
    #
    rehalfcld
    #
    @86
    ltsub2d
    @72
    @74
    @13
    @9
    clt
    @72
    @74
    @10
    @12
    cmul
    co
    #
    c2
    cdiv
    co
    @13
    @72
    @73
    @88
    c2
    cdiv
    @72
    @73
    @10
    @6
    cabs
    cfv
    #
    cmul
    co
    @88
    @72
    @5
    @6
    @81
    @83
    absmuld
    @72
    @89
    @12
    @10
    cmul
    @72
    @1
    cN
    @79
    @82
    absexpd
    oveq2d
    eqtrd
    oveq1d
    @72
    @10
    @12
    c2
    @72
    @10
    @72
    @5
    @81
    abscld
    recnd
    @72
    @12
    @72
    @2
    cN
    @43
    @65
    @69
    @44
    @70
    adantrr
    #
    @82
    reexpcld
    #
    recnd
    @72
    2cnd
    c2
    cc0
    wne
    @72
    2ne0
    a1i
    div23d
    eqtrd
    #
    breq2d
    @72
    @78
    @74
    @76
    clt
    @72
    @74
    @74
    caddc
    co
    #
    @74
    cmin
    co
    @78
    @74
    @72
    @93
    @73
    @74
    cmin
    @72
    @73
    @72
    @73
    @86
    recnd
    2halvesd
    oveq1d
    @72
    @74
    @74
    @72
    @74
    @87
    recnd
    #
    @94
    pncand
    eqtr3d
    breq1d
    3bitr3d
    @72
    @77
    @76
    @21
    cle
    wbr
    #
    @75
    @72
    @73
    @7
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    cmin
    co
    @7
    @96
    cmin
    co
    #
    cabs
    cfv
    @76
    @21
    cle
    @72
    @7
    @96
    @84
    @72
    @7
    @4
    @84
    @80
    subcld
    abs2difd
    @72
    @97
    @9
    @73
    cmin
    @72
    @7
    @4
    @84
    @80
    abssubd
    oveq2d
    @72
    @98
    @4
    cabs
    @72
    @7
    @4
    @84
    @80
    nncand
    fveq2d
    3brtr3d
    @72
    @74
    cr
    wcel
    #
    @76
    cr
    wcel
    @21
    cr
    wcel
    #
    @77
    @95
    wa
    @75
    wi
    @87
    @72
    @73
    @9
    @86
    @85
    resubcld
    @72
    @4
    @80
    abscld
    #
    @74
    @76
    @21
    ltletr
    syl3anc
    mpan2d
    sylbid
    @72
    @20
    @74
    clt
    wbr
    #
    @75
    @22
    @72
    @20
    @13
    @74
    clt
    @72
    @20
    @11
    @2
    cmul
    co
    #
    @13
    wph
    @20
    cr
    wcel
    #
    @42
    @71
    @55
    ad2antrr
    #
    @72
    @11
    @2
    @72
    @11
    wph
    @11
    crp
    wcel
    @42
    @71
    @38
    ad2antrr
    #
    rpred
    @90
    remulcld
    @72
    @74
    @13
    cr
    @92
    @87
    eqeltrrd
    @72
    @52
    @2
    clt
    wbr
    @20
    @103
    clt
    wbr
    @72
    @52
    cT
    @2
    clt
    ftalem2.6
    @72
    cT
    cU
    @2
    @43
    @51
    @71
    @56
    adantr
    @43
    @68
    @71
    @61
    adantr
    #
    @90
    @43
    cT
    cU
    cle
    wbr
    @71
    @43
    cT
    @50
    cU
    cle
    @43
    @58
    @51
    cT
    @50
    cle
    wbr
    @60
    @56
    @48
    cT
    max2
    syl2anc
    ftalem2.5
    syl6breqr
    adantr
    @43
    @65
    @44
    simprr
    #
    lelttrd
    syl5eqbrr
    @72
    @20
    @2
    @11
    @105
    @90
    @106
    ltdivmuld
    mpbid
    @72
    @2
    @12
    cle
    wbr
    @103
    @13
    cle
    wbr
    @72
    @2
    c1
    cexp
    co
    @2
    @12
    cle
    @72
    @2
    @72
    @2
    @90
    recnd
    exp1d
    @72
    @2
    c1
    cN
    @90
    @72
    c1
    @2
    @72
    1red
    #
    @90
    @72
    c1
    cU
    @2
    @109
    @107
    @90
    @43
    c1
    cU
    cle
    wbr
    @71
    @64
    adantr
    @108
    lelttrd
    ltled
    @72
    cN
    cn
    c1
    cuz
    cfv
    wph
    cN
    cn
    wcel
    @42
    @71
    ftalem.4
    ad2antrr
    nnuz
    syl6eleq
    leexp2ad
    eqbrtrrd
    @72
    @2
    @12
    @11
    @90
    @91
    @106
    lemul2d
    mpbid
    ltletrd
    @92
    breqtrrd
    @72
    @104
    @99
    @100
    @102
    @75
    wa
    @22
    wi
    @105
    @87
    @101
    @20
    @74
    @21
    lttr
    syl3anc
    mpand
    syld
    expr
    a2d
    syld
    ralimdva
    @24
    @46
    vr
    cU
    crp
    @17
    cU
    wceq
    #
    @23
    @45
    vx
    cc
    @110
    @18
    @44
    @22
    @17
    cU
    @2
    clt
    breq1
    imbi1d
    ralbidv
    rspcev
    syl6an
    rexlimdva
    mpd
end
