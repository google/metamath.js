include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cnv.mm"
include "nvsf.mm"
include "ax-mp.mm"
include "c1.mm"
include "cfv.mm"
include "caddc.mm"
include "cdiv.mm"
include "1rp.mm"
include "cr.mm"
include "simpr.mm"
include "nvcl.mm"
include "sylancr.mm"
include "abscl.mm"
include "adantr.mm"
include "readdcld.mm"
include "cc0.mm"
include "cle.mm"
include "nvge0.mm"
include "absge0.mm"
include "addge0d.mm"
include "ge0p1rpd.mm"
include "rpdivcl.mm"
include "sylan.mm"
include "rpaddcl.mm"
include "rpreccld.mm"
include "syl5eqel.mm"
include "cme.mm"
include "imsmet.mm"
include "a1i.mm"
include "simplll.mm"
include "simpllr.mm"
include "nvscl.mm"
include "syl3anc.mm"
include "simprll.mm"
include "simprlr.mm"
include "metcl.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "mettri.mm"
include "syl13anc.mm"
include "cmul.mm"
include "abscld.mm"
include "peano2re.mm"
include "syl.mm"
include "rpred.mm"
include "remulcld.mm"
include "cnsb.mm"
include "subcld.mm"
include "eqid.mm"
include "nvmcl.mm"
include "abssubd.mm"
include "wceq.mm"
include "cnmetdval.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "simprrl.mm"
include "eqbrtrrd.mm"
include "ltled.mm"
include "eqbrtrd.mm"
include "lemul1ad.mm"
include "rpcnd.mm"
include "recnd.mm"
include "mulcomd.mm"
include "breqtrd.mm"
include "absge0d.mm"
include "pncan3d.mm"
include "fveq2d.mm"
include "abstrid.mm"
include "1red.mm"
include "1re.mm"
include "ltaddrp.mm"
include "recgt1d.mm"
include "mpbid.mm"
include "syl5eqbr.mm"
include "letrd.mm"
include "leadd2dd.mm"
include "imsdval.mm"
include "simprrr.mm"
include "lemul12ad.mm"
include "le2addd.mm"
include "cneg.mm"
include "cpv.mm"
include "imsdval2.mm"
include "neg1cn.mm"
include "mulcl.mm"
include "nvdir.mm"
include "mulm1d.mm"
include "oveq2d.mm"
include "negsubd.mm"
include "oveq1d.mm"
include "nvsass.mm"
include "3eqtr3d.mm"
include "nvs.mm"
include "3eqtr2d.mm"
include "nvmdi.mm"
include "oveq12d.mm"
include "1cnd.mm"
include "addassd.mm"
include "adddird.mm"
include "3brtr4d.mm"
include "rpne0d.mm"
include "divrecd.mm"
include "oveq2i.mm"
include "syl6reqr.mm"
include "simplr.mm"
include "ltp1d.mm"
include "addcomd.mm"
include "ltdiv23d.mm"
include "lelttrd.mm"
include "expr.mm"
include "ralrimivva.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "ralrimiva.mm"
include "rgen2.mm"
include "cxmt.mm"
include "wb.mm"
include "cnxmet.mm"
include "imsxmet.mm"
include "cnfldtopn.mm"
include "txmetcn.mm"
include "mp3an.mm"
include "mpbir2an.mm"

theorem smcnlem
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let cJ: class J
  let cK: class K
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  assume smcn.c: |- C = ( IndMet ` U )
  assume smcn.j: |- J = ( MetOpen ` C )
  assume smcn.s: |- S = ( .sOLD ` U )
  assume smcn.k: |- K = ( TopOpen ` CCfld )
  assume smcn.x: |- X = ( BaseSet ` U )
  assume smcn.n: |- N = ( normCV ` U )
  assume smcn.u: |- U e. NrmCVec
  assume smcn.t: |- T = ( 1 / ( 1 + ( ( ( ( N ` y ) + ( abs ` x ) ) + 1 ) / r ) ) )

  disjoint r x
  disjoint r y
  disjoint C r
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint U r
  disjoint U x
  disjoint U y
  disjoint K r
  disjoint K x
  disjoint K y
  disjoint S r
  disjoint S x
  disjoint S y
  disjoint X r
  disjoint X x
  disjoint X y
  disjoint r s
  disjoint r w
  disjoint r z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint J s
  disjoint J w
  disjoint J z
  disjoint T s
  disjoint T w
  disjoint T z
  disjoint K s
  disjoint K w
  disjoint K z
  disjoint S s
  disjoint S w
  disjoint S z
  disjoint X s
  disjoint X w
  disjoint X z
  assert |- S e. ( ( K tX J ) Cn J )

  proof
    cS
    cK
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    #
    cc
    cX
    cxp
    cX
    cS
    wf
    #
    vx
    cv
    #
    vz
    cv
    #
    cabs
    cmin
    ccom
    #
    co
    #
    vs
    cv
    #
    clt
    wbr
    #
    vy
    cv
    #
    vw
    cv
    #
    cC
    co
    #
    @6
    clt
    wbr
    #
    wa
    #
    @2
    @8
    cS
    co
    #
    @3
    @9
    cS
    co
    #
    cC
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cX
    wral
    vz
    cc
    wral
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    #
    vy
    cX
    wral
    vx
    cc
    wral
    #
    cU
    cnv
    wcel
    #
    @1
    smcn.u
    cS
    cU
    cX
    smcn.x
    smcn.s
    nvsf
    ax-mp
    @21
    vx
    vy
    cc
    cX
    @2
    cc
    wcel
    #
    @8
    cX
    wcel
    #
    wa
    #
    @20
    vr
    crp
    @26
    @16
    crp
    wcel
    #
    wa
    #
    cT
    crp
    wcel
    #
    @5
    cT
    clt
    wbr
    #
    @10
    cT
    clt
    wbr
    #
    wa
    #
    @17
    wi
    #
    vw
    cX
    wral
    vz
    cc
    wral
    #
    @20
    @28
    cT
    c1
    c1
    @8
    cN
    cfv
    #
    @2
    cabs
    cfv
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    @16
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    crp
    smcn.t
    @28
    @40
    @28
    c1
    crp
    wcel
    @39
    crp
    wcel
    #
    @40
    crp
    wcel
    #
    1rp
    @26
    @38
    crp
    wcel
    @27
    @42
    @26
    @37
    @26
    @35
    @36
    @26
    @23
    @25
    @35
    cr
    wcel
    #
    smcn.u
    @24
    @25
    simpr
    #
    @8
    cU
    cN
    cX
    smcn.x
    smcn.n
    nvcl
    #
    sylancr
    #
    @24
    @36
    cr
    wcel
    #
    @25
    @2
    abscl
    adantr
    #
    readdcld
    @26
    @35
    @36
    @47
    @49
    @26
    @23
    @25
    cc0
    @35
    cle
    wbr
    #
    smcn.u
    @45
    @8
    cU
    cN
    cX
    smcn.x
    smcn.n
    nvge0
    #
    sylancr
    @24
    cc0
    @36
    cle
    wbr
    @25
    @2
    absge0
    adantr
    addge0d
    ge0p1rpd
    @38
    @16
    rpdivcl
    sylan
    #
    c1
    @39
    rpaddcl
    sylancr
    #
    rpreccld
    syl5eqel
    #
    @28
    @33
    vz
    vw
    cc
    cX
    @28
    @3
    cc
    wcel
    #
    @9
    cX
    wcel
    #
    wa
    #
    @32
    @17
    @28
    @57
    @32
    wa
    #
    wa
    #
    @15
    @13
    @3
    @8
    cS
    co
    #
    cC
    co
    #
    @60
    @14
    cC
    co
    #
    caddc
    co
    #
    @16
    @59
    cC
    cX
    cme
    cfv
    wcel
    #
    @13
    cX
    wcel
    #
    @14
    cX
    wcel
    #
    @15
    cr
    wcel
    @64
    @59
    @23
    @64
    smcn.u
    cC
    cU
    cX
    smcn.x
    smcn.c
    imsmet
    ax-mp
    a1i
    #
    @59
    @23
    @24
    @25
    @65
    @23
    @59
    smcn.u
    a1i
    #
    @24
    @25
    @27
    @58
    simplll
    #
    @24
    @25
    @27
    @58
    simpllr
    #
    @2
    @8
    cS
    cU
    cX
    smcn.x
    smcn.s
    nvscl
    syl3anc
    #
    @59
    @23
    @55
    @56
    @66
    @68
    @28
    @55
    @56
    @32
    simprll
    #
    @28
    @55
    @56
    @32
    simprlr
    #
    @3
    @9
    cS
    cU
    cX
    smcn.x
    smcn.s
    nvscl
    syl3anc
    #
    @13
    @14
    cC
    cX
    metcl
    syl3anc
    @59
    @61
    @62
    @59
    @64
    @65
    @60
    cX
    wcel
    #
    @61
    cr
    wcel
    @67
    @71
    @59
    @23
    @55
    @25
    @75
    @68
    @72
    @70
    @3
    @8
    cS
    cU
    cX
    smcn.x
    smcn.s
    nvscl
    syl3anc
    #
    @13
    @60
    cC
    cX
    metcl
    syl3anc
    @59
    @64
    @75
    @66
    @62
    cr
    wcel
    @67
    @76
    @74
    @60
    @14
    cC
    cX
    metcl
    syl3anc
    readdcld
    #
    @27
    @16
    cr
    wcel
    @26
    @58
    @16
    rpre
    ad2antlr
    #
    @59
    @64
    @65
    @66
    @75
    @15
    @63
    cle
    wbr
    @67
    @71
    @74
    @76
    @13
    @14
    @60
    cC
    cX
    mettri
    syl13anc
    @59
    @63
    @38
    cT
    cmul
    co
    #
    @16
    @77
    @59
    @38
    cT
    @59
    @37
    cr
    wcel
    @38
    cr
    wcel
    @59
    @35
    @36
    @59
    @23
    @25
    @44
    smcn.u
    @70
    @46
    sylancr
    #
    @59
    @2
    @69
    abscld
    #
    readdcld
    @37
    peano2re
    syl
    #
    @59
    cT
    @28
    @29
    @58
    @54
    adantr
    #
    rpred
    #
    remulcld
    @78
    @59
    @2
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    @35
    cmul
    co
    #
    @3
    cabs
    cfv
    #
    @8
    @9
    cU
    cnsb
    cfv
    #
    co
    #
    cN
    cfv
    #
    cmul
    co
    #
    caddc
    co
    @35
    cT
    cmul
    co
    #
    @36
    c1
    caddc
    co
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    @63
    @79
    cle
    @59
    @87
    @92
    @93
    @95
    @59
    @86
    @35
    @59
    @85
    @59
    @2
    @3
    @69
    @72
    subcld
    #
    abscld
    #
    @80
    remulcld
    @59
    @88
    @91
    @59
    @3
    @72
    abscld
    #
    @59
    @23
    @90
    cX
    wcel
    #
    @91
    cr
    wcel
    smcn.u
    @59
    @23
    @25
    @56
    @100
    @68
    @70
    @73
    @8
    @9
    cU
    @89
    cX
    smcn.x
    @89
    eqid
    #
    nvmcl
    syl3anc
    #
    @90
    cU
    cN
    cX
    smcn.x
    smcn.n
    nvcl
    sylancr
    #
    remulcld
    @59
    @35
    cT
    @80
    @84
    remulcld
    @59
    @94
    cT
    @59
    @48
    @94
    cr
    wcel
    @81
    @36
    peano2re
    syl
    #
    @84
    remulcld
    @59
    @87
    cT
    @35
    cmul
    co
    @93
    cle
    @59
    @86
    cT
    @35
    @98
    @84
    @80
    @59
    @23
    @25
    @50
    smcn.u
    @70
    @51
    sylancr
    @59
    @86
    @3
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    cT
    cle
    @59
    @2
    @3
    @69
    @72
    abssubd
    #
    @59
    @106
    cT
    @59
    @105
    @59
    @3
    @2
    @72
    @69
    subcld
    #
    abscld
    #
    @84
    @59
    @5
    @106
    cT
    clt
    @59
    @5
    @86
    @106
    @59
    @24
    @55
    @5
    @86
    wceq
    @69
    @72
    @2
    @3
    @4
    @4
    eqid
    cnmetdval
    syl2anc
    @107
    eqtrd
    @28
    @57
    @30
    @31
    simprrl
    eqbrtrrd
    ltled
    #
    eqbrtrd
    lemul1ad
    @59
    cT
    @35
    @59
    cT
    @83
    rpcnd
    #
    @59
    @35
    @80
    recnd
    #
    mulcomd
    breqtrd
    @59
    @88
    @94
    @91
    cT
    @99
    @104
    @103
    @84
    @59
    @3
    @72
    absge0d
    @59
    @23
    @100
    cc0
    @91
    cle
    wbr
    smcn.u
    @102
    @90
    cU
    cN
    cX
    smcn.x
    smcn.n
    nvge0
    sylancr
    @59
    @88
    @36
    @106
    caddc
    co
    #
    @94
    @99
    @59
    @36
    @106
    @81
    @109
    readdcld
    @104
    @59
    @2
    @105
    caddc
    co
    #
    cabs
    cfv
    @88
    @113
    cle
    @59
    @114
    @3
    cabs
    @59
    @2
    @3
    @69
    @72
    pncan3d
    fveq2d
    @59
    @2
    @105
    @69
    @108
    abstrid
    eqbrtrrd
    @59
    @106
    c1
    @36
    @109
    @59
    1red
    #
    @81
    @59
    @106
    cT
    c1
    @109
    @84
    @115
    @110
    @59
    cT
    c1
    @84
    @115
    @59
    cT
    @41
    c1
    clt
    smcn.t
    @59
    c1
    @40
    clt
    wbr
    #
    @41
    c1
    clt
    wbr
    @59
    c1
    cr
    wcel
    @42
    @116
    1re
    @28
    @42
    @58
    @52
    adantr
    #
    c1
    @39
    ltaddrp
    sylancr
    @59
    @40
    @28
    @43
    @58
    @53
    adantr
    #
    recgt1d
    mpbid
    syl5eqbr
    ltled
    letrd
    leadd2dd
    letrd
    @59
    @91
    cT
    @103
    @84
    @59
    @10
    @91
    cT
    clt
    @59
    @23
    @25
    @56
    @10
    @91
    wceq
    @68
    @70
    @73
    @8
    @9
    cC
    cU
    @89
    cN
    cX
    smcn.x
    @101
    smcn.n
    smcn.c
    imsdval
    syl3anc
    @28
    @57
    @30
    @31
    simprrr
    eqbrtrrd
    ltled
    lemul12ad
    le2addd
    @59
    @61
    @87
    @62
    @92
    caddc
    @59
    @61
    @13
    c1
    cneg
    #
    @60
    cS
    co
    #
    cU
    cpv
    cfv
    #
    co
    #
    cN
    cfv
    #
    @85
    @8
    cS
    co
    #
    cN
    cfv
    #
    @87
    @59
    @23
    @65
    @75
    @61
    @123
    wceq
    @68
    @71
    @76
    @13
    @60
    cC
    cS
    cU
    @121
    cN
    cX
    smcn.x
    @121
    eqid
    #
    smcn.s
    smcn.n
    smcn.c
    imsdval2
    syl3anc
    @59
    @124
    @122
    cN
    @59
    @2
    @119
    @3
    cmul
    co
    #
    caddc
    co
    #
    @8
    cS
    co
    #
    @13
    @127
    @8
    cS
    co
    #
    @121
    co
    #
    @124
    @122
    @59
    @23
    @24
    @127
    cc
    wcel
    #
    @25
    @129
    @131
    wceq
    @68
    @69
    @59
    @119
    cc
    wcel
    #
    @55
    @132
    neg1cn
    @72
    @119
    @3
    mulcl
    sylancr
    @70
    @2
    @127
    @8
    cS
    cU
    @121
    cX
    smcn.x
    @126
    smcn.s
    nvdir
    syl13anc
    @59
    @128
    @85
    @8
    cS
    @59
    @128
    @2
    @3
    cneg
    #
    caddc
    co
    @85
    @59
    @127
    @134
    @2
    caddc
    @59
    @3
    @72
    mulm1d
    oveq2d
    @59
    @2
    @3
    @69
    @72
    negsubd
    eqtrd
    oveq1d
    @59
    @130
    @120
    @13
    @121
    @59
    @23
    @133
    @55
    @25
    @130
    @120
    wceq
    @68
    @133
    @59
    neg1cn
    a1i
    @72
    @70
    @119
    @3
    @8
    cS
    cU
    cX
    smcn.x
    smcn.s
    nvsass
    syl13anc
    oveq2d
    3eqtr3d
    fveq2d
    @59
    @23
    @85
    cc
    wcel
    @25
    @125
    @87
    wceq
    @68
    @97
    @70
    @85
    @8
    cS
    cU
    cN
    cX
    smcn.x
    smcn.s
    smcn.n
    nvs
    syl3anc
    3eqtr2d
    @59
    @62
    @60
    @14
    @89
    co
    #
    cN
    cfv
    #
    @3
    @90
    cS
    co
    #
    cN
    cfv
    #
    @92
    @59
    @23
    @75
    @66
    @62
    @136
    wceq
    @68
    @76
    @74
    @60
    @14
    cC
    cU
    @89
    cN
    cX
    smcn.x
    @101
    smcn.n
    smcn.c
    imsdval
    syl3anc
    @59
    @137
    @135
    cN
    @59
    @23
    @55
    @25
    @56
    @137
    @135
    wceq
    @68
    @72
    @70
    @73
    @3
    @8
    @9
    cS
    cU
    @89
    cX
    smcn.x
    @101
    smcn.s
    nvmdi
    syl13anc
    fveq2d
    @59
    @23
    @55
    @100
    @138
    @92
    wceq
    @68
    @72
    @102
    @3
    @90
    cS
    cU
    cN
    cX
    smcn.x
    smcn.s
    smcn.n
    nvs
    syl3anc
    3eqtr2d
    oveq12d
    @59
    @79
    @35
    @94
    caddc
    co
    #
    cT
    cmul
    co
    @96
    @59
    @38
    @139
    cT
    cmul
    @59
    @35
    @36
    c1
    @112
    @59
    @36
    @81
    recnd
    @59
    1cnd
    #
    addassd
    oveq1d
    @59
    @35
    @94
    cT
    @112
    @59
    @94
    @104
    recnd
    @111
    adddird
    eqtrd
    3brtr4d
    @59
    @79
    @38
    @40
    cdiv
    co
    #
    @16
    clt
    @59
    @141
    @38
    @41
    cmul
    co
    @79
    @59
    @38
    @40
    @59
    @38
    @82
    recnd
    @59
    @40
    @118
    rpcnd
    @59
    @40
    @118
    rpne0d
    divrecd
    cT
    @41
    @38
    cmul
    smcn.t
    oveq2i
    syl6reqr
    @59
    @38
    @16
    @40
    @82
    @26
    @27
    @58
    simplr
    @118
    @59
    @39
    @39
    c1
    caddc
    co
    @40
    clt
    @59
    @39
    @59
    @39
    @117
    rpred
    ltp1d
    @59
    @39
    c1
    @59
    @39
    @117
    rpcnd
    @140
    addcomd
    breqtrd
    ltdiv23d
    eqbrtrd
    lelttrd
    lelttrd
    expr
    ralrimivva
    @19
    @34
    vs
    cT
    crp
    @6
    cT
    wceq
    #
    @18
    @33
    vz
    vw
    cc
    cX
    @142
    @12
    @32
    @17
    @142
    @7
    @30
    @11
    @31
    @6
    cT
    @5
    clt
    breq2
    @6
    cT
    @10
    clt
    breq2
    anbi12d
    imbi1d
    2ralbidv
    rspcev
    syl2anc
    ralrimiva
    rgen2
    @4
    cc
    cxmt
    cfv
    wcel
    cC
    cX
    cxmt
    cfv
    wcel
    #
    @143
    @0
    @1
    @22
    wa
    wb
    cnxmet
    @23
    @143
    smcn.u
    cC
    cU
    cX
    smcn.x
    smcn.c
    imsxmet
    ax-mp
    #
    @144
    vx
    vy
    vr
    vs
    vw
    vz
    @4
    cC
    cC
    cS
    cK
    cJ
    cJ
    cc
    cX
    cX
    cK
    smcn.k
    cnfldtopn
    smcn.j
    smcn.j
    txmetcn
    mp3an
    mpbir2an
end
