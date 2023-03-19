include "cv.mm"
include "csb.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "wcel.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "wel.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "mpteq1.mm"
include "oveq2d.mm"
include "eleq2.mm"
include "ifbid.mm"
include "ifeq1d.mm"
include "mpt2eq3dv.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "weq.mm"
include "wa.mm"
include "wn.mm"
include "noel.mm"
include "iffalse.mm"
include "mp1i.mm"
include "mpt2eq3ia.mm"
include "fveq2i.mm"
include "eqid.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "syl.mm"
include "simpld.mm"
include "cxp.mm"
include "cmap.mm"
include "wf.mm"
include "matbas2i.mm"
include "elmapi.mm"
include "3syl.mm"
include "fovrnda.mm"
include "3impb.mm"
include "mdetr0.mm"
include "syl5eq.mm"
include "mpt0.mm"
include "oveq2i.mm"
include "gsum0.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "wss.mm"
include "cdif.mm"
include "cplusg.mm"
include "crg.mm"
include "ccmn.mm"
include "ccrg.mm"
include "adantr.mm"
include "crngring.mm"
include "ringcmn.mm"
include "simprl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "wral.mm"
include "sselda.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "rspcsbela.mm"
include "maduf.mm"
include "ffvelrnd.mm"
include "fovrnd.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "vex.mm"
include "a1i.mm"
include "eldifn.mm"
include "ad2antll.mm"
include "eldifi.mm"
include "csbeq1.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "gsumunsn.mm"
include "adantl.mm"
include "cur.mm"
include "w3a.mm"
include "wo.mm"
include "wb.mm"
include "elun.mm"
include "velsn.mm"
include "orbi2i.mm"
include "bitri.mm"
include "ifbi.mm"
include "ax-mp.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "elequ1.mm"
include "biimpac.mm"
include "nsyl.mm"
include "mndifsplit.mm"
include "ifeq1da.mm"
include "ovif2.mm"
include "ringridm.mm"
include "ringrz.mm"
include "ifeq12d.mm"
include "eqtr4d.mm"
include "eqtrd.mm"
include "mpt2eq3dva.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "ringidcl.mm"
include "mdetrlin2.mm"
include "mdetrsca2.mm"
include "maducoeval.mm"
include "3eqtrrd.mm"
include "3eqtrd.mm"
include "ex.mm"
include "findcard2d.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfov.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "nfv.mm"
include "nfif.mm"
include "eqeq1.mm"
include "oveq12.mm"
include "ifbieq12d.mm"
include "cbvmpt2.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "3eqtr4g.mm"

theorem madugsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  assume maduf.a: |- A = ( N Mat R )
  assume maduf.j: |- J = ( N maAdju R )
  assume maduf.b: |- B = ( Base ` A )
  assume madugsum.d: |- D = ( N maDet R )
  assume madugsum.t: |- .x. = ( .r ` R )
  assume madugsum.k: |- K = ( Base ` R )
  assume madugsum.m: |- ( ph -> M e. B )
  assume madugsum.r: |- ( ph -> R e. CRing )
  assume madugsum.x: |- ( ( ph /\ i e. N ) -> X e. K )
  assume madugsum.l: |- ( ph -> L e. N )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint B i
  disjoint B j
  disjoint i ph
  disjoint j ph
  disjoint J i
  disjoint K i
  disjoint K j
  disjoint M i
  disjoint M j
  disjoint X j
  disjoint .x. i
  disjoint L i
  disjoint L j
  disjoint N k
  disjoint N l
  disjoint N m
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint R k
  disjoint R l
  disjoint R m
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a i
  disjoint a j
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b i
  disjoint b j
  disjoint c d
  disjoint c e
  disjoint c i
  disjoint c j
  disjoint d e
  disjoint d i
  disjoint d j
  disjoint e i
  disjoint e j
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint J a
  disjoint J b
  disjoint J c
  disjoint J d
  disjoint J e
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K d
  disjoint K e
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint M d
  disjoint M e
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N d
  disjoint N e
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint R e
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X e
  disjoint L a
  disjoint L b
  disjoint L c
  disjoint L d
  disjoint L e
  disjoint .x. a
  disjoint .x. b
  disjoint .x. c
  disjoint .x. d
  disjoint .x. e
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  assert |- ( ph -> ( R gsum ( i e. N |-> ( X .x. ( i ( J ` M ) L ) ) ) ) = ( D ` ( j e. N , i e. N |-> if ( j = L , X , ( j M i ) ) ) ) )

  proof
    wph
    cR
    vb
    cN
    vi
    vb
    cv
    #
    cX
    csb
    #
    @0
    cL
    cM
    cJ
    cfv
    #
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    va
    vb
    cN
    cN
    va
    cv
    #
    cL
    wceq
    #
    @0
    cN
    wcel
    #
    @1
    cR
    c0g
    cfv
    #
    cif
    #
    @7
    @0
    cM
    co
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    cR
    vi
    cN
    cX
    vi
    cv
    #
    cL
    @2
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    vj
    vi
    cN
    cN
    vj
    cv
    #
    cL
    wceq
    #
    cX
    @20
    @16
    cM
    co
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    wph
    cR
    vb
    vc
    cv
    #
    @4
    cmpt
    #
    cgsu
    co
    #
    va
    vb
    cN
    cN
    @8
    vb
    vc
    wel
    #
    @1
    @10
    cif
    #
    @12
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    wceq
    cR
    vb
    c0
    @4
    cmpt
    #
    cgsu
    co
    #
    va
    vb
    cN
    cN
    @8
    @0
    c0
    wcel
    #
    @1
    @10
    cif
    #
    @12
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    wceq
    cR
    vb
    vd
    cv
    #
    @4
    cmpt
    #
    cgsu
    co
    #
    va
    vb
    cN
    cN
    @8
    vb
    vd
    wel
    #
    @1
    @10
    cif
    #
    @12
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    wceq
    #
    cR
    vb
    @40
    ve
    cv
    #
    csn
    #
    cun
    #
    @4
    cmpt
    #
    cgsu
    co
    #
    va
    vb
    cN
    cN
    @8
    @0
    @51
    wcel
    #
    @1
    @10
    cif
    #
    @12
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    wceq
    #
    @6
    @15
    wceq
    vc
    vd
    ve
    cN
    @25
    c0
    wceq
    #
    @27
    @34
    @32
    @39
    @60
    @26
    @33
    cR
    cgsu
    vb
    @25
    c0
    @4
    mpteq1
    oveq2d
    @60
    @31
    @38
    cD
    @60
    va
    vb
    cN
    cN
    @30
    @37
    @60
    @8
    @29
    @36
    @12
    @60
    @28
    @35
    @1
    @10
    @25
    c0
    @0
    eleq2
    ifbid
    ifeq1d
    mpt2eq3dv
    fveq2d
    eqeq12d
    vc
    vd
    weq
    #
    @27
    @42
    @32
    @47
    @61
    @26
    @41
    cR
    cgsu
    vb
    @25
    @40
    @4
    mpteq1
    oveq2d
    @61
    @31
    @46
    cD
    @61
    va
    vb
    cN
    cN
    @30
    @45
    @61
    @8
    @29
    @44
    @12
    @61
    @28
    @43
    @1
    @10
    @25
    @40
    @0
    eleq2
    ifbid
    ifeq1d
    mpt2eq3dv
    fveq2d
    eqeq12d
    @25
    @51
    wceq
    #
    @27
    @53
    @32
    @58
    @62
    @26
    @52
    cR
    cgsu
    vb
    @25
    @51
    @4
    mpteq1
    oveq2d
    @62
    @31
    @57
    cD
    @62
    va
    vb
    cN
    cN
    @30
    @56
    @62
    @8
    @29
    @55
    @12
    @62
    @28
    @54
    @1
    @10
    @25
    @51
    @0
    eleq2
    ifbid
    ifeq1d
    mpt2eq3dv
    fveq2d
    eqeq12d
    @25
    cN
    wceq
    #
    @27
    @6
    @32
    @15
    @63
    @26
    @5
    cR
    cgsu
    vb
    @25
    cN
    @4
    mpteq1
    oveq2d
    @63
    @31
    @14
    cD
    @63
    va
    vb
    cN
    cN
    @30
    @13
    @63
    @8
    @29
    @11
    @12
    @63
    @28
    @9
    @1
    @10
    @25
    cN
    @0
    eleq2
    ifbid
    ifeq1d
    mpt2eq3dv
    fveq2d
    eqeq12d
    wph
    @39
    @10
    @34
    wph
    @39
    va
    vb
    cN
    cN
    @8
    @10
    @12
    cif
    #
    cmpt2
    #
    cD
    cfv
    @10
    @38
    @65
    cD
    va
    vb
    cN
    cN
    @37
    @64
    @7
    cN
    wcel
    #
    @9
    wa
    #
    @8
    @36
    @10
    @12
    @35
    wn
    @36
    @10
    wceq
    @67
    @0
    noel
    @35
    @1
    @10
    iffalse
    mp1i
    ifeq1d
    mpt2eq3ia
    fveq2i
    wph
    cD
    cR
    va
    vb
    cL
    cK
    cN
    @12
    @10
    madugsum.d
    madugsum.k
    @10
    eqid
    #
    madugsum.r
    wph
    cN
    cfn
    wcel
    #
    cR
    cvv
    wcel
    #
    wph
    cM
    cB
    wcel
    #
    @69
    @70
    wa
    madugsum.m
    cA
    cB
    cR
    cN
    cM
    maduf.a
    maduf.b
    matrcl
    syl
    simpld
    #
    wph
    @66
    @9
    @12
    cK
    wcel
    #
    wph
    @7
    @0
    cK
    cN
    cN
    cM
    wph
    @71
    cM
    cK
    cN
    cN
    cxp
    #
    cmap
    co
    #
    wcel
    @74
    cK
    cM
    wf
    #
    madugsum.m
    cA
    cB
    cR
    cK
    cM
    cN
    maduf.a
    madugsum.k
    maduf.b
    matbas2i
    cM
    cK
    @74
    elmapi
    3syl
    #
    fovrnda
    3impb
    madugsum.l
    mdetr0
    syl5eq
    @34
    cR
    c0
    cgsu
    co
    @10
    @33
    c0
    cR
    cgsu
    vb
    @4
    mpt0
    oveq2i
    cR
    @10
    @68
    gsum0
    eqtri
    syl6reqr
    wph
    @40
    cN
    wss
    #
    @49
    cN
    @40
    cdif
    wcel
    #
    wa
    #
    wa
    #
    @48
    @59
    @81
    @48
    wa
    @53
    @42
    vi
    @49
    cX
    csb
    #
    @49
    cL
    @2
    co
    #
    c.x
    co
    #
    cR
    cplusg
    cfv
    #
    co
    #
    @47
    @84
    @85
    co
    #
    @58
    @81
    @53
    @86
    wceq
    @48
    @81
    @40
    cK
    @85
    vb
    cR
    @49
    cvv
    @4
    @84
    madugsum.k
    @85
    eqid
    #
    @81
    cR
    crg
    wcel
    #
    cR
    ccmn
    wcel
    @81
    cR
    ccrg
    wcel
    #
    @89
    wph
    @90
    @80
    madugsum.r
    adantr
    #
    cR
    crngring
    syl
    #
    cR
    ringcmn
    syl
    @81
    @69
    @78
    @40
    cfn
    wcel
    wph
    @69
    @80
    @72
    adantr
    #
    wph
    @78
    @79
    simprl
    #
    cN
    @40
    ssfi
    syl2anc
    @81
    @43
    wa
    #
    @89
    @1
    cK
    wcel
    #
    @3
    cK
    wcel
    @4
    cK
    wcel
    @81
    @89
    @43
    @92
    adantr
    @95
    @9
    cX
    cK
    wcel
    #
    vi
    cN
    wral
    #
    @96
    @81
    @40
    cN
    @0
    @94
    sselda
    #
    wph
    @98
    @80
    @43
    wph
    @97
    vi
    cN
    madugsum.x
    ralrimiva
    #
    ad2antrr
    vi
    @0
    cN
    cX
    cK
    rspcsbela
    #
    syl2anc
    @95
    @0
    cL
    cK
    cN
    cN
    @2
    wph
    @74
    cK
    @2
    wf
    #
    @80
    @43
    wph
    @2
    cB
    wcel
    @2
    @75
    wcel
    @102
    wph
    cB
    cB
    cM
    cJ
    wph
    @90
    cB
    cB
    cJ
    wf
    madugsum.r
    cA
    cB
    cR
    cJ
    cN
    maduf.a
    maduf.j
    maduf.b
    maduf
    syl
    madugsum.m
    ffvelrnd
    cA
    cB
    cR
    cK
    @2
    cN
    maduf.a
    madugsum.k
    maduf.b
    matbas2i
    @2
    cK
    @74
    elmapi
    3syl
    #
    ad2antrr
    @99
    wph
    cL
    cN
    wcel
    #
    @80
    @43
    madugsum.l
    ad2antrr
    fovrnd
    cK
    cR
    c.x
    @1
    @3
    madugsum.k
    madugsum.t
    ringcl
    syl3anc
    @49
    cvv
    wcel
    @81
    ve
    vex
    a1i
    @79
    ve
    vd
    wel
    #
    wn
    wph
    @78
    @49
    cN
    @40
    eldifn
    ad2antll
    #
    @81
    @89
    @82
    cK
    wcel
    #
    @83
    cK
    wcel
    @84
    cK
    wcel
    @92
    @81
    @49
    cN
    wcel
    #
    @98
    @107
    @79
    @108
    wph
    @78
    @49
    cN
    @40
    eldifi
    ad2antll
    #
    wph
    @98
    @80
    @100
    adantr
    #
    vi
    @49
    cN
    cX
    cK
    rspcsbela
    syl2anc
    #
    @81
    @49
    cL
    cK
    cN
    cN
    @2
    wph
    @102
    @80
    @103
    adantr
    @109
    wph
    @104
    @80
    madugsum.l
    adantr
    #
    fovrnd
    cK
    cR
    c.x
    @82
    @83
    madugsum.k
    madugsum.t
    ringcl
    syl3anc
    vb
    ve
    weq
    #
    @1
    @82
    @3
    @83
    c.x
    vi
    @0
    @49
    cX
    csbeq1
    #
    @0
    @49
    cL
    @2
    oveq1
    oveq12d
    gsumunsn
    adantr
    @48
    @86
    @87
    wceq
    @81
    @42
    @47
    @84
    @85
    oveq1
    adantl
    @81
    @87
    @58
    wceq
    @48
    @81
    @58
    va
    vb
    cN
    cN
    @8
    @44
    @82
    @113
    cR
    cur
    cfv
    #
    @10
    cif
    #
    c.x
    co
    #
    @85
    co
    #
    @12
    cif
    #
    cmpt2
    #
    cD
    cfv
    @47
    va
    vb
    cN
    cN
    @8
    @117
    @12
    cif
    cmpt2
    cD
    cfv
    #
    @85
    co
    @87
    @81
    @57
    @120
    cD
    @81
    va
    vb
    cN
    cN
    @56
    @119
    @81
    @66
    @9
    w3a
    #
    @8
    @55
    @118
    @12
    @122
    @55
    @44
    @113
    @1
    @10
    cif
    #
    @85
    co
    #
    @118
    @122
    @55
    @43
    @113
    wo
    #
    @1
    @10
    cif
    #
    @124
    @54
    @125
    wb
    @55
    @126
    wceq
    @54
    @43
    @0
    @50
    wcel
    #
    wo
    @125
    @0
    @40
    @50
    elun
    @127
    @113
    @43
    vb
    @49
    velsn
    orbi2i
    bitri
    @54
    @125
    @1
    @10
    ifbi
    ax-mp
    @122
    cR
    cmnd
    wcel
    #
    @96
    @43
    @113
    wa
    #
    wn
    #
    @126
    @124
    wceq
    @81
    @66
    @128
    @9
    @81
    @89
    @128
    @92
    cR
    ringmnd
    syl
    3ad2ant1
    @122
    @9
    @98
    @96
    @81
    @66
    @9
    simp3
    @81
    @66
    @98
    @9
    @110
    3ad2ant1
    @101
    syl2anc
    #
    @81
    @66
    @130
    @9
    @81
    @105
    @129
    @106
    @113
    @43
    @105
    vb
    ve
    vd
    elequ1
    biimpac
    nsyl
    3ad2ant1
    @43
    @113
    @1
    cK
    @85
    cR
    @10
    madugsum.k
    @68
    @88
    mndifsplit
    syl3anc
    syl5eq
    @81
    @66
    @124
    @118
    wceq
    @9
    @81
    @123
    @117
    @44
    @85
    @81
    @123
    @113
    @82
    @10
    cif
    #
    @117
    @81
    @113
    @1
    @82
    @10
    @113
    @1
    @82
    wceq
    @81
    @114
    adantl
    ifeq1da
    @81
    @117
    @113
    @82
    @115
    c.x
    co
    #
    @82
    @10
    c.x
    co
    #
    cif
    @132
    @113
    @82
    @115
    @10
    c.x
    ovif2
    @81
    @113
    @133
    @82
    @134
    @10
    @81
    @89
    @107
    @133
    @82
    wceq
    @92
    @111
    cK
    cR
    c.x
    @115
    @82
    madugsum.k
    madugsum.t
    @115
    eqid
    #
    ringridm
    syl2anc
    @81
    @89
    @107
    @134
    @10
    wceq
    @92
    @111
    cK
    cR
    c.x
    @82
    @10
    madugsum.k
    madugsum.t
    @68
    ringrz
    syl2anc
    ifeq12d
    syl5eq
    eqtr4d
    oveq2d
    3ad2ant1
    eqtrd
    ifeq1d
    mpt2eq3dva
    fveq2d
    @81
    cD
    @85
    cR
    va
    vb
    cL
    cK
    cN
    @44
    @117
    @12
    madugsum.d
    madugsum.k
    @88
    @91
    @93
    @122
    @43
    @1
    @10
    cK
    @131
    @81
    @66
    @10
    cK
    wcel
    #
    @9
    @81
    @89
    @136
    @92
    cK
    cR
    @10
    madugsum.k
    @68
    ring0cl
    syl
    #
    3ad2ant1
    ifcld
    @81
    @66
    @117
    cK
    wcel
    #
    @9
    @81
    @89
    @107
    @116
    cK
    wcel
    #
    @138
    @92
    @111
    @81
    @113
    @115
    @10
    cK
    @81
    @89
    @115
    cK
    wcel
    @92
    cK
    cR
    @115
    madugsum.k
    @135
    ringidcl
    syl
    @137
    ifcld
    #
    cK
    cR
    c.x
    @82
    @116
    madugsum.k
    madugsum.t
    ringcl
    syl3anc
    3ad2ant1
    @81
    @66
    @9
    @73
    @81
    @7
    @0
    cK
    cN
    cN
    cM
    wph
    @76
    @80
    @77
    adantr
    fovrnda
    3impb
    #
    @112
    mdetrlin2
    @81
    @121
    @84
    @47
    @85
    @81
    @121
    @82
    va
    vb
    cN
    cN
    @8
    @116
    @12
    cif
    cmpt2
    cD
    cfv
    #
    c.x
    co
    @84
    @81
    cD
    cR
    c.x
    va
    vb
    @82
    cL
    cK
    cN
    @116
    @12
    madugsum.d
    madugsum.k
    madugsum.t
    @91
    @93
    @81
    @66
    @139
    @9
    @140
    3ad2ant1
    @141
    @111
    @112
    mdetrsca2
    @81
    @83
    @142
    @82
    c.x
    @81
    @71
    @108
    @104
    @83
    @142
    wceq
    wph
    @71
    @80
    madugsum.m
    adantr
    @109
    @112
    cA
    cB
    cD
    cR
    @115
    va
    cL
    @49
    cJ
    cM
    cN
    @10
    vb
    maduf.a
    madugsum.d
    maduf.j
    maduf.b
    @135
    @68
    maducoeval
    syl3anc
    oveq2d
    eqtr4d
    oveq2d
    3eqtrrd
    adantr
    3eqtrd
    ex
    @72
    findcard2d
    @19
    @5
    cR
    cgsu
    vi
    vb
    cN
    @18
    @4
    vb
    @18
    nfcv
    vi
    @1
    @3
    c.x
    vi
    @0
    cX
    nfcsb1v
    #
    vi
    c.x
    nfcv
    vi
    @3
    nfcv
    nfov
    vi
    vb
    weq
    #
    cX
    @1
    @17
    @3
    c.x
    vi
    @0
    cX
    csbeq1a
    #
    @16
    @0
    cL
    @2
    oveq1
    oveq12d
    cbvmpt
    oveq2i
    @24
    @14
    cD
    @24
    va
    vb
    cN
    cN
    @8
    @1
    @12
    cif
    #
    cmpt2
    @14
    vj
    vi
    va
    vb
    cN
    cN
    @23
    @146
    va
    @23
    nfcv
    vb
    @23
    nfcv
    vj
    @146
    nfcv
    @8
    vi
    @1
    @12
    @8
    vi
    nfv
    @143
    vi
    @12
    nfcv
    nfif
    vj
    va
    weq
    #
    @144
    wa
    @21
    @8
    cX
    @22
    @1
    @12
    @147
    @21
    @8
    wb
    @144
    @20
    @7
    cL
    eqeq1
    adantr
    @144
    cX
    @1
    wceq
    @147
    @145
    adantl
    @20
    @7
    @16
    @0
    cM
    oveq12
    ifbieq12d
    cbvmpt2
    va
    vb
    cN
    cN
    @146
    @13
    @67
    @8
    @1
    @11
    @12
    @9
    @1
    @11
    wceq
    @66
    @9
    @11
    @1
    @9
    @1
    @10
    iftrue
    eqcomd
    adantl
    ifeq1d
    mpt2eq3ia
    eqtri
    fveq2i
    3eqtr4g
end
