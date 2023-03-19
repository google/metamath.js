include "cfv.mm"
include "crn.mm"
include "cun.mm"
include "cv.mm"
include "wss.mm"
include "cotp.mm"
include "wcel.mm"
include "cima.mm"
include "wbr.mm"
include "cxp.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "co.mm"
include "abid.mm"
include "intss1.mm"
include "sylbir.mm"
include "mclsval.mm"
include "sseq1d.mm"
include "syl5ibr.mm"
include "sstr2.mm"
include "com12.mm"
include "anim1d.mm"
include "imim1d.mm"
include "ralimdv.mm"
include "imim2d.mm"
include "alimdv.mm"
include "2alimdv.mm"
include "adantl.mm"
include "sylcom.mm"
include "cmpst.mm"
include "cvv.mm"
include "w3a.mm"
include "cmsta.mm"
include "eqid.mm"
include "mstapst.mm"
include "cmfs.mm"
include "maxsta.mm"
include "syl.mm"
include "sseldd.mm"
include "sseldi.mm"
include "mpstrcl.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "oteq123d.mm"
include "eleq1d.mm"
include "uneq1d.mm"
include "imaeq2d.mm"
include "breqd.mm"
include "imbi1d.mm"
include "2albidv.mm"
include "anbi12d.mm"
include "fveq2d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "spc3gv.mm"
include "3syl.mm"
include "wo.mm"
include "elun.mm"
include "ralrimiva.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "mvhf.mm"
include "ffn.mm"
include "fveq2.mm"
include "ralrn.mm"
include "mpbird.mm"
include "r19.21bi.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "wfun.mm"
include "cdm.mm"
include "msubf.mm"
include "ffun.mm"
include "cfn.mm"
include "ccnv.mm"
include "elmpst.mm"
include "sylib.mm"
include "simp2d.mm"
include "simpld.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "frn.mm"
include "unssd.mm"
include "funimass4.mm"
include "syl2anc.mm"
include "3exp2.mm"
include "imp4b.mm"
include "ralrimivv.mm"
include "dfss3.mm"
include "cop.mm"
include "eleq1.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "ralxp.mm"
include "bitri.mm"
include "sylibr.mm"
include "ex.mm"
include "alrimivv.mm"
include "jca.mm"
include "imaeq1.mm"
include "fveq1.mm"
include "xpeq12d.mm"
include "imbi2d.mm"
include "rspcv.mm"
include "mpid.mm"
include "embantd.mm"
include "3syld.mm"
include "alrimiv.mm"
include "fvex.mm"
include "elintab.mm"
include "eleqtrrd.mm"

theorem mclsax
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let cE: class E
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vh: setvar h
  let vt: setvar t
  let vc: setvar c
  let vm: setvar m
  let vo: setvar o
  let vp: setvar p
  let vs: setvar s
  let vz: setvar z
  let cQ: class Q
  let cX: class X
  let cY: class Y
  assume mclsval.d: |- D = ( mDV ` T )
  assume mclsval.e: |- E = ( mEx ` T )
  assume mclsval.c: |- C = ( mCls ` T )
  assume mclsval.1: |- ( ph -> T e. mFS )
  assume mclsval.2: |- ( ph -> K C_ D )
  assume mclsval.3: |- ( ph -> B C_ E )
  assume mclsax.a: |- A = ( mAx ` T )
  assume mclsax.l: |- L = ( mSubst ` T )
  assume mclsax.v: |- V = ( mVR ` T )
  assume mclsax.h: |- H = ( mVH ` T )
  assume mclsax.w: |- W = ( mVars ` T )
  assume mclsax.4: |- ( ph -> <. M , O , P >. e. A )
  assume mclsax.5: |- ( ph -> S e. ran L )
  assume mclsax.6: |- ( ( ph /\ x e. O ) -> ( S ` x ) e. ( K C B ) )
  assume mclsax.7: |- ( ( ph /\ v e. V ) -> ( S ` ( H ` v ) ) e. ( K C B ) )
  assume mclsax.8: |- ( ( ph /\ ( x M y /\ a e. ( W ` ( S ` ( H ` x ) ) ) /\ b e. ( W ` ( S ` ( H ` y ) ) ) ) ) -> a K b )

  disjoint E v
  disjoint a b
  disjoint a v
  disjoint a x
  disjoint H a
  disjoint b v
  disjoint b x
  disjoint H b
  disjoint v x
  disjoint H v
  disjoint H x
  disjoint v y
  disjoint B v
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C v
  disjoint C x
  disjoint L x
  disjoint L y
  disjoint O x
  disjoint O y
  disjoint a y
  disjoint S a
  disjoint b y
  disjoint S b
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint M a
  disjoint M b
  disjoint M x
  disjoint M y
  disjoint P x
  disjoint P y
  disjoint T x
  disjoint T y
  disjoint a ph
  disjoint b ph
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint V v
  disjoint V x
  disjoint W a
  disjoint W b
  disjoint W x
  disjoint K a
  disjoint K b
  disjoint K v
  disjoint K x
  disjoint K y
  disjoint d h
  disjoint d t
  disjoint D d
  disjoint h t
  disjoint D h
  disjoint D t
  disjoint c d
  disjoint c h
  disjoint c m
  disjoint c o
  disjoint c p
  disjoint c s
  disjoint c t
  disjoint c v
  disjoint E c
  disjoint d m
  disjoint d o
  disjoint d p
  disjoint d s
  disjoint d v
  disjoint E d
  disjoint h m
  disjoint h o
  disjoint h p
  disjoint h s
  disjoint h v
  disjoint E h
  disjoint m o
  disjoint m p
  disjoint m s
  disjoint m t
  disjoint m v
  disjoint E m
  disjoint o p
  disjoint o s
  disjoint o t
  disjoint o v
  disjoint E o
  disjoint p s
  disjoint p t
  disjoint p v
  disjoint E p
  disjoint s t
  disjoint s v
  disjoint E s
  disjoint t v
  disjoint E t
  disjoint a c
  disjoint a d
  disjoint a h
  disjoint a m
  disjoint a o
  disjoint a p
  disjoint a s
  disjoint a t
  disjoint a z
  disjoint b c
  disjoint b d
  disjoint b h
  disjoint b m
  disjoint b o
  disjoint b p
  disjoint b s
  disjoint b t
  disjoint b z
  disjoint c x
  disjoint c z
  disjoint H c
  disjoint d x
  disjoint d z
  disjoint H d
  disjoint h x
  disjoint h z
  disjoint H h
  disjoint m x
  disjoint m z
  disjoint H m
  disjoint o x
  disjoint o z
  disjoint H o
  disjoint p x
  disjoint p z
  disjoint H p
  disjoint s x
  disjoint s z
  disjoint H s
  disjoint t x
  disjoint t z
  disjoint H t
  disjoint v z
  disjoint x z
  disjoint H z
  disjoint c y
  disjoint B c
  disjoint d y
  disjoint B d
  disjoint h y
  disjoint B h
  disjoint m y
  disjoint B m
  disjoint o y
  disjoint B o
  disjoint p y
  disjoint B p
  disjoint s y
  disjoint B s
  disjoint t y
  disjoint B t
  disjoint C m
  disjoint C o
  disjoint C p
  disjoint C s
  disjoint C t
  disjoint L c
  disjoint L m
  disjoint L o
  disjoint L p
  disjoint L s
  disjoint A c
  disjoint A d
  disjoint A h
  disjoint A m
  disjoint A o
  disjoint A p
  disjoint A s
  disjoint A t
  disjoint O m
  disjoint O o
  disjoint O p
  disjoint O s
  disjoint S c
  disjoint S d
  disjoint S h
  disjoint S s
  disjoint S t
  disjoint y z
  disjoint S z
  disjoint M m
  disjoint M o
  disjoint M p
  disjoint M s
  disjoint P c
  disjoint P m
  disjoint P o
  disjoint P p
  disjoint P s
  disjoint T c
  disjoint T d
  disjoint T h
  disjoint T m
  disjoint T o
  disjoint T p
  disjoint T s
  disjoint T t
  disjoint c ph
  disjoint d ph
  disjoint h ph
  disjoint m ph
  disjoint o ph
  disjoint p ph
  disjoint ph s
  disjoint Q c
  disjoint Q m
  disjoint Q o
  disjoint Q p
  disjoint Q s
  disjoint Q v
  disjoint V c
  disjoint V d
  disjoint V h
  disjoint V t
  disjoint W c
  disjoint W m
  disjoint W o
  disjoint W p
  disjoint W s
  disjoint W z
  disjoint X c
  disjoint X m
  disjoint X o
  disjoint X p
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint Y c
  disjoint Y m
  disjoint Y o
  disjoint Y p
  disjoint Y s
  disjoint Y x
  disjoint Y y
  disjoint K c
  disjoint K d
  disjoint K h
  disjoint K m
  disjoint K o
  disjoint K p
  disjoint K s
  disjoint K t
  disjoint K z
  assert |- ( ph -> ( S ` P ) e. ( K C B ) )

  proof
    wph
    cP
    cS
    cfv
    #
    cB
    cH
    crn
    #
    cun
    vc
    cv
    #
    wss
    #
    vm
    cv
    #
    vo
    cv
    #
    vp
    cv
    #
    cotp
    #
    cA
    wcel
    #
    vs
    cv
    #
    @5
    @1
    cun
    #
    cima
    #
    @2
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    @4
    wbr
    #
    @13
    cH
    cfv
    #
    @9
    cfv
    #
    cW
    cfv
    #
    @14
    cH
    cfv
    #
    @9
    cfv
    #
    cW
    cfv
    #
    cxp
    #
    cK
    wss
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    wa
    #
    @6
    @9
    cfv
    #
    @2
    wcel
    #
    wi
    #
    vs
    cL
    crn
    #
    wral
    #
    wi
    #
    vp
    wal
    #
    vo
    wal
    vm
    wal
    #
    wa
    #
    vc
    cab
    #
    cint
    #
    cK
    cB
    cC
    co
    #
    wph
    @35
    @0
    @2
    wcel
    #
    wi
    #
    vc
    wal
    @0
    @37
    wcel
    wph
    @40
    vc
    wph
    @35
    @8
    @11
    @38
    wss
    #
    @25
    wa
    #
    @28
    wi
    #
    vs
    @30
    wral
    #
    wi
    #
    vp
    wal
    #
    vo
    wal
    vm
    wal
    #
    cM
    cO
    cP
    cotp
    #
    cA
    wcel
    #
    @9
    cO
    @1
    cun
    #
    cima
    #
    @38
    wss
    #
    @13
    @14
    cM
    wbr
    #
    @23
    wi
    #
    vy
    wal
    vx
    wal
    #
    wa
    #
    cP
    @9
    cfv
    #
    @2
    wcel
    #
    wi
    #
    vs
    @30
    wral
    #
    wi
    #
    @39
    wph
    @35
    @38
    @2
    wss
    #
    @47
    @35
    @62
    wph
    @37
    @2
    wss
    #
    @35
    @2
    @36
    wcel
    @63
    @35
    vc
    abid
    @2
    @36
    intss1
    sylbir
    wph
    @38
    @37
    @2
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cL
    cT
    vm
    vo
    cE
    cH
    cK
    cW
    vs
    vp
    vc
    mclsval.d
    mclsval.e
    mclsval.c
    mclsval.1
    mclsval.2
    mclsval.3
    mclsax.h
    mclsax.a
    mclsax.l
    mclsax.w
    mclsval
    #
    sseq1d
    syl5ibr
    @34
    @62
    @47
    wi
    @3
    @62
    @34
    @47
    @62
    @33
    @46
    vm
    vo
    @62
    @32
    @45
    vp
    @62
    @31
    @44
    @8
    @62
    @29
    @43
    vs
    @30
    @62
    @42
    @26
    @28
    @62
    @41
    @12
    @25
    @41
    @62
    @12
    @11
    @38
    @2
    sstr2
    com12
    anim1d
    imim1d
    ralimdv
    imim2d
    alimdv
    2alimdv
    com12
    adantl
    sylcom
    wph
    @48
    cT
    cmpst
    cfv
    #
    wcel
    #
    cM
    cvv
    wcel
    cO
    cvv
    wcel
    cP
    cvv
    wcel
    w3a
    @47
    @61
    wi
    wph
    cT
    cmsta
    cfv
    #
    @65
    @48
    @65
    @67
    cT
    @65
    eqid
    #
    @67
    eqid
    #
    mstapst
    wph
    cA
    @67
    @48
    wph
    cT
    cmfs
    wcel
    #
    cA
    @67
    wss
    mclsval.1
    cA
    @67
    cT
    mclsax.a
    @69
    maxsta
    syl
    mclsax.4
    sseldd
    sseldi
    #
    cP
    cM
    @65
    cT
    cO
    @68
    mpstrcl
    @45
    @61
    vm
    vo
    vp
    cM
    cO
    cP
    cvv
    cvv
    cvv
    @4
    cM
    wceq
    #
    @5
    cO
    wceq
    #
    @6
    cP
    wceq
    #
    w3a
    #
    @8
    @49
    @44
    @60
    @75
    @7
    @48
    cA
    @75
    @4
    cM
    @5
    cO
    @6
    cP
    @72
    @73
    @74
    simp1
    #
    @72
    @73
    @74
    simp2
    #
    @72
    @73
    @74
    simp3
    #
    oteq123d
    eleq1d
    @75
    @43
    @59
    vs
    @30
    @75
    @42
    @56
    @28
    @58
    @75
    @41
    @52
    @25
    @55
    @75
    @11
    @51
    @38
    @75
    @10
    @50
    @9
    @75
    @5
    cO
    @1
    @77
    uneq1d
    imaeq2d
    sseq1d
    @75
    @24
    @54
    vx
    vy
    @75
    @15
    @53
    @23
    @75
    @4
    cM
    @13
    @14
    @76
    breqd
    imbi1d
    2albidv
    anbi12d
    @75
    @27
    @57
    @2
    @75
    @6
    cP
    @9
    @78
    fveq2d
    eleq1d
    imbi12d
    ralbidv
    imbi12d
    spc3gv
    3syl
    wph
    @49
    @60
    @39
    mclsax.4
    wph
    @60
    cS
    @50
    cima
    #
    @38
    wss
    #
    @53
    @16
    cS
    cfv
    #
    cW
    cfv
    #
    @19
    cS
    cfv
    #
    cW
    cfv
    #
    cxp
    #
    cK
    wss
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    wa
    #
    @39
    wph
    @80
    @88
    wph
    @80
    @13
    cS
    cfv
    #
    @38
    wcel
    #
    vx
    @50
    wral
    #
    wph
    @91
    vx
    @50
    @13
    @50
    wcel
    wph
    @13
    cO
    wcel
    #
    @13
    @1
    wcel
    #
    wo
    @91
    @13
    cO
    @1
    elun
    wph
    @93
    @91
    @94
    mclsax.6
    wph
    @91
    vx
    @1
    wph
    @91
    vx
    @1
    wral
    #
    vv
    cv
    cH
    cfv
    #
    cS
    cfv
    #
    @38
    wcel
    #
    vv
    cV
    wral
    #
    wph
    @98
    vv
    cV
    mclsax.7
    ralrimiva
    wph
    cV
    cE
    cH
    wf
    #
    cH
    cV
    wfn
    @95
    @99
    wb
    wph
    @70
    @100
    mclsval.1
    cT
    cE
    cH
    cV
    mclsax.v
    mclsval.e
    mclsax.h
    mvhf
    syl
    #
    cV
    cE
    cH
    ffn
    @91
    @98
    vx
    vv
    cV
    cH
    @13
    @96
    wceq
    @90
    @97
    @38
    @13
    @96
    cS
    fveq2
    eleq1d
    ralrn
    3syl
    mpbird
    r19.21bi
    jaodan
    sylan2b
    ralrimiva
    wph
    cS
    wfun
    #
    @50
    cS
    cdm
    #
    wss
    @80
    @92
    wb
    wph
    cE
    cE
    cS
    wf
    #
    @102
    wph
    cS
    @30
    wcel
    #
    @104
    mclsax.5
    cL
    cT
    cE
    cS
    mclsax.l
    mclsval.e
    msubf
    syl
    #
    cE
    cE
    cS
    ffun
    syl
    wph
    cO
    @1
    @103
    wph
    cO
    cE
    @103
    wph
    cO
    cE
    wss
    #
    cO
    cfn
    wcel
    #
    wph
    cM
    cD
    wss
    cM
    ccnv
    cM
    wceq
    wa
    #
    @107
    @108
    wa
    #
    cP
    cE
    wcel
    #
    wph
    @66
    @109
    @110
    @111
    w3a
    @71
    cP
    cM
    @65
    cT
    cE
    cO
    cD
    mclsval.d
    mclsval.e
    @68
    elmpst
    sylib
    simp2d
    simpld
    wph
    @104
    @103
    cE
    wceq
    @106
    cE
    cE
    cS
    fdm
    syl
    #
    sseqtr4d
    wph
    @1
    cE
    @103
    wph
    @100
    @1
    cE
    wss
    @101
    cV
    cE
    cH
    frn
    syl
    @112
    sseqtr4d
    unssd
    vx
    @50
    @38
    cS
    funimass4
    syl2anc
    mpbird
    wph
    @87
    vx
    vy
    wph
    @53
    @86
    wph
    @53
    wa
    #
    va
    cv
    #
    vb
    cv
    #
    cK
    wbr
    #
    vb
    @84
    wral
    va
    @82
    wral
    #
    @86
    @113
    @116
    va
    vb
    @82
    @84
    wph
    @53
    @114
    @82
    wcel
    #
    @115
    @84
    wcel
    #
    @116
    wph
    @53
    @118
    @119
    @116
    mclsax.8
    3exp2
    imp4b
    ralrimivv
    @86
    vz
    cv
    #
    cK
    wcel
    #
    vz
    @85
    wral
    @117
    vz
    @85
    cK
    dfss3
    @121
    @116
    vz
    va
    vb
    @82
    @84
    @120
    @114
    @115
    cop
    #
    wceq
    @121
    @122
    cK
    wcel
    @116
    @120
    @122
    cK
    eleq1
    @114
    @115
    cK
    df-br
    syl6bbr
    ralxp
    bitri
    sylibr
    ex
    alrimivv
    jca
    wph
    @105
    @60
    @89
    @39
    wi
    #
    wi
    mclsax.5
    @59
    @123
    vs
    cS
    @30
    @9
    cS
    wceq
    #
    @56
    @89
    @58
    @39
    @124
    @52
    @80
    @55
    @88
    @124
    @51
    @79
    @38
    @9
    cS
    @50
    imaeq1
    sseq1d
    @124
    @54
    @87
    vx
    vy
    @124
    @23
    @86
    @53
    @124
    @22
    @85
    cK
    @124
    @18
    @82
    @21
    @84
    @124
    @17
    @81
    cW
    @16
    @9
    cS
    fveq1
    fveq2d
    @124
    @20
    @83
    cW
    @19
    @9
    cS
    fveq1
    fveq2d
    xpeq12d
    sseq1d
    imbi2d
    2albidv
    anbi12d
    @124
    @57
    @0
    @2
    cP
    @9
    cS
    fveq1
    eleq1d
    imbi12d
    rspcv
    syl
    mpid
    embantd
    3syld
    alrimiv
    @35
    vc
    @0
    cP
    cS
    fvex
    elintab
    sylibr
    @64
    eleqtrrd
end
