include "cpw.mm"
include "cv.mm"
include "crn.mm"
include "cun.mm"
include "wss.mm"
include "cotp.mm"
include "wcel.mm"
include "cima.mm"
include "wbr.mm"
include "cfv.mm"
include "cxp.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "cvv.mm"
include "cmcls.mm"
include "cmpt2.mm"
include "cmfs.mm"
include "wceq.mm"
include "elex.mm"
include "cmdv.mm"
include "cmex.mm"
include "cmvh.mm"
include "cmax.mm"
include "cmvrs.mm"
include "cmsub.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "rneqd.mm"
include "uneq2d.mm"
include "sseq1d.mm"
include "eleq2d.mm"
include "imaeq2d.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "xpeq12d.mm"
include "imbi2d.mm"
include "2albidv.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "raleqbidv.mm"
include "imbi12d.mm"
include "albidv.mm"
include "abbidv.mm"
include "inteqd.mm"
include "mpt2eq123dv.mm"
include "df-mcls.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "3syl.mm"
include "syl5eq.mm"
include "simprr.mm"
include "uneq1d.mm"
include "simprl.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "ralbidv.mm"
include "elpw2.mm"
include "sylibr.mm"
include "mclsssvlem.mm"
include "ssex.mm"
include "syl.mm"
include "ovmpt2d.mm"

theorem mclsval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vm: setvar m
  let vo: setvar o
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let vs: setvar s
  let vp: setvar p
  let vc: setvar c
  let vd: setvar d
  let vh: setvar h
  let vt: setvar t
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let cL: class L
  let cO: class O
  let cM: class M
  let cP: class P
  let cQ: class Q
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mclsval.d: |- D = ( mDV ` T )
  assume mclsval.e: |- E = ( mEx ` T )
  assume mclsval.c: |- C = ( mCls ` T )
  assume mclsval.1: |- ( ph -> T e. mFS )
  assume mclsval.2: |- ( ph -> K C_ D )
  assume mclsval.3: |- ( ph -> B C_ E )
  assume mclsval.h: |- H = ( mVH ` T )
  assume mclsval.a: |- A = ( mAx ` T )
  assume mclsval.s: |- S = ( mSubst ` T )
  assume mclsval.v: |- V = ( mVars ` T )

  disjoint c m
  disjoint c o
  disjoint c p
  disjoint c s
  disjoint E c
  disjoint m o
  disjoint m p
  disjoint m s
  disjoint E m
  disjoint o p
  disjoint o s
  disjoint E o
  disjoint p s
  disjoint E p
  disjoint E s
  disjoint c x
  disjoint H c
  disjoint m x
  disjoint H m
  disjoint o x
  disjoint H o
  disjoint p x
  disjoint H p
  disjoint s x
  disjoint H s
  disjoint H x
  disjoint c y
  disjoint B c
  disjoint m y
  disjoint B m
  disjoint o y
  disjoint B o
  disjoint p y
  disjoint B p
  disjoint s y
  disjoint B s
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C m
  disjoint C o
  disjoint C p
  disjoint C s
  disjoint C x
  disjoint A c
  disjoint A m
  disjoint A o
  disjoint A p
  disjoint A s
  disjoint S c
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T c
  disjoint T m
  disjoint T o
  disjoint T p
  disjoint T s
  disjoint T x
  disjoint T y
  disjoint c ph
  disjoint m ph
  disjoint o ph
  disjoint p ph
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint V c
  disjoint V x
  disjoint K c
  disjoint K m
  disjoint K o
  disjoint K p
  disjoint K s
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
  disjoint c t
  disjoint c v
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
  disjoint m t
  disjoint m v
  disjoint o t
  disjoint o v
  disjoint p t
  disjoint p v
  disjoint s t
  disjoint s v
  disjoint t v
  disjoint E t
  disjoint E v
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a h
  disjoint a m
  disjoint a o
  disjoint a p
  disjoint a s
  disjoint a t
  disjoint a v
  disjoint a x
  disjoint a z
  disjoint H a
  disjoint b c
  disjoint b d
  disjoint b h
  disjoint b m
  disjoint b o
  disjoint b p
  disjoint b s
  disjoint b t
  disjoint b v
  disjoint b x
  disjoint b z
  disjoint H b
  disjoint c z
  disjoint d x
  disjoint d z
  disjoint H d
  disjoint h x
  disjoint h z
  disjoint H h
  disjoint m z
  disjoint o z
  disjoint p z
  disjoint s z
  disjoint t x
  disjoint t z
  disjoint H t
  disjoint v x
  disjoint v z
  disjoint H v
  disjoint x z
  disjoint H z
  disjoint d y
  disjoint B d
  disjoint h y
  disjoint B h
  disjoint t y
  disjoint B t
  disjoint v y
  disjoint B v
  disjoint C t
  disjoint C v
  disjoint L c
  disjoint L m
  disjoint L o
  disjoint L p
  disjoint L s
  disjoint L x
  disjoint L y
  disjoint A d
  disjoint A h
  disjoint A t
  disjoint O m
  disjoint O o
  disjoint O p
  disjoint O s
  disjoint O x
  disjoint O y
  disjoint a y
  disjoint S a
  disjoint b y
  disjoint S b
  disjoint S d
  disjoint S h
  disjoint S t
  disjoint S v
  disjoint y z
  disjoint S z
  disjoint M a
  disjoint M b
  disjoint M m
  disjoint M o
  disjoint M p
  disjoint M s
  disjoint M x
  disjoint M y
  disjoint P c
  disjoint P m
  disjoint P o
  disjoint P p
  disjoint P s
  disjoint P x
  disjoint P y
  disjoint T d
  disjoint T h
  disjoint T t
  disjoint a ph
  disjoint b ph
  disjoint d ph
  disjoint h ph
  disjoint ph v
  disjoint Q c
  disjoint Q m
  disjoint Q o
  disjoint Q p
  disjoint Q s
  disjoint Q v
  disjoint V d
  disjoint V h
  disjoint V t
  disjoint V v
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W m
  disjoint W o
  disjoint W p
  disjoint W s
  disjoint W x
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
  disjoint K a
  disjoint K b
  disjoint K d
  disjoint K h
  disjoint K t
  disjoint K v
  disjoint K z
  assert |- ( ph -> ( K C B ) = |^| { c | ( ( B u. ran H ) C_ c /\ A. m A. o A. p ( <. m , o , p >. e. A -> A. s e. ran S ( ( ( s " ( o u. ran H ) ) C_ c /\ A. x A. y ( x m y -> ( ( V ` ( s ` ( H ` x ) ) ) X. ( V ` ( s ` ( H ` y ) ) ) ) C_ K ) ) -> ( s ` p ) e. c ) ) ) } )

  proof
    wph
    vd
    vh
    cK
    cB
    cD
    cpw
    #
    cE
    cpw
    #
    vh
    cv
    #
    cH
    crn
    #
    cun
    #
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
    @8
    @3
    cun
    #
    cima
    #
    @5
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    @7
    wbr
    #
    @16
    cH
    cfv
    #
    @12
    cfv
    #
    cV
    cfv
    #
    @17
    cH
    cfv
    #
    @12
    cfv
    #
    cV
    cfv
    #
    cxp
    #
    vd
    cv
    #
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
    @9
    @12
    cfv
    @5
    wcel
    #
    wi
    #
    vs
    cS
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
    cB
    @3
    cun
    #
    @5
    wss
    #
    @11
    @15
    @18
    @25
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
    @31
    wi
    #
    vs
    @33
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
    cC
    cvv
    wph
    cC
    cT
    cmcls
    cfv
    #
    vd
    vh
    @0
    @1
    @40
    cmpt2
    #
    mclsval.c
    wph
    cT
    cmfs
    wcel
    cT
    cvv
    wcel
    @55
    @56
    wceq
    mclsval.1
    cT
    cmfs
    elex
    vt
    cT
    vd
    vh
    vt
    cv
    #
    cmdv
    cfv
    #
    cpw
    #
    @57
    cmex
    cfv
    #
    cpw
    #
    @2
    @57
    cmvh
    cfv
    #
    crn
    #
    cun
    #
    @5
    wss
    #
    @10
    @57
    cmax
    cfv
    #
    wcel
    #
    @12
    @8
    @63
    cun
    #
    cima
    #
    @5
    wss
    #
    @18
    @16
    @62
    cfv
    #
    @12
    cfv
    #
    @57
    cmvrs
    cfv
    #
    cfv
    #
    @17
    @62
    cfv
    #
    @12
    cfv
    #
    @73
    cfv
    #
    cxp
    #
    @26
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
    @31
    wi
    #
    vs
    @57
    cmsub
    cfv
    #
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
    cmpt2
    @56
    cvv
    cmcls
    @57
    cT
    wceq
    #
    vd
    vh
    @59
    @61
    @92
    @0
    @1
    @40
    @93
    @58
    cD
    @93
    @58
    cT
    cmdv
    cfv
    #
    cD
    @57
    cT
    cmdv
    fveq2
    mclsval.d
    syl6eqr
    pweqd
    @93
    @60
    cE
    @93
    @60
    cT
    cmex
    cfv
    #
    cE
    @57
    cT
    cmex
    fveq2
    mclsval.e
    syl6eqr
    pweqd
    @93
    @91
    @39
    @93
    @90
    @38
    vc
    @93
    @65
    @6
    @89
    @37
    @93
    @64
    @4
    @5
    @93
    @63
    @3
    @2
    @93
    @62
    cH
    @93
    @62
    cT
    cmvh
    cfv
    cH
    @57
    cT
    cmvh
    fveq2
    mclsval.h
    syl6eqr
    #
    rneqd
    #
    uneq2d
    sseq1d
    @93
    @88
    @36
    vm
    vo
    @93
    @87
    @35
    vp
    @93
    @67
    @11
    @86
    @34
    @93
    @66
    cA
    @10
    @93
    @66
    cT
    cmax
    cfv
    cA
    @57
    cT
    cmax
    fveq2
    mclsval.a
    syl6eqr
    eleq2d
    @93
    @83
    @32
    vs
    @85
    @33
    @93
    @84
    cS
    @93
    @84
    cT
    cmsub
    cfv
    cS
    @57
    cT
    cmsub
    fveq2
    mclsval.s
    syl6eqr
    rneqd
    @93
    @82
    @30
    @31
    @93
    @70
    @15
    @81
    @29
    @93
    @69
    @14
    @5
    @93
    @68
    @13
    @12
    @93
    @63
    @3
    @8
    @97
    uneq2d
    imaeq2d
    sseq1d
    @93
    @80
    @28
    vx
    vy
    @93
    @79
    @27
    @18
    @93
    @78
    @25
    @26
    @93
    @74
    @21
    @77
    @24
    @93
    @72
    @20
    @73
    cV
    @93
    @73
    cT
    cmvrs
    cfv
    cV
    @57
    cT
    cmvrs
    fveq2
    mclsval.v
    syl6eqr
    #
    @93
    @71
    @19
    @12
    @93
    @16
    @62
    cH
    @96
    fveq1d
    fveq2d
    fveq12d
    @93
    @76
    @23
    @73
    cV
    @98
    @93
    @75
    @22
    @12
    @93
    @17
    @62
    cH
    @96
    fveq1d
    fveq2d
    fveq12d
    xpeq12d
    sseq1d
    imbi2d
    2albidv
    anbi12d
    imbi1d
    raleqbidv
    imbi12d
    albidv
    2albidv
    anbi12d
    abbidv
    inteqd
    mpt2eq123dv
    vx
    vy
    vt
    vh
    vm
    vo
    vs
    vp
    vc
    vd
    df-mcls
    vd
    vh
    @0
    @1
    @40
    cD
    cD
    @94
    cvv
    mclsval.d
    cT
    cmdv
    fvex
    eqeltri
    #
    pwex
    cE
    cE
    @95
    cvv
    mclsval.e
    cT
    cmex
    fvex
    eqeltri
    #
    pwex
    mpt2ex
    fvmpt
    3syl
    syl5eq
    wph
    @26
    cK
    wceq
    #
    @2
    cB
    wceq
    #
    wa
    wa
    #
    @39
    @53
    @103
    @38
    @52
    vc
    @103
    @6
    @42
    @37
    @51
    @103
    @4
    @41
    @5
    @103
    @2
    cB
    @3
    wph
    @101
    @102
    simprr
    uneq1d
    sseq1d
    @103
    @36
    @50
    vm
    vo
    @103
    @35
    @49
    vp
    @103
    @34
    @48
    @11
    @103
    @32
    @47
    vs
    @33
    @103
    @30
    @46
    @31
    @103
    @29
    @45
    @15
    @103
    @28
    @44
    vx
    vy
    @103
    @27
    @43
    @18
    @103
    @26
    cK
    @25
    wph
    @101
    @102
    simprl
    sseq2d
    imbi2d
    2albidv
    anbi2d
    imbi1d
    ralbidv
    imbi2d
    albidv
    2albidv
    anbi12d
    abbidv
    inteqd
    wph
    cK
    cD
    wss
    cK
    @0
    wcel
    mclsval.2
    cK
    cD
    @99
    elpw2
    sylibr
    wph
    cB
    cE
    wss
    cB
    @1
    wcel
    mclsval.3
    cB
    cE
    @100
    elpw2
    sylibr
    wph
    @54
    cE
    wss
    @54
    cvv
    wcel
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cS
    cT
    vm
    vo
    cE
    cH
    cK
    cV
    vs
    vp
    vc
    mclsval.d
    mclsval.e
    mclsval.c
    mclsval.1
    mclsval.2
    mclsval.3
    mclsval.h
    mclsval.a
    mclsval.s
    mclsval.v
    mclsssvlem
    @54
    cE
    @100
    ssex
    syl
    ovmpt2d
end
