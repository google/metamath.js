include "co.mm"
include "crn.mm"
include "cun.mm"
include "cv.mm"
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
include "mclsval.mm"
include "cin.mm"
include "ssind.mm"
include "wf.mm"
include "wfn.mm"
include "cmfs.mm"
include "mvhf.mm"
include "syl.mm"
include "ffn.mm"
include "ffvelrnda.mm"
include "elind.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "frn.mm"
include "unssd.mm"
include "id.mm"
include "inss2.mm"
include "syl6ss.mm"
include "w3a.mm"
include "cmap.mm"
include "cmrex.mm"
include "cpm.mm"
include "adantr.mm"
include "eqid.mm"
include "msubff.mm"
include "3syl.mm"
include "simpr2.mm"
include "sseldd.mm"
include "elmapi.mm"
include "cmpst.mm"
include "cmsta.mm"
include "maxsta.mm"
include "mstapst.mm"
include "simpr1.mm"
include "ccnv.mm"
include "wceq.mm"
include "cfn.mm"
include "elmpst.mm"
include "simp3bi.mm"
include "ffvelrnd.mm"
include "3adant3.mm"
include "3exp.mm"
include "3expd.mm"
include "imp31.mm"
include "syl5.mm"
include "impd.mm"
include "ex.mm"
include "alrimiv.mm"
include "alrimivv.mm"
include "cmex.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "inex1.mm"
include "sseq2.mm"
include "anbi1d.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "imbi2d.mm"
include "albidv.mm"
include "2albidv.mm"
include "anbi12d.mm"
include "elab.mm"
include "intss1.mm"
include "eqsstrd.mm"

theorem mclsind
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cT: class T
  let vm: setvar m
  let vo: setvar o
  let cE: class E
  let cH: class H
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vp: setvar p
  let vd: setvar d
  let vh: setvar h
  let vt: setvar t
  let vc: setvar c
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let cO: class O
  let cS: class S
  let cM: class M
  let cP: class P
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
  assume mclsind.4: |- ( ph -> B C_ Q )
  assume mclsind.5: |- ( ( ph /\ v e. V ) -> ( H ` v ) e. Q )
  assume mclsind.6: |- ( ( ph /\ ( <. m , o , p >. e. A /\ s e. ran L /\ ( s " ( o u. ran H ) ) C_ Q ) /\ A. x A. y ( x m y -> ( ( W ` ( s ` ( H ` x ) ) ) X. ( W ` ( s ` ( H ` y ) ) ) ) C_ K ) ) -> ( s ` p ) e. Q )

  disjoint m o
  disjoint m p
  disjoint m s
  disjoint m v
  disjoint E m
  disjoint o p
  disjoint o s
  disjoint o v
  disjoint E o
  disjoint p s
  disjoint p v
  disjoint E p
  disjoint s v
  disjoint E s
  disjoint E v
  disjoint m x
  disjoint H m
  disjoint o x
  disjoint H o
  disjoint p x
  disjoint H p
  disjoint s x
  disjoint H s
  disjoint v x
  disjoint H v
  disjoint H x
  disjoint m y
  disjoint B m
  disjoint o y
  disjoint B o
  disjoint p y
  disjoint B p
  disjoint s y
  disjoint B s
  disjoint v y
  disjoint B v
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C m
  disjoint C o
  disjoint C p
  disjoint C s
  disjoint C v
  disjoint C x
  disjoint L m
  disjoint L o
  disjoint L p
  disjoint L s
  disjoint L x
  disjoint L y
  disjoint A m
  disjoint A o
  disjoint A p
  disjoint A s
  disjoint T m
  disjoint T o
  disjoint T p
  disjoint T s
  disjoint T x
  disjoint T y
  disjoint m ph
  disjoint o ph
  disjoint p ph
  disjoint ph s
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint Q m
  disjoint Q o
  disjoint Q p
  disjoint Q s
  disjoint Q v
  disjoint V v
  disjoint V x
  disjoint W m
  disjoint W o
  disjoint W p
  disjoint W s
  disjoint W x
  disjoint K m
  disjoint K o
  disjoint K p
  disjoint K s
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
  disjoint m t
  disjoint o t
  disjoint p t
  disjoint s t
  disjoint t v
  disjoint E t
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
  disjoint c x
  disjoint c z
  disjoint H c
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
  disjoint v z
  disjoint x z
  disjoint H z
  disjoint c y
  disjoint B c
  disjoint d y
  disjoint B d
  disjoint h y
  disjoint B h
  disjoint t y
  disjoint B t
  disjoint C t
  disjoint L c
  disjoint A c
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
  disjoint S c
  disjoint S d
  disjoint S h
  disjoint S s
  disjoint S t
  disjoint S v
  disjoint S x
  disjoint y z
  disjoint S y
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
  disjoint T c
  disjoint T d
  disjoint T h
  disjoint T t
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint h ph
  disjoint Q c
  disjoint V c
  disjoint V d
  disjoint V h
  disjoint V t
  disjoint W a
  disjoint W b
  disjoint W c
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
  disjoint K c
  disjoint K d
  disjoint K h
  disjoint K t
  disjoint K z
  assert |- ( ph -> ( K C B ) C_ Q )

  proof
    wph
    cK
    cB
    cC
    co
    cB
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
    @5
    @0
    cun
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
    @12
    cH
    cfv
    @9
    cfv
    cW
    cfv
    @13
    cH
    cfv
    @9
    cfv
    cW
    cfv
    cxp
    cK
    wss
    wi
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
    cQ
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
    wph
    @26
    cE
    cQ
    cin
    #
    cQ
    wph
    @27
    @25
    wcel
    #
    @26
    @27
    wss
    wph
    @1
    @27
    wss
    #
    @8
    @10
    @27
    wss
    #
    @14
    wa
    #
    @16
    @27
    wcel
    #
    wi
    #
    vs
    @19
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
    @28
    wph
    cB
    @0
    @27
    wph
    cB
    cE
    cQ
    mclsval.3
    mclsind.4
    ssind
    wph
    cV
    @27
    cH
    wf
    #
    @0
    @27
    wss
    wph
    cH
    cV
    wfn
    #
    vv
    cv
    #
    cH
    cfv
    #
    @27
    wcel
    #
    vv
    cV
    wral
    @38
    wph
    cV
    cE
    cH
    wf
    #
    @39
    wph
    cT
    cmfs
    wcel
    #
    @43
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
    syl
    wph
    @42
    vv
    cV
    wph
    @40
    cV
    wcel
    wa
    cE
    cQ
    @41
    wph
    cV
    cE
    @40
    cH
    @45
    ffvelrnda
    mclsind.5
    elind
    ralrimiva
    vv
    cV
    @27
    cH
    ffnfv
    sylanbrc
    cV
    @27
    cH
    frn
    syl
    unssd
    wph
    @36
    vm
    vo
    wph
    @35
    vp
    wph
    @8
    @34
    wph
    @8
    wa
    #
    @33
    vs
    @19
    @46
    @9
    @19
    wcel
    #
    wa
    #
    @30
    @14
    @32
    @30
    @10
    cQ
    wss
    #
    @48
    @14
    @32
    wi
    #
    @30
    @10
    @27
    cQ
    @30
    id
    cE
    cQ
    inss2
    #
    syl6ss
    wph
    @8
    @47
    @49
    @50
    wi
    wph
    @8
    @47
    @49
    @50
    wph
    @8
    @47
    @49
    w3a
    #
    @14
    @32
    wph
    @52
    @14
    w3a
    cE
    cQ
    @16
    wph
    @52
    @16
    cE
    wcel
    @14
    wph
    @52
    wa
    #
    cE
    cE
    @6
    @9
    @53
    @9
    cE
    cE
    cmap
    co
    #
    wcel
    cE
    cE
    @9
    wf
    @53
    @19
    @54
    @9
    @53
    @44
    cT
    cmrex
    cfv
    #
    cV
    cpm
    co
    #
    @54
    cL
    wf
    @19
    @54
    wss
    wph
    @44
    @52
    mclsval.1
    adantr
    #
    @55
    cL
    cT
    cE
    cV
    cmfs
    mclsax.v
    @55
    eqid
    mclsax.l
    mclsval.e
    msubff
    @56
    @54
    cL
    frn
    3syl
    wph
    @8
    @47
    @49
    simpr2
    sseldd
    @9
    cE
    cE
    elmapi
    syl
    @53
    @7
    cT
    cmpst
    cfv
    #
    wcel
    #
    @6
    cE
    wcel
    #
    @53
    cA
    @58
    @7
    @53
    cA
    cT
    cmsta
    cfv
    #
    @58
    @53
    @44
    cA
    @61
    wss
    @57
    cA
    @61
    cT
    mclsax.a
    @61
    eqid
    #
    maxsta
    syl
    @58
    @61
    cT
    @58
    eqid
    #
    @62
    mstapst
    syl6ss
    wph
    @8
    @47
    @49
    simpr1
    sseldd
    @59
    @4
    cD
    wss
    @4
    ccnv
    @4
    wceq
    wa
    @5
    cE
    wss
    @5
    cfn
    wcel
    wa
    @60
    @6
    @4
    @58
    cT
    cE
    @5
    cD
    mclsval.d
    mclsval.e
    @63
    elmpst
    simp3bi
    syl
    ffvelrnd
    3adant3
    mclsind.6
    elind
    3exp
    3expd
    imp31
    syl5
    impd
    ralrimiva
    ex
    alrimiv
    alrimivv
    @24
    @29
    @37
    wa
    vc
    @27
    cE
    cQ
    cE
    cT
    cmex
    cfv
    cvv
    mclsval.e
    cT
    cmex
    fvex
    eqeltri
    inex1
    @2
    @27
    wceq
    #
    @3
    @29
    @23
    @37
    @2
    @27
    @1
    sseq2
    @64
    @22
    @36
    vm
    vo
    @64
    @21
    @35
    vp
    @64
    @20
    @34
    @8
    @64
    @18
    @33
    vs
    @19
    @64
    @15
    @31
    @17
    @32
    @64
    @11
    @30
    @14
    @2
    @27
    @10
    sseq2
    anbi1d
    @2
    @27
    @16
    eleq2
    imbi12d
    ralbidv
    imbi2d
    albidv
    2albidv
    anbi12d
    elab
    sylanbrc
    @27
    @25
    intss1
    syl
    @51
    syl6ss
    eqsstrd
end
