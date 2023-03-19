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
include "cmvar.mm"
include "wf.mm"
include "cmfs.mm"
include "eqid.mm"
include "mvhf.mm"
include "syl.mm"
include "frn.mm"
include "unssd.mm"
include "msubf.mm"
include "cmpst.mm"
include "cmsta.mm"
include "maxsta.mm"
include "mstapst.mm"
include "syl6ss.mm"
include "sselda.mm"
include "ccnv.mm"
include "wceq.mm"
include "cfn.mm"
include "elmpst.mm"
include "simp3bi.mm"
include "ffvelrn.mm"
include "syl2anr.mm"
include "a1d.mm"
include "ralrimiva.mm"
include "ex.mm"
include "alrimiv.mm"
include "alrimivv.mm"
include "cmex.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
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
include "sylanbrc.mm"
include "intss1.mm"

theorem mclsssvlem
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
  assert |- ( ph -> |^| { c | ( ( B u. ran H ) C_ c /\ A. m A. o A. p ( <. m , o , p >. e. A -> A. s e. ran S ( ( ( s " ( o u. ran H ) ) C_ c /\ A. x A. y ( x m y -> ( ( V ` ( s ` ( H ` x ) ) ) X. ( V ` ( s ` ( H ` y ) ) ) ) C_ K ) ) -> ( s ` p ) e. c ) ) ) } C_ E )

  proof
    wph
    cE
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
    cV
    cfv
    @13
    cH
    cfv
    @9
    cfv
    cV
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
    wcel
    #
    @25
    cint
    cE
    wss
    wph
    @1
    cE
    wss
    #
    @8
    @10
    cE
    wss
    #
    @14
    wa
    #
    @16
    cE
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
    @26
    wph
    cB
    @0
    cE
    mclsval.3
    wph
    cT
    cmvar
    cfv
    #
    cE
    cH
    wf
    #
    @0
    cE
    wss
    wph
    cT
    cmfs
    wcel
    #
    @37
    mclsval.1
    cT
    cE
    cH
    @36
    @36
    eqid
    mclsval.e
    mclsval.h
    mvhf
    syl
    @36
    cE
    cH
    frn
    syl
    unssd
    wph
    @34
    vm
    vo
    wph
    @33
    vp
    wph
    @8
    @32
    wph
    @8
    wa
    #
    @31
    vs
    @19
    @39
    @9
    @19
    wcel
    #
    wa
    @30
    @29
    @40
    cE
    cE
    @9
    wf
    @6
    cE
    wcel
    #
    @30
    @39
    cS
    cT
    cE
    @9
    mclsval.s
    mclsval.e
    msubf
    @39
    @7
    cT
    cmpst
    cfv
    #
    wcel
    #
    @41
    wph
    cA
    @42
    @7
    wph
    cA
    cT
    cmsta
    cfv
    #
    @42
    wph
    @38
    cA
    @44
    wss
    mclsval.1
    cA
    @44
    cT
    mclsval.a
    @44
    eqid
    #
    maxsta
    syl
    @42
    @44
    cT
    @42
    eqid
    #
    @45
    mstapst
    syl6ss
    sselda
    @43
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
    @41
    @6
    @4
    @42
    cT
    cE
    @5
    cD
    mclsval.d
    mclsval.e
    @46
    elmpst
    simp3bi
    syl
    cE
    cE
    @6
    @9
    ffvelrn
    syl2anr
    a1d
    ralrimiva
    ex
    alrimiv
    alrimivv
    @24
    @27
    @35
    wa
    vc
    cE
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
    @2
    cE
    wceq
    #
    @3
    @27
    @23
    @35
    @2
    cE
    @1
    sseq2
    @47
    @22
    @34
    vm
    vo
    @47
    @21
    @33
    vp
    @47
    @20
    @32
    @8
    @47
    @18
    @31
    vs
    @19
    @47
    @15
    @29
    @17
    @30
    @47
    @11
    @28
    @14
    @2
    cE
    @10
    sseq2
    anbi1d
    @2
    cE
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
    cE
    @25
    intss1
    syl
end
