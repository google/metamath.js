include "wfn.mm"
include "ccnv.mm"
include "co.mm"
include "cima.mm"
include "wcel.mm"
include "cfv.mm"
include "wf.mm"
include "crn.mm"
include "msubf.mm"
include "syl.mm"
include "ffn.mm"
include "cmax.mm"
include "wss.mm"
include "wceq.mm"
include "wa.mm"
include "cfn.mm"
include "cotp.mm"
include "cmpst.mm"
include "w3a.mm"
include "eqid.mm"
include "mppspst.mm"
include "sseldi.mm"
include "elmpst.mm"
include "sylib.mm"
include "simp1d.mm"
include "simpld.mm"
include "simp2d.mm"
include "cv.mm"
include "wral.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "ffun.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass5.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "cmfs.mm"
include "mvhf.mm"
include "ffvelrnda.mm"
include "elpreima.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "cun.mm"
include "wbr.mm"
include "cxp.mm"
include "wi.mm"
include "wal.mm"
include "3ad2ant1.mm"
include "3ad2antl1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3.mm"
include "mclsppslem.mm"
include "mclsind.mm"
include "elmpps.mm"
include "simprbi.mm"
include "sseldd.mm"
include "simplbda.mm"

theorem mclspps
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let cE: class E
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vo: setvar o
  let vp: setvar p
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vc: setvar c
  let vw: setvar w
  let vz: setvar z
  let vd: setvar d
  assume mclspps.d: |- D = ( mDV ` T )
  assume mclspps.e: |- E = ( mEx ` T )
  assume mclspps.c: |- C = ( mCls ` T )
  assume mclspps.1: |- ( ph -> T e. mFS )
  assume mclspps.2: |- ( ph -> K C_ D )
  assume mclspps.3: |- ( ph -> B C_ E )
  assume mclspps.j: |- J = ( mPPSt ` T )
  assume mclspps.l: |- L = ( mSubst ` T )
  assume mclspps.v: |- V = ( mVR ` T )
  assume mclspps.h: |- H = ( mVH ` T )
  assume mclspps.w: |- W = ( mVars ` T )
  assume mclspps.4: |- ( ph -> <. M , O , P >. e. J )
  assume mclspps.5: |- ( ph -> S e. ran L )
  assume mclspps.6: |- ( ( ph /\ x e. O ) -> ( S ` x ) e. ( K C B ) )
  assume mclspps.7: |- ( ( ph /\ v e. V ) -> ( S ` ( H ` v ) ) e. ( K C B ) )
  assume mclspps.8: |- ( ( ph /\ ( x M y /\ a e. ( W ` ( S ` ( H ` x ) ) ) /\ b e. ( W ` ( S ` ( H ` y ) ) ) ) ) -> a K b )

  disjoint E v
  disjoint a b
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint H a
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint H b
  disjoint v x
  disjoint v y
  disjoint H v
  disjoint x y
  disjoint H x
  disjoint H y
  disjoint V v
  disjoint K a
  disjoint K b
  disjoint K v
  disjoint K x
  disjoint K y
  disjoint T a
  disjoint T b
  disjoint T v
  disjoint T x
  disjoint T y
  disjoint L a
  disjoint L b
  disjoint L v
  disjoint L x
  disjoint L y
  disjoint S a
  disjoint S b
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint B a
  disjoint B b
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint W a
  disjoint W b
  disjoint W v
  disjoint W x
  disjoint W y
  disjoint C a
  disjoint C b
  disjoint C v
  disjoint C x
  disjoint C y
  disjoint M a
  disjoint M b
  disjoint M v
  disjoint M x
  disjoint M y
  disjoint O v
  disjoint O x
  disjoint a ph
  disjoint b ph
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint m o
  disjoint m p
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint E m
  disjoint o p
  disjoint o s
  disjoint o t
  disjoint o u
  disjoint o v
  disjoint E o
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p v
  disjoint E p
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint E s
  disjoint t u
  disjoint t v
  disjoint E t
  disjoint u v
  disjoint E u
  disjoint a c
  disjoint a m
  disjoint a o
  disjoint a p
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a w
  disjoint a z
  disjoint b c
  disjoint b m
  disjoint b o
  disjoint b p
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b w
  disjoint b z
  disjoint c m
  disjoint c o
  disjoint c p
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint H c
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint H m
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint H o
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint H p
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint H s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint H t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint H u
  disjoint v w
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint H w
  disjoint x z
  disjoint y z
  disjoint H z
  disjoint V c
  disjoint V t
  disjoint V z
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint K c
  disjoint d m
  disjoint d o
  disjoint d p
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint K d
  disjoint K m
  disjoint K o
  disjoint K p
  disjoint K s
  disjoint K t
  disjoint K u
  disjoint T c
  disjoint d w
  disjoint d z
  disjoint T d
  disjoint T m
  disjoint T o
  disjoint T p
  disjoint T s
  disjoint T u
  disjoint T w
  disjoint T z
  disjoint L c
  disjoint L d
  disjoint L m
  disjoint L o
  disjoint L p
  disjoint L s
  disjoint L w
  disjoint L z
  disjoint S c
  disjoint S d
  disjoint S m
  disjoint S o
  disjoint S p
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint B c
  disjoint B d
  disjoint B m
  disjoint B o
  disjoint B p
  disjoint B s
  disjoint B t
  disjoint W c
  disjoint W m
  disjoint W o
  disjoint W p
  disjoint W s
  disjoint W u
  disjoint W w
  disjoint W z
  disjoint C c
  disjoint C m
  disjoint C o
  disjoint C p
  disjoint C s
  disjoint C t
  disjoint C z
  disjoint M m
  disjoint M o
  disjoint M p
  disjoint M s
  disjoint M w
  disjoint M z
  disjoint O m
  disjoint O o
  disjoint O p
  disjoint O s
  disjoint O w
  disjoint O z
  disjoint c ph
  disjoint d ph
  disjoint ph t
  disjoint ph u
  disjoint m ph
  disjoint o ph
  disjoint p ph
  disjoint ph s
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> ( S ` P ) e. ( K C B ) )

  proof
    wph
    cS
    cE
    wfn
    #
    cP
    cS
    ccnv
    cK
    cB
    cC
    co
    #
    cima
    #
    wcel
    #
    cP
    cS
    cfv
    @1
    wcel
    #
    wph
    cE
    cE
    cS
    wf
    #
    @0
    wph
    cS
    cL
    crn
    #
    wcel
    #
    @5
    mclspps.5
    cL
    cT
    cE
    cS
    mclspps.l
    mclspps.e
    msubf
    syl
    #
    cE
    cE
    cS
    ffn
    syl
    #
    wph
    cM
    cO
    cC
    co
    #
    @2
    cP
    wph
    vz
    vw
    vv
    cT
    cmax
    cfv
    #
    cO
    cC
    cD
    @2
    cT
    vm
    vo
    cE
    cH
    cM
    cL
    cV
    cW
    vs
    vp
    mclspps.d
    mclspps.e
    mclspps.c
    mclspps.1
    wph
    cM
    cD
    wss
    #
    cM
    ccnv
    cM
    wceq
    #
    wph
    @12
    @13
    wa
    #
    cO
    cE
    wss
    #
    cO
    cfn
    wcel
    #
    wa
    #
    cP
    cE
    wcel
    #
    wph
    cM
    cO
    cP
    cotp
    #
    cT
    cmpst
    cfv
    #
    wcel
    #
    @14
    @17
    @18
    w3a
    wph
    cJ
    @20
    @19
    @20
    cT
    cJ
    @20
    eqid
    #
    mclspps.j
    mppspst
    mclspps.4
    sseldi
    cP
    cM
    @20
    cT
    cE
    cO
    cD
    mclspps.d
    mclspps.e
    @22
    elmpst
    sylib
    #
    simp1d
    simpld
    wph
    @15
    @16
    wph
    @14
    @17
    @18
    @23
    simp2d
    simpld
    #
    @11
    eqid
    mclspps.l
    mclspps.v
    mclspps.h
    mclspps.w
    wph
    cO
    @2
    wss
    #
    vx
    cv
    #
    cS
    cfv
    @1
    wcel
    #
    vx
    cO
    wral
    #
    wph
    @27
    vx
    cO
    mclspps.6
    ralrimiva
    wph
    cS
    wfun
    #
    cO
    cS
    cdm
    #
    wss
    @25
    @28
    wb
    wph
    @5
    @29
    @8
    cE
    cE
    cS
    ffun
    syl
    wph
    cO
    cE
    @30
    @24
    wph
    @5
    @30
    cE
    wceq
    @8
    cE
    cE
    cS
    fdm
    syl
    sseqtr4d
    vx
    cO
    @1
    cS
    funimass5
    syl2anc
    mpbird
    wph
    vv
    cv
    #
    cV
    wcel
    #
    wa
    @31
    cH
    cfv
    #
    @2
    wcel
    #
    @33
    cE
    wcel
    #
    @33
    cS
    cfv
    @1
    wcel
    #
    wph
    cV
    cE
    @31
    cH
    wph
    cT
    cmfs
    wcel
    #
    cV
    cE
    cH
    wf
    mclspps.1
    cT
    cE
    cH
    cV
    mclspps.v
    mclspps.e
    mclspps.h
    mvhf
    syl
    ffvelrnda
    mclspps.7
    wph
    @34
    @35
    @36
    wa
    wb
    #
    @32
    wph
    @0
    @38
    @9
    cE
    @33
    @1
    cS
    elpreima
    syl
    adantr
    mpbir2and
    wph
    vm
    cv
    #
    vo
    cv
    #
    vp
    cv
    cotp
    @11
    wcel
    #
    vs
    cv
    #
    @6
    wcel
    #
    @42
    @40
    cH
    crn
    cun
    cima
    @2
    wss
    #
    w3a
    #
    vz
    cv
    #
    vw
    cv
    #
    @39
    wbr
    @46
    cH
    cfv
    @42
    cfv
    cW
    cfv
    @47
    cH
    cfv
    @42
    cfv
    cW
    cfv
    cxp
    cM
    wss
    wi
    vw
    wal
    vz
    wal
    #
    w3a
    vx
    vy
    vz
    vw
    vv
    cB
    cC
    cD
    cP
    cS
    cT
    vm
    vo
    cE
    cH
    cJ
    cK
    cL
    cM
    cO
    cV
    cW
    vs
    vp
    va
    vb
    mclspps.d
    mclspps.e
    mclspps.c
    wph
    @45
    @37
    @48
    mclspps.1
    3ad2ant1
    wph
    @45
    cK
    cD
    wss
    @48
    mclspps.2
    3ad2ant1
    wph
    @45
    cB
    cE
    wss
    @48
    mclspps.3
    3ad2ant1
    mclspps.j
    mclspps.l
    mclspps.v
    mclspps.h
    mclspps.w
    wph
    @45
    @19
    cJ
    wcel
    #
    @48
    mclspps.4
    3ad2ant1
    wph
    @45
    @7
    @48
    mclspps.5
    3ad2ant1
    wph
    @45
    @26
    cO
    wcel
    @27
    @48
    mclspps.6
    3ad2antl1
    wph
    @45
    @32
    @36
    @48
    mclspps.7
    3ad2antl1
    wph
    @45
    @26
    vy
    cv
    #
    cM
    wbr
    va
    cv
    #
    @26
    cH
    cfv
    cS
    cfv
    cW
    cfv
    wcel
    vb
    cv
    #
    @50
    cH
    cfv
    cS
    cfv
    cW
    cfv
    wcel
    w3a
    @51
    @52
    cK
    wbr
    @48
    mclspps.8
    3ad2antl1
    wph
    @41
    @43
    @44
    @48
    simp21
    wph
    @41
    @43
    @44
    @48
    simp22
    wph
    @41
    @43
    @44
    @48
    simp23
    wph
    @45
    @48
    simp3
    mclsppslem
    mclsind
    wph
    @49
    cP
    @10
    wcel
    #
    mclspps.4
    @49
    @21
    @53
    cP
    cC
    cM
    @20
    cT
    cO
    cJ
    @22
    mclspps.j
    mclspps.c
    elmpps
    simprbi
    syl
    sseldd
    @0
    @3
    @18
    @4
    cE
    cP
    @1
    cS
    elpreima
    simplbda
    syl2anc
end
