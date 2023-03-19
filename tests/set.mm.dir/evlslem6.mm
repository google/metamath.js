include "cv.mm"
include "cfv.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "cmpt.mm"
include "wf.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "adantr.mm"
include "crh.mm"
include "rhmf.mm"
include "mplelf.mm"
include "ffvelrnda.mm"
include "ffvelrnd.mm"
include "mgpbas.mm"
include "eqid.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "simpr.mm"
include "cvv.mm"
include "psrbagev2.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "wfun.mm"
include "csupp.mm"
include "cfn.mm"
include "wss.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cn0.mm"
include "cmap.mm"
include "ovexd.mm"
include "rabexd.mm"
include "mptexg.mm"
include "funmpt.mm"
include "a1i.mm"
include "fvexd.mm"
include "mplelsfi.mm"
include "fsuppimpd.mm"
include "wceq.mm"
include "feqmptd.mm"
include "oveq1d.mm"
include "eqimss2.mm"
include "cghm.mm"
include "rhmghm.mm"
include "ghmid.mm"
include "3syl.mm"
include "suppssfv.mm"
include "ringlz.mm"
include "sylan.mm"
include "suppssov1.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "jca.mm"

theorem evlslem6
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let vh: setvar h
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let cY: class Y
  let vp: setvar p
  let vb: setvar b
  let vx: setvar x
  assume evlslem1.p: |- P = ( I mPoly R )
  assume evlslem1.b: |- B = ( Base ` P )
  assume evlslem1.c: |- C = ( Base ` S )
  assume evlslem1.k: |- K = ( Base ` R )
  assume evlslem1.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume evlslem1.t: |- T = ( mulGrp ` S )
  assume evlslem1.x: |- .^ = ( .g ` T )
  assume evlslem1.m: |- .x. = ( .r ` S )
  assume evlslem1.v: |- V = ( I mVar R )
  assume evlslem1.e: |- E = ( p e. B |-> ( S gsum ( b e. D |-> ( ( F ` ( p ` b ) ) .x. ( T gsum ( b oF .^ G ) ) ) ) ) )
  assume evlslem1.i: |- ( ph -> I e. _V )
  assume evlslem1.r: |- ( ph -> R e. CRing )
  assume evlslem1.s: |- ( ph -> S e. CRing )
  assume evlslem1.f: |- ( ph -> F e. ( R RingHom S ) )
  assume evlslem1.g: |- ( ph -> G : I --> C )
  assume evlslem6.y: |- ( ph -> Y e. B )

  disjoint b ph
  disjoint C b
  disjoint D b
  disjoint I h
  disjoint R b
  disjoint S b
  disjoint Y b
  disjoint b h
  disjoint ph x
  disjoint b x
  disjoint C x
  disjoint G x
  disjoint .x. x
  disjoint S x
  disjoint T x
  disjoint .^ x
  assert |- ( ph -> ( ( b e. D |-> ( ( F ` ( Y ` b ) ) .x. ( T gsum ( b oF .^ G ) ) ) ) : D --> C /\ ( b e. D |-> ( ( F ` ( Y ` b ) ) .x. ( T gsum ( b oF .^ G ) ) ) ) finSupp ( 0g ` S ) ) )

  proof
    wph
    cD
    cC
    vb
    cD
    vb
    cv
    #
    cY
    cfv
    #
    cF
    cfv
    #
    cT
    @0
    cG
    c.ex
    cof
    co
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    #
    wf
    @5
    cS
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    wph
    vb
    cD
    @4
    cC
    @5
    wph
    @0
    cD
    wcel
    #
    wa
    #
    cS
    crg
    wcel
    #
    @2
    cC
    wcel
    @3
    cC
    wcel
    @4
    cC
    wcel
    wph
    @10
    @8
    wph
    cS
    ccrg
    wcel
    #
    @10
    evlslem1.s
    cS
    crngring
    syl
    #
    adantr
    @9
    cK
    cC
    @1
    cF
    wph
    cK
    cC
    cF
    wf
    #
    @8
    wph
    cF
    cR
    cS
    crh
    co
    wcel
    #
    @13
    evlslem1.f
    cK
    cC
    cR
    cS
    cF
    evlslem1.k
    evlslem1.c
    rhmf
    syl
    adantr
    wph
    cD
    cK
    @0
    cY
    wph
    cB
    cD
    cP
    cR
    vh
    cI
    cK
    cY
    evlslem1.p
    evlslem1.k
    evlslem1.b
    evlslem1.d
    evlslem6.y
    mplelf
    #
    ffvelrnda
    ffvelrnd
    @9
    @0
    cC
    cD
    cT
    c.ex
    vh
    cG
    cI
    cT
    c0g
    cfv
    #
    evlslem1.d
    cC
    cS
    cT
    evlslem1.t
    evlslem1.c
    mgpbas
    evlslem1.x
    @16
    eqid
    wph
    cT
    ccmn
    wcel
    #
    @8
    wph
    @11
    @17
    evlslem1.s
    cS
    cT
    evlslem1.t
    crngmgp
    syl
    adantr
    wph
    @8
    simpr
    wph
    cI
    cC
    cG
    wf
    @8
    evlslem1.g
    adantr
    wph
    cI
    cvv
    wcel
    @8
    evlslem1.i
    adantr
    psrbagev2
    #
    cC
    cS
    c.x
    @2
    @3
    evlslem1.c
    evlslem1.m
    ringcl
    syl3anc
    @5
    eqid
    fmptd
    wph
    @5
    cvv
    wcel
    #
    @5
    wfun
    #
    @6
    cvv
    wcel
    cY
    cR
    c0g
    cfv
    #
    csupp
    co
    #
    cfn
    wcel
    @5
    @6
    csupp
    co
    @22
    wss
    @7
    wph
    cD
    cvv
    wcel
    @19
    wph
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    cI
    cmap
    co
    cD
    cvv
    evlslem1.d
    wph
    cn0
    cI
    cmap
    ovexd
    rabexd
    vb
    cD
    @4
    cvv
    mptexg
    syl
    @20
    wph
    vb
    cD
    @4
    funmpt
    a1i
    wph
    cS
    c0g
    fvexd
    #
    wph
    cY
    @21
    wph
    cB
    cP
    cR
    cY
    cI
    ccrg
    @21
    evlslem1.p
    evlslem1.b
    @21
    eqid
    #
    evlslem6.y
    evlslem1.r
    mplelsfi
    fsuppimpd
    wph
    vb
    vx
    @2
    @3
    cD
    cC
    @22
    c.x
    cvv
    cvv
    @6
    @6
    wph
    vb
    @1
    cD
    cvv
    cF
    @22
    cvv
    @21
    @6
    wph
    @22
    vb
    cD
    @1
    cmpt
    #
    @21
    csupp
    co
    #
    wceq
    @26
    @22
    wss
    wph
    cY
    @25
    @21
    csupp
    wph
    vb
    cD
    cK
    cY
    @15
    feqmptd
    oveq1d
    @26
    @22
    eqimss2
    syl
    wph
    @14
    cF
    cR
    cS
    cghm
    co
    wcel
    @21
    cF
    cfv
    @6
    wceq
    evlslem1.f
    cR
    cS
    cF
    rhmghm
    cR
    cS
    cF
    @21
    @6
    @24
    @6
    eqid
    #
    ghmid
    3syl
    @9
    @0
    cY
    fvexd
    wph
    cR
    c0g
    fvexd
    suppssfv
    wph
    @10
    vx
    cv
    #
    cC
    wcel
    @6
    @28
    c.x
    co
    @6
    wceq
    @12
    cC
    cS
    c.x
    @28
    @6
    evlslem1.c
    evlslem1.m
    @27
    ringlz
    sylan
    @9
    @1
    cF
    fvexd
    @18
    @23
    suppssov1
    @22
    @5
    cvv
    cvv
    @6
    suppssfifsupp
    syl32anc
    jca
end
