include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "clt.mm"
include "cmin.mm"
include "co.mm"
include "w3a.mm"
include "wrex.mm"
include "c0.mm"
include "wceq.mm"
include "cmpt.mm"
include "nfeq1.mm"
include "nfan.mm"
include "eqid.mm"
include "cr.mm"
include "wcel.mm"
include "adantlr.mm"
include "ccld.mm"
include "adantr.mm"
include "crp.mm"
include "simpr.mm"
include "stoweidlem18.mm"
include "wne.mm"
include "cdif.mm"
include "crab.mm"
include "nfcv.mm"
include "nfne.mm"
include "ccmp.mm"
include "wss.mm"
include "caddc.mm"
include "3adant1r.mm"
include "cmul.mm"
include "cin.mm"
include "c3.mm"
include "cdiv.mm"
include "stoweidlem57.mm"
include "pm2.61dane.mm"

theorem stoweidlem58
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cJ: class J
  let cK: class K
  let vr: setvar r
  let vq: setvar q
  let va: setvar a
  let ve: setvar e
  let vh: setvar h
  let vw: setvar w
  let vk: setvar k
  assume stoweidlem58.1: |- F/_ t D
  assume stoweidlem58.2: |- F/_ t U
  assume stoweidlem58.3: |- F/ t ph
  assume stoweidlem58.4: |- K = ( topGen ` ran (,) )
  assume stoweidlem58.5: |- T = U. J
  assume stoweidlem58.6: |- C = ( J Cn K )
  assume stoweidlem58.7: |- ( ph -> J e. Comp )
  assume stoweidlem58.8: |- ( ph -> A C_ C )
  assume stoweidlem58.9: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem58.10: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem58.11: |- ( ( ph /\ a e. RR ) -> ( t e. T |-> a ) e. A )
  assume stoweidlem58.12: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. q e. A ( q ` r ) =/= ( q ` t ) )
  assume stoweidlem58.13: |- ( ph -> B e. ( Clsd ` J ) )
  assume stoweidlem58.14: |- ( ph -> D e. ( Clsd ` J ) )
  assume stoweidlem58.15: |- ( ph -> ( B i^i D ) = (/) )
  assume stoweidlem58.16: |- U = ( T \ B )
  assume stoweidlem58.17: |- ( ph -> E e. RR+ )
  assume stoweidlem58.18: |- ( ph -> E < ( 1 / 3 ) )

  disjoint a f
  disjoint a r
  disjoint a t
  disjoint A a
  disjoint f r
  disjoint f t
  disjoint A f
  disjoint r t
  disjoint A r
  disjoint A t
  disjoint a q
  disjoint f q
  disjoint q r
  disjoint q t
  disjoint A q
  disjoint D a
  disjoint D f
  disjoint D r
  disjoint T a
  disjoint T f
  disjoint T r
  disjoint T t
  disjoint U a
  disjoint U f
  disjoint U r
  disjoint a ph
  disjoint f ph
  disjoint ph r
  disjoint f g
  disjoint g r
  disjoint g t
  disjoint A g
  disjoint E f
  disjoint E g
  disjoint E r
  disjoint E t
  disjoint f x
  disjoint g x
  disjoint t x
  disjoint A x
  disjoint B f
  disjoint B g
  disjoint B r
  disjoint J f
  disjoint J g
  disjoint J r
  disjoint J t
  disjoint g q
  disjoint D g
  disjoint T g
  disjoint U g
  disjoint g ph
  disjoint D q
  disjoint T q
  disjoint U q
  disjoint ph q
  disjoint K t
  disjoint B x
  disjoint D x
  disjoint E x
  disjoint T x
  disjoint a e
  disjoint e f
  disjoint e r
  disjoint e t
  disjoint A e
  disjoint D e
  disjoint T e
  disjoint U e
  disjoint e ph
  disjoint e g
  disjoint e h
  disjoint e w
  disjoint f h
  disjoint f w
  disjoint g h
  disjoint g w
  disjoint h r
  disjoint h t
  disjoint h w
  disjoint A h
  disjoint r w
  disjoint t w
  disjoint A w
  disjoint E e
  disjoint E h
  disjoint E w
  disjoint h x
  disjoint B w
  disjoint J h
  disjoint J w
  disjoint D h
  disjoint D w
  disjoint T h
  disjoint T w
  disjoint U h
  disjoint U w
  disjoint h ph
  disjoint ph w
  disjoint k x
  assert |- ( ph -> E. x e. A ( A. t e. T ( 0 <_ ( x ` t ) /\ ( x ` t ) <_ 1 ) /\ A. t e. D ( x ` t ) < E /\ A. t e. B ( 1 - E ) < ( x ` t ) ) )

  proof
    wph
    cc0
    vt
    cv
    #
    vx
    cv
    cfv
    #
    cle
    wbr
    @1
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    @1
    cE
    clt
    wbr
    vt
    cD
    wral
    c1
    cE
    cmin
    co
    @1
    clt
    wbr
    vt
    cB
    wral
    w3a
    vx
    cA
    wrex
    cD
    c0
    wph
    cD
    c0
    wceq
    #
    wa
    vx
    vt
    cA
    cB
    cD
    cT
    cE
    vt
    cT
    c1
    cmpt
    #
    cJ
    va
    stoweidlem58.1
    wph
    @2
    vt
    stoweidlem58.3
    vt
    cD
    c0
    stoweidlem58.1
    nfeq1
    nfan
    @3
    eqid
    stoweidlem58.5
    wph
    va
    cv
    #
    cr
    wcel
    #
    vt
    cT
    @4
    cmpt
    cA
    wcel
    #
    @2
    stoweidlem58.11
    adantlr
    wph
    cB
    cJ
    ccld
    cfv
    #
    wcel
    #
    @2
    stoweidlem58.13
    adantr
    wph
    cE
    crp
    wcel
    #
    @2
    stoweidlem58.17
    adantr
    wph
    @2
    simpr
    stoweidlem18
    wph
    cD
    c0
    wne
    #
    wa
    vx
    vw
    vt
    cA
    cB
    cC
    cD
    cT
    cU
    ve
    vf
    vg
    vh
    cE
    cJ
    cK
    cc0
    @0
    vh
    cv
    cfv
    #
    cle
    wbr
    @11
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    #
    @11
    ve
    cv
    #
    clt
    wbr
    vt
    vw
    cv
    wral
    c1
    @13
    cmin
    co
    @11
    clt
    wbr
    vt
    cT
    cU
    cdif
    wral
    w3a
    vh
    cA
    wrex
    ve
    crp
    wral
    vw
    cJ
    crab
    #
    @12
    vh
    cA
    crab
    #
    vr
    vq
    va
    stoweidlem58.1
    stoweidlem58.2
    wph
    @10
    vt
    stoweidlem58.3
    vt
    cD
    c0
    stoweidlem58.1
    vt
    c0
    nfcv
    nfne
    nfan
    @15
    eqid
    @14
    eqid
    stoweidlem58.4
    stoweidlem58.5
    stoweidlem58.6
    stoweidlem58.16
    wph
    cJ
    ccmp
    wcel
    @10
    stoweidlem58.7
    adantr
    wph
    cA
    cC
    wss
    @10
    stoweidlem58.8
    adantr
    wph
    vf
    cv
    #
    cA
    wcel
    #
    vg
    cv
    #
    cA
    wcel
    #
    vt
    cT
    @0
    @16
    cfv
    #
    @0
    @18
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    @10
    stoweidlem58.9
    3adant1r
    wph
    @17
    @19
    vt
    cT
    @20
    @21
    cmul
    co
    cmpt
    cA
    wcel
    @10
    stoweidlem58.10
    3adant1r
    wph
    @5
    @6
    @10
    stoweidlem58.11
    adantlr
    wph
    vr
    cv
    #
    cT
    wcel
    @0
    cT
    wcel
    @22
    @0
    wne
    w3a
    @22
    vq
    cv
    #
    cfv
    @0
    @23
    cfv
    wne
    vq
    cA
    wrex
    @10
    stoweidlem58.12
    adantlr
    wph
    @8
    @10
    stoweidlem58.13
    adantr
    wph
    cD
    @7
    wcel
    @10
    stoweidlem58.14
    adantr
    wph
    cB
    cD
    cin
    c0
    wceq
    @10
    stoweidlem58.15
    adantr
    wph
    @10
    simpr
    wph
    @9
    @10
    stoweidlem58.17
    adantr
    wph
    cE
    c1
    c3
    cdiv
    co
    clt
    wbr
    @10
    stoweidlem58.18
    adantr
    stoweidlem57
    pm2.61dane
end
