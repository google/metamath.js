include "cv.mm"
include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cfv.mm"
include "cle.mm"
include "wa.mm"
include "wral.mm"
include "wceq.mm"
include "cdif.mm"
include "w3a.mm"
include "wex.mm"
include "wss.mm"
include "cmin.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "eqid.mm"
include "stoweidlem55.mm"
include "df-rex.mm"
include "sylib.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr3.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "ccmp.mm"
include "3ad2ant1.mm"
include "ccn.mm"
include "sselda.mm"
include "syl6eleq.mm"
include "3adant3.mm"
include "simp3.mm"
include "stoweidlem28.mm"
include "syl3anc.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simplrl.mm"
include "simprr1.mm"
include "adantr.mm"
include "simprr2.mm"
include "simpr3.mm"
include "3jca.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "c2.mm"
include "cdiv.mm"
include "nfan.mm"
include "nfcv.mm"
include "caddc.mm"
include "cmpt.mm"
include "3adant1r.mm"
include "cmul.mm"
include "cr.mm"
include "adantlr.mm"
include "simpr3l.mm"
include "simp3r1.mm"
include "adantl.mm"
include "simp3r2.mm"
include "simp3r3.mm"
include "stoweidlem52.mm"
include "exlimdvv.mm"

theorem stoweidlem56
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cJ: class J
  let cK: class K
  let cZ: class Z
  let vr: setvar r
  let vq: setvar q
  let vd: setvar d
  let vp: setvar p
  let vh: setvar h
  let vw: setvar w
  let vk: setvar k
  assume stoweidlem56.1: |- F/_ t U
  assume stoweidlem56.2: |- F/ t ph
  assume stoweidlem56.3: |- K = ( topGen ` ran (,) )
  assume stoweidlem56.4: |- ( ph -> J e. Comp )
  assume stoweidlem56.5: |- T = U. J
  assume stoweidlem56.6: |- C = ( J Cn K )
  assume stoweidlem56.7: |- ( ph -> A C_ C )
  assume stoweidlem56.8: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem56.9: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem56.10: |- ( ( ph /\ y e. RR ) -> ( t e. T |-> y ) e. A )
  assume stoweidlem56.11: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. q e. A ( q ` r ) =/= ( q ` t ) )
  assume stoweidlem56.12: |- ( ph -> U e. J )
  assume stoweidlem56.13: |- ( ph -> Z e. U )

  disjoint e f
  disjoint e g
  disjoint e t
  disjoint A e
  disjoint f g
  disjoint f t
  disjoint A f
  disjoint g t
  disjoint A g
  disjoint A t
  disjoint e v
  disjoint e x
  disjoint t v
  disjoint t x
  disjoint v x
  disjoint A v
  disjoint A x
  disjoint e y
  disjoint f y
  disjoint t y
  disjoint A y
  disjoint J g
  disjoint J t
  disjoint T e
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint U e
  disjoint U f
  disjoint U g
  disjoint Z e
  disjoint Z f
  disjoint Z g
  disjoint Z t
  disjoint e ph
  disjoint f ph
  disjoint g ph
  disjoint f q
  disjoint g q
  disjoint q t
  disjoint A q
  disjoint f r
  disjoint g r
  disjoint q r
  disjoint r t
  disjoint A r
  disjoint q y
  disjoint T q
  disjoint T y
  disjoint U q
  disjoint U y
  disjoint Z q
  disjoint Z y
  disjoint ph q
  disjoint ph y
  disjoint r y
  disjoint T r
  disjoint U r
  disjoint ph r
  disjoint K t
  disjoint J v
  disjoint T v
  disjoint T x
  disjoint U v
  disjoint U x
  disjoint Z v
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d p
  disjoint d t
  disjoint A d
  disjoint e p
  disjoint f p
  disjoint g p
  disjoint p t
  disjoint A p
  disjoint d v
  disjoint d x
  disjoint p v
  disjoint p x
  disjoint d y
  disjoint p y
  disjoint J d
  disjoint J p
  disjoint T d
  disjoint T p
  disjoint U d
  disjoint U p
  disjoint Z d
  disjoint Z p
  disjoint d ph
  disjoint p ph
  disjoint f h
  disjoint g h
  disjoint h q
  disjoint h t
  disjoint A h
  disjoint g w
  disjoint h w
  disjoint t w
  disjoint A w
  disjoint h y
  disjoint J h
  disjoint J w
  disjoint T h
  disjoint U h
  disjoint Z h
  disjoint h ph
  disjoint p q
  disjoint w y
  disjoint T w
  disjoint U w
  disjoint Z w
  disjoint ph w
  disjoint k x
  assert |- ( ph -> E. v e. J ( ( Z e. v /\ v C_ U ) /\ A. e e. RR+ E. x e. A ( A. t e. T ( 0 <_ ( x ` t ) /\ ( x ` t ) <_ 1 ) /\ A. t e. v ( x ` t ) < e /\ A. t e. ( T \ U ) ( 1 - e ) < ( x ` t ) ) ) )

  proof
    wph
    vd
    cv
    #
    crp
    wcel
    #
    @0
    c1
    clt
    wbr
    #
    vp
    cv
    #
    cA
    wcel
    #
    cc0
    vt
    cv
    #
    @3
    cfv
    #
    cle
    wbr
    @6
    c1
    cle
    wbr
    wa
    #
    vt
    cT
    wral
    #
    cZ
    @3
    cfv
    cc0
    wceq
    #
    @0
    @6
    cle
    wbr
    #
    vt
    cT
    cU
    cdif
    #
    wral
    #
    w3a
    #
    wa
    #
    w3a
    #
    vd
    wex
    #
    vp
    wex
    #
    cZ
    vv
    cv
    #
    wcel
    @18
    cU
    wss
    wa
    cc0
    @5
    vx
    cv
    cfv
    #
    cle
    wbr
    @19
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    @19
    ve
    cv
    #
    clt
    wbr
    vt
    @18
    wral
    c1
    @20
    cmin
    co
    @19
    clt
    wbr
    vt
    @11
    wral
    w3a
    vx
    cA
    wrex
    ve
    crp
    wral
    wa
    vv
    cJ
    wrex
    #
    wph
    @4
    @8
    @9
    cc0
    @6
    clt
    wbr
    #
    vt
    @11
    wral
    #
    w3a
    #
    wa
    #
    vp
    wex
    #
    @17
    wph
    @24
    vp
    cA
    wrex
    @26
    wph
    vy
    vw
    vt
    cA
    cC
    cZ
    vh
    cv
    #
    cfv
    cc0
    wceq
    cc0
    @5
    @27
    cfv
    #
    cle
    wbr
    @28
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    wa
    vh
    cA
    crab
    #
    cT
    cU
    vf
    vg
    vh
    cJ
    cK
    vw
    cv
    cc0
    @28
    clt
    wbr
    vt
    cT
    crab
    wceq
    vh
    @29
    wrex
    vw
    cJ
    crab
    #
    cZ
    vr
    vq
    vp
    stoweidlem56.1
    stoweidlem56.2
    stoweidlem56.3
    stoweidlem56.4
    stoweidlem56.5
    stoweidlem56.6
    stoweidlem56.7
    stoweidlem56.8
    stoweidlem56.9
    stoweidlem56.10
    stoweidlem56.11
    stoweidlem56.12
    stoweidlem56.13
    @29
    eqid
    @30
    eqid
    stoweidlem55
    @24
    vp
    cA
    df-rex
    sylib
    wph
    @25
    @16
    vp
    wph
    @25
    @16
    wph
    @25
    wa
    #
    @1
    @2
    @12
    w3a
    #
    vd
    wex
    #
    @16
    @31
    wph
    @4
    @23
    @33
    wph
    @25
    simpl
    wph
    @4
    @24
    simprl
    @8
    @9
    @23
    @4
    wph
    simprr3
    wph
    @4
    @23
    w3a
    vt
    @3
    cT
    cU
    cJ
    cK
    vd
    stoweidlem56.1
    wph
    @4
    @23
    vt
    stoweidlem56.2
    @4
    vt
    nfv
    #
    @22
    vt
    @11
    nfra1
    nf3an
    stoweidlem56.3
    stoweidlem56.5
    wph
    @4
    cJ
    ccmp
    wcel
    @23
    stoweidlem56.4
    3ad2ant1
    wph
    @4
    @3
    cJ
    cK
    ccn
    co
    #
    wcel
    @23
    wph
    @4
    wa
    @3
    cC
    @35
    wph
    cA
    cC
    @3
    stoweidlem56.7
    sselda
    stoweidlem56.6
    syl6eleq
    3adant3
    wph
    @4
    @23
    simp3
    wph
    @4
    cU
    cJ
    wcel
    #
    @23
    stoweidlem56.12
    3ad2ant1
    stoweidlem28
    syl3anc
    @31
    @32
    @15
    vd
    @31
    @32
    @15
    @31
    @32
    wa
    #
    @1
    @2
    @14
    @31
    @1
    @2
    @12
    simpr1
    @31
    @1
    @2
    @12
    simpr2
    @37
    @4
    @13
    wph
    @4
    @24
    @32
    simplrl
    @37
    @8
    @9
    @12
    @31
    @8
    @32
    @8
    @9
    @23
    @4
    wph
    simprr1
    adantr
    @31
    @9
    @32
    @8
    @9
    @23
    @4
    wph
    simprr2
    adantr
    @31
    @1
    @2
    @12
    simpr3
    3jca
    jca
    3jca
    ex
    eximdv
    mpd
    ex
    eximdv
    mpd
    wph
    @15
    @21
    vp
    vd
    wph
    @15
    @21
    wph
    @15
    wa
    vx
    vv
    vt
    cA
    cC
    @0
    @3
    cT
    cU
    ve
    vf
    vg
    cJ
    cK
    @6
    @0
    c2
    cdiv
    co
    clt
    wbr
    vt
    cT
    crab
    #
    cZ
    vy
    stoweidlem56.1
    wph
    @15
    vt
    stoweidlem56.2
    @1
    @2
    @14
    vt
    @1
    vt
    nfv
    @2
    vt
    nfv
    @4
    @13
    vt
    @34
    @8
    @9
    @12
    vt
    @7
    vt
    cT
    nfra1
    @9
    vt
    nfv
    @10
    vt
    @11
    nfra1
    nf3an
    nfan
    nf3an
    nfan
    vt
    @3
    nfcv
    stoweidlem56.3
    @38
    eqid
    stoweidlem56.5
    stoweidlem56.6
    wph
    cA
    cC
    wss
    @15
    stoweidlem56.7
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
    @5
    @39
    cfv
    #
    @5
    @41
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    @15
    stoweidlem56.8
    3adant1r
    wph
    @40
    @42
    vt
    cT
    @43
    @44
    cmul
    co
    cmpt
    cA
    wcel
    @15
    stoweidlem56.9
    3adant1r
    wph
    vy
    cv
    #
    cr
    wcel
    vt
    cT
    @45
    cmpt
    cA
    wcel
    @15
    stoweidlem56.10
    adantlr
    wph
    @1
    @2
    @14
    simpr1
    wph
    @1
    @2
    @14
    simpr2
    wph
    @36
    @15
    stoweidlem56.12
    adantr
    wph
    cZ
    cU
    wcel
    @15
    stoweidlem56.13
    adantr
    @4
    @13
    @1
    @2
    wph
    simpr3l
    @15
    @8
    wph
    @8
    @9
    @12
    @4
    @1
    @2
    simp3r1
    adantl
    @15
    @9
    wph
    @8
    @9
    @12
    @4
    @1
    @2
    simp3r2
    adantl
    @15
    @12
    wph
    @8
    @9
    @12
    @4
    @1
    @2
    simp3r3
    adantl
    stoweidlem52
    ex
    exlimdvv
    mpd
end
