include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cc0.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cle.mm"
include "wceq.mm"
include "w3a.mm"
include "cfn.mm"
include "wss.mm"
include "cuni.mm"
include "stoweidlem50.mm"
include "crab.mm"
include "cmpt.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "nfrab1.mm"
include "nfeq2.mm"
include "nfrex.mm"
include "nfss.mm"
include "nfdif.mm"
include "nf3an.mm"
include "nfre1.mm"
include "eqid.mm"
include "cvv.mm"
include "ccn.mm"
include "ctop.mm"
include "ccmp.mm"
include "cmptop.mm"
include "syl.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "retop.mm"
include "eqeltri.mm"
include "cnfex.mm"
include "sylancl.mm"
include "syl6sseq.mm"
include "ssexd.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "c0.mm"
include "wne.mm"
include "stoweidlem35.mm"
include "exlimddv.mm"
include "cdiv.mm"
include "csu.mm"
include "cmul.mm"
include "nfral.mm"
include "nff.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "caddc.mm"
include "3adant1r.mm"
include "cr.mm"
include "adantlr.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "sseldd.mm"
include "stoweidlem44.mm"
include "ex.mm"
include "exlimdvv.mm"
include "mpd.mm"

theorem stoweidlem53
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cQ: class Q
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cJ: class J
  let cK: class K
  let cW: class W
  let cZ: class Z
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vi: setvar i
  let vm: setvar m
  let vy: setvar y
  let vu: setvar u
  let vk: setvar k
  assume stoweidlem53.1: |- F/_ t U
  assume stoweidlem53.2: |- F/ t ph
  assume stoweidlem53.3: |- K = ( topGen ` ran (,) )
  assume stoweidlem53.4: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem53.5: |- W = { w e. J | E. h e. Q w = { t e. T | 0 < ( h ` t ) } }
  assume stoweidlem53.6: |- T = U. J
  assume stoweidlem53.7: |- C = ( J Cn K )
  assume stoweidlem53.8: |- ( ph -> J e. Comp )
  assume stoweidlem53.9: |- ( ph -> A C_ C )
  assume stoweidlem53.10: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem53.11: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem53.12: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem53.13: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. q e. A ( q ` r ) =/= ( q ` t ) )
  assume stoweidlem53.14: |- ( ph -> U e. J )
  assume stoweidlem53.15: |- ( ph -> ( T \ U ) =/= (/) )
  assume stoweidlem53.16: |- ( ph -> Z e. U )

  disjoint f g
  disjoint f h
  disjoint f q
  disjoint f t
  disjoint T f
  disjoint g h
  disjoint g q
  disjoint g t
  disjoint T g
  disjoint h q
  disjoint h t
  disjoint T h
  disjoint q t
  disjoint T q
  disjoint T t
  disjoint f r
  disjoint q r
  disjoint r t
  disjoint T r
  disjoint f x
  disjoint q x
  disjoint t x
  disjoint T x
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A q
  disjoint A t
  disjoint Q f
  disjoint Q g
  disjoint Q q
  disjoint U f
  disjoint U g
  disjoint U h
  disjoint U q
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint Z q
  disjoint Z t
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph q
  disjoint g w
  disjoint h w
  disjoint t w
  disjoint T w
  disjoint W g
  disjoint J h
  disjoint J t
  disjoint J w
  disjoint p q
  disjoint p t
  disjoint T p
  disjoint A p
  disjoint U p
  disjoint Z p
  disjoint A r
  disjoint U r
  disjoint ph r
  disjoint K t
  disjoint Q w
  disjoint U w
  disjoint ph w
  disjoint A x
  disjoint Q x
  disjoint U x
  disjoint Z x
  disjoint ph x
  disjoint f i
  disjoint f m
  disjoint f y
  disjoint g i
  disjoint g m
  disjoint g y
  disjoint h i
  disjoint h m
  disjoint h y
  disjoint i m
  disjoint i q
  disjoint i t
  disjoint i y
  disjoint T i
  disjoint m q
  disjoint m t
  disjoint m y
  disjoint T m
  disjoint q y
  disjoint t y
  disjoint T y
  disjoint i r
  disjoint m r
  disjoint i x
  disjoint m x
  disjoint A m
  disjoint Q i
  disjoint Q m
  disjoint Q y
  disjoint U i
  disjoint U m
  disjoint U y
  disjoint Z m
  disjoint Z y
  disjoint i ph
  disjoint m ph
  disjoint ph y
  disjoint i w
  disjoint m w
  disjoint W i
  disjoint W m
  disjoint h u
  disjoint i u
  disjoint m u
  disjoint q u
  disjoint t u
  disjoint T u
  disjoint u w
  disjoint J u
  disjoint m p
  disjoint p y
  disjoint Q u
  disjoint U u
  disjoint W u
  disjoint ph u
  disjoint k x
  assert |- ( ph -> E. p e. A ( A. t e. T ( 0 <_ ( p ` t ) /\ ( p ` t ) <_ 1 ) /\ ( p ` Z ) = 0 /\ A. t e. ( T \ U ) 0 < ( p ` t ) ) )

  proof
    wph
    vm
    cv
    #
    cn
    wcel
    #
    c1
    @0
    cfz
    co
    #
    cQ
    vq
    cv
    #
    wf
    #
    cc0
    vt
    cv
    #
    vi
    cv
    @3
    cfv
    cfv
    clt
    wbr
    #
    vi
    @2
    wrex
    #
    vt
    cT
    cU
    cdif
    #
    wral
    #
    wa
    #
    wa
    #
    vq
    wex
    vm
    wex
    #
    cc0
    @5
    vp
    cv
    #
    cfv
    #
    cle
    wbr
    @14
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    cZ
    @13
    cfv
    cc0
    wceq
    cc0
    @14
    clt
    wbr
    vt
    @8
    wral
    w3a
    vp
    cA
    wrex
    #
    wph
    vu
    cv
    #
    cfn
    wcel
    #
    @16
    cW
    wss
    #
    @8
    @16
    cuni
    #
    wss
    #
    w3a
    #
    @12
    vu
    wph
    vx
    vw
    vu
    vt
    cA
    cC
    cQ
    cT
    cU
    vf
    vg
    vh
    cJ
    cK
    cW
    cZ
    vr
    vq
    stoweidlem53.1
    stoweidlem53.2
    stoweidlem53.3
    stoweidlem53.4
    stoweidlem53.5
    stoweidlem53.6
    stoweidlem53.7
    stoweidlem53.8
    stoweidlem53.9
    stoweidlem53.10
    stoweidlem53.11
    stoweidlem53.12
    stoweidlem53.13
    stoweidlem53.14
    stoweidlem53.16
    stoweidlem50
    wph
    @21
    wa
    vw
    vt
    cA
    cQ
    cT
    cU
    vh
    vi
    vm
    vw
    @16
    vw
    cv
    #
    cc0
    @5
    vh
    cv
    #
    cfv
    #
    clt
    wbr
    #
    vt
    cT
    crab
    #
    wceq
    #
    vh
    cQ
    crab
    cmpt
    #
    cJ
    cW
    @16
    cZ
    vq
    wph
    @21
    vt
    stoweidlem53.2
    @17
    @18
    @20
    vt
    @17
    vt
    nfv
    vt
    @16
    cW
    vt
    @16
    nfcv
    vt
    cW
    @27
    vh
    cQ
    wrex
    #
    vw
    cJ
    crab
    #
    stoweidlem53.5
    @29
    vt
    vw
    cJ
    @27
    vt
    vh
    cQ
    vt
    cQ
    cZ
    @23
    cfv
    cc0
    wceq
    #
    cc0
    @24
    cle
    wbr
    @24
    c1
    cle
    wbr
    wa
    #
    vt
    cT
    wral
    #
    wa
    #
    vh
    cA
    crab
    stoweidlem53.4
    @34
    vt
    vh
    cA
    @31
    @33
    vt
    @31
    vt
    nfv
    @32
    vt
    cT
    nfra1
    nfan
    vt
    cA
    nfcv
    nfrab
    nfcxfr
    #
    vt
    @22
    @26
    @25
    vt
    cT
    nfrab1
    nfeq2
    nfrex
    vt
    cJ
    nfcv
    nfrab
    nfcxfr
    nfss
    vt
    @8
    @19
    vt
    cT
    cU
    vt
    cT
    nfcv
    stoweidlem53.1
    nfdif
    vt
    @19
    nfcv
    nfss
    nf3an
    nfan
    wph
    @21
    vw
    wph
    vw
    nfv
    @17
    @18
    @20
    vw
    @17
    vw
    nfv
    vw
    @16
    cW
    vw
    @16
    nfcv
    vw
    cW
    @30
    stoweidlem53.5
    @29
    vw
    cJ
    nfrab1
    nfcxfr
    nfss
    @20
    vw
    nfv
    nf3an
    nfan
    wph
    @21
    vh
    wph
    vh
    nfv
    @17
    @18
    @20
    vh
    @17
    vh
    nfv
    vh
    @16
    cW
    vh
    @16
    nfcv
    vh
    cW
    @30
    stoweidlem53.5
    @29
    vh
    vw
    cJ
    @27
    vh
    cQ
    nfre1
    vh
    cJ
    nfcv
    nfrab
    nfcxfr
    nfss
    @20
    vh
    nfv
    nf3an
    nfan
    stoweidlem53.4
    stoweidlem53.5
    @28
    eqid
    wph
    cA
    cvv
    wcel
    @21
    wph
    cA
    cJ
    cK
    ccn
    co
    #
    cvv
    wph
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    @36
    cvv
    wcel
    wph
    cJ
    ccmp
    wcel
    @37
    stoweidlem53.8
    cJ
    cmptop
    syl
    cK
    cioo
    crn
    ctg
    cfv
    ctop
    stoweidlem53.3
    retop
    eqeltri
    cJ
    cK
    cnfex
    sylancl
    wph
    cA
    cC
    @36
    stoweidlem53.9
    stoweidlem53.7
    syl6sseq
    #
    ssexd
    adantr
    wph
    @17
    @18
    @20
    simpr1
    wph
    @17
    @18
    @20
    simpr2
    wph
    @17
    @18
    @20
    simpr3
    wph
    @8
    c0
    wne
    @21
    stoweidlem53.15
    adantr
    stoweidlem35
    exlimddv
    wph
    @11
    @15
    vm
    vq
    wph
    @11
    @15
    wph
    @11
    wa
    vx
    vt
    cA
    vt
    cT
    c1
    @0
    cdiv
    co
    @2
    @5
    vy
    cv
    @3
    cfv
    cfv
    vy
    csu
    cmul
    co
    cmpt
    #
    cQ
    cT
    cU
    vf
    vg
    vh
    vy
    vi
    @3
    cJ
    cK
    @0
    cZ
    vp
    wph
    @11
    vi
    wph
    vi
    nfv
    @1
    @10
    vi
    @1
    vi
    nfv
    @4
    @9
    vi
    @4
    vi
    nfv
    @7
    vi
    vt
    @8
    vi
    @8
    nfcv
    @6
    vi
    @2
    nfre1
    nfral
    nfan
    nfan
    nfan
    wph
    @11
    vt
    stoweidlem53.2
    @1
    @10
    vt
    @1
    vt
    nfv
    @4
    @9
    vt
    vt
    @2
    cQ
    @3
    vt
    @3
    nfcv
    vt
    @2
    nfcv
    @35
    nff
    @7
    vt
    @8
    nfra1
    nfan
    nfan
    nfan
    stoweidlem53.3
    stoweidlem53.4
    @39
    eqid
    wph
    @1
    @10
    simprl
    wph
    @1
    @4
    @9
    simprrl
    wph
    @1
    @4
    @9
    simprrr
    stoweidlem53.6
    wph
    cA
    @36
    wss
    @11
    @38
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
    @40
    cfv
    #
    @5
    @42
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    @11
    stoweidlem53.10
    3adant1r
    wph
    @41
    @43
    vt
    cT
    @44
    @45
    cmul
    co
    cmpt
    cA
    wcel
    @11
    stoweidlem53.11
    3adant1r
    wph
    vx
    cv
    #
    cr
    wcel
    vt
    cT
    @46
    cmpt
    cA
    wcel
    @11
    stoweidlem53.12
    adantlr
    wph
    cZ
    cT
    wcel
    @11
    wph
    cU
    cT
    cZ
    wph
    cU
    cJ
    wcel
    #
    cU
    cT
    wss
    stoweidlem53.14
    @47
    cU
    cJ
    cuni
    cT
    cU
    cJ
    elssuni
    stoweidlem53.6
    syl6sseqr
    syl
    stoweidlem53.16
    sseldd
    adantr
    stoweidlem44
    ex
    exlimdvv
    mpd
end
