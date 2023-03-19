include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wral.mm"
include "clt.mm"
include "cmin.mm"
include "co.mm"
include "cdif.mm"
include "w3a.mm"
include "wrex.mm"
include "crp.mm"
include "c2.mm"
include "cdiv.mm"
include "nfcv.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "rexrd.mm"
include "ccn.mm"
include "syl6sseq.mm"
include "sseldd.mm"
include "rfcnpre2.mm"
include "crab.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "rpgt0d.mm"
include "2pos.mm"
include "divgt0d.mm"
include "eqbrtrd.mm"
include "nffv.mm"
include "nfbr.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrabf.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "wn.mm"
include "wf.mm"
include "fcnre.mm"
include "adantr.mm"
include "rabeq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "simprd.mm"
include "wb.mm"
include "halfpos.mm"
include "mpbid.mm"
include "lttrd.mm"
include "ad2antrr.mm"
include "anim1i.mm"
include "eldif.mm"
include "sylibr.mm"
include "rsp.mm"
include "sylc.mm"
include "lensymd.mm"
include "condan.mm"
include "ex.mm"
include "ssrd.mm"
include "cmpt.mm"
include "nfv.mm"
include "nfan.mm"
include "nfra1.mm"
include "nf3an.mm"
include "eqid.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "simplr.mm"
include "simplll.mm"
include "sselda.mm"
include "syl2anc.mm"
include "sylan.mm"
include "caddc.mm"
include "syl3an1.mm"
include "cmul.mm"
include "simpllr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "stoweidlem41.mm"
include "adantlr.mm"
include "3adant1r.mm"
include "simpr.mm"
include "stoweidlem49.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "jca31.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "raleqf.mm"
include "3anbi2d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "rspcev.mm"

theorem stoweidlem52
  let wph: wff ph
  let vx: setvar x
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cJ: class J
  let cK: class K
  let cV: class V
  let cZ: class Z
  let va: setvar a
  let vy: setvar y
  let vk: setvar k
  assume stoweidlem52.1: |- F/_ t U
  assume stoweidlem52.2: |- F/ t ph
  assume stoweidlem52.3: |- F/_ t P
  assume stoweidlem52.4: |- K = ( topGen ` ran (,) )
  assume stoweidlem52.5: |- V = { t e. T | ( P ` t ) < ( D / 2 ) }
  assume stoweidlem52.7: |- T = U. J
  assume stoweidlem52.8: |- C = ( J Cn K )
  assume stoweidlem52.9: |- ( ph -> A C_ C )
  assume stoweidlem52.10: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem52.11: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem52.12: |- ( ( ph /\ a e. RR ) -> ( t e. T |-> a ) e. A )
  assume stoweidlem52.13: |- ( ph -> D e. RR+ )
  assume stoweidlem52.14: |- ( ph -> D < 1 )
  assume stoweidlem52.15: |- ( ph -> U e. J )
  assume stoweidlem52.16: |- ( ph -> Z e. U )
  assume stoweidlem52.17: |- ( ph -> P e. A )
  assume stoweidlem52.18: |- ( ph -> A. t e. T ( 0 <_ ( P ` t ) /\ ( P ` t ) <_ 1 ) )
  assume stoweidlem52.19: |- ( ph -> ( P ` Z ) = 0 )
  assume stoweidlem52.20: |- ( ph -> A. t e. ( T \ U ) D <_ ( P ` t ) )

  disjoint a e
  disjoint a t
  disjoint e t
  disjoint A a
  disjoint A t
  disjoint D a
  disjoint D t
  disjoint T a
  disjoint T t
  disjoint U a
  disjoint V a
  disjoint V e
  disjoint a ph
  disjoint e ph
  disjoint e f
  disjoint e g
  disjoint f g
  disjoint f t
  disjoint g t
  disjoint e v
  disjoint e x
  disjoint t v
  disjoint t x
  disjoint v x
  disjoint A f
  disjoint A g
  disjoint D f
  disjoint D g
  disjoint P f
  disjoint P g
  disjoint T f
  disjoint T g
  disjoint U f
  disjoint U g
  disjoint V f
  disjoint V g
  disjoint f ph
  disjoint g ph
  disjoint Z t
  disjoint Z v
  disjoint A v
  disjoint J v
  disjoint T v
  disjoint T x
  disjoint U v
  disjoint U x
  disjoint V v
  disjoint V x
  disjoint A x
  disjoint a y
  disjoint e y
  disjoint t y
  disjoint A y
  disjoint T y
  disjoint U y
  disjoint V y
  disjoint ph y
  disjoint f y
  disjoint g y
  disjoint P y
  disjoint x y
  disjoint k x
  assert |- ( ph -> E. v e. J ( ( Z e. v /\ v C_ U ) /\ A. e e. RR+ E. x e. A ( A. t e. T ( 0 <_ ( x ` t ) /\ ( x ` t ) <_ 1 ) /\ A. t e. v ( x ` t ) < e /\ A. t e. ( T \ U ) ( 1 - e ) < ( x ` t ) ) ) )

  proof
    wph
    cV
    cJ
    wcel
    cZ
    cV
    wcel
    #
    cV
    cU
    wss
    #
    wa
    #
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
    @4
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    #
    @4
    ve
    cv
    #
    clt
    wbr
    #
    vt
    cV
    wral
    #
    c1
    @6
    cmin
    co
    #
    @4
    clt
    wbr
    vt
    cT
    cU
    cdif
    #
    wral
    #
    w3a
    #
    vx
    cA
    wrex
    #
    ve
    crp
    wral
    #
    wa
    #
    cZ
    vv
    cv
    #
    wcel
    #
    @16
    cU
    wss
    #
    wa
    #
    @5
    @7
    vt
    @16
    wral
    #
    @11
    w3a
    #
    vx
    cA
    wrex
    #
    ve
    crp
    wral
    #
    wa
    #
    vv
    cJ
    wrex
    wph
    vt
    cV
    cD
    c2
    cdiv
    co
    #
    cP
    cJ
    cK
    cT
    vt
    @25
    nfcv
    #
    stoweidlem52.3
    stoweidlem52.2
    stoweidlem52.4
    stoweidlem52.7
    stoweidlem52.5
    wph
    @25
    wph
    cD
    wph
    cD
    stoweidlem52.13
    rpred
    #
    rehalfcld
    #
    rexrd
    wph
    cA
    cJ
    cK
    ccn
    co
    #
    cP
    wph
    cA
    cC
    @29
    stoweidlem52.9
    stoweidlem52.8
    syl6sseq
    stoweidlem52.17
    sseldd
    rfcnpre2
    wph
    @0
    @1
    @14
    wph
    cZ
    @3
    cP
    cfv
    #
    @25
    clt
    wbr
    #
    vt
    cT
    crab
    #
    cV
    wph
    cZ
    cT
    wcel
    cZ
    cP
    cfv
    #
    @25
    clt
    wbr
    #
    cZ
    @32
    wcel
    wph
    cU
    cT
    cZ
    wph
    cU
    cJ
    cuni
    #
    cT
    wph
    cU
    cJ
    wcel
    cU
    @35
    wss
    stoweidlem52.15
    cU
    cJ
    elssuni
    syl
    stoweidlem52.7
    syl6sseqr
    stoweidlem52.16
    sseldd
    wph
    @33
    cc0
    @25
    clt
    stoweidlem52.19
    wph
    cD
    c2
    @27
    c2
    cr
    wcel
    wph
    2re
    a1i
    wph
    cD
    stoweidlem52.13
    rpgt0d
    #
    cc0
    c2
    clt
    wbr
    wph
    2pos
    a1i
    divgt0d
    eqbrtrd
    @31
    @34
    vt
    cZ
    cT
    vt
    cZ
    nfcv
    #
    vt
    cT
    nfcv
    vt
    @33
    @25
    clt
    vt
    cZ
    cP
    stoweidlem52.3
    @37
    nffv
    vt
    clt
    nfcv
    @26
    nfbr
    @3
    cZ
    wceq
    @30
    @33
    @25
    clt
    @3
    cZ
    cP
    fveq2
    breq1d
    elrabf
    sylanbrc
    stoweidlem52.5
    syl6eleqr
    wph
    vt
    cV
    cU
    stoweidlem52.2
    vt
    cV
    @32
    stoweidlem52.5
    @31
    vt
    cT
    nfrab1
    nfcxfr
    #
    stoweidlem52.1
    wph
    @3
    cV
    wcel
    #
    @3
    cU
    wcel
    #
    wph
    @39
    wa
    #
    @40
    @30
    cD
    clt
    wbr
    #
    @41
    @42
    @40
    wn
    #
    @41
    @30
    @25
    cD
    @41
    cT
    cr
    @3
    cP
    wph
    cT
    cr
    cP
    wf
    #
    @39
    wph
    cC
    cT
    cP
    cJ
    cK
    stoweidlem52.4
    stoweidlem52.7
    stoweidlem52.8
    wph
    cA
    cC
    cP
    stoweidlem52.9
    stoweidlem52.17
    sseldd
    fcnre
    #
    adantr
    @41
    @3
    cT
    wcel
    #
    @31
    @39
    @46
    @31
    wa
    #
    wph
    @39
    @47
    @31
    vt
    cV
    cT
    stoweidlem52.5
    rabeq2i
    biimpi
    adantl
    #
    simpld
    #
    ffvelrnd
    #
    wph
    @25
    cr
    wcel
    @39
    @28
    adantr
    wph
    cD
    cr
    wcel
    #
    @39
    @27
    adantr
    @41
    @46
    @31
    @48
    simprd
    wph
    @25
    cD
    clt
    wbr
    #
    @39
    wph
    cc0
    cD
    clt
    wbr
    #
    @52
    @36
    wph
    @51
    @53
    @52
    wb
    @27
    cD
    halfpos
    syl
    mpbid
    adantr
    lttrd
    adantr
    @41
    @43
    wa
    #
    cD
    @30
    wph
    @51
    @39
    @43
    @27
    ad2antrr
    @41
    @30
    cr
    wcel
    @43
    @50
    adantr
    @54
    cD
    @30
    cle
    wbr
    #
    vt
    @10
    wral
    #
    @3
    @10
    wcel
    #
    @55
    wph
    @56
    @39
    @43
    stoweidlem52.20
    ad2antrr
    @54
    @46
    @43
    wa
    @57
    @41
    @46
    @43
    @49
    anim1i
    @3
    cT
    cU
    eldif
    sylibr
    @55
    vt
    @10
    rsp
    sylc
    lensymd
    condan
    ex
    ssrd
    wph
    @13
    ve
    crp
    wph
    @6
    crp
    wcel
    #
    wa
    #
    cc0
    @3
    vy
    cv
    #
    cfv
    #
    cle
    wbr
    @61
    c1
    cle
    wbr
    wa
    #
    vt
    cT
    wral
    #
    @9
    @61
    clt
    wbr
    #
    vt
    cV
    wral
    #
    @61
    @6
    clt
    wbr
    #
    vt
    @10
    wral
    #
    w3a
    #
    @13
    vy
    cA
    @59
    @60
    cA
    wcel
    #
    wa
    #
    @68
    wa
    #
    vx
    vy
    va
    vt
    cA
    cT
    cU
    vf
    vg
    @6
    vt
    cT
    c1
    cmpt
    #
    cV
    vt
    cT
    c1
    @61
    cmin
    co
    cmpt
    #
    @70
    @68
    vt
    @59
    @69
    vt
    wph
    @58
    vt
    stoweidlem52.2
    @58
    vt
    nfv
    nfan
    #
    @69
    vt
    nfv
    nfan
    @63
    @65
    @67
    vt
    @62
    vt
    cT
    nfra1
    @64
    vt
    cV
    nfra1
    @66
    vt
    @10
    nfra1
    nf3an
    nfan
    @73
    eqid
    @72
    eqid
    cV
    @32
    cT
    stoweidlem52.5
    @31
    vt
    cT
    ssrab2
    eqsstri
    @59
    @69
    @68
    simplr
    #
    @71
    wph
    @69
    cT
    cr
    @60
    wf
    wph
    @58
    @69
    @68
    simplll
    #
    @75
    wph
    @69
    wa
    cC
    cT
    @60
    cJ
    cK
    stoweidlem52.4
    stoweidlem52.7
    stoweidlem52.8
    wph
    cA
    cC
    @60
    stoweidlem52.9
    sselda
    fcnre
    syl2anc
    @71
    wph
    vf
    cv
    #
    cA
    wcel
    #
    cT
    cr
    @77
    wf
    #
    @76
    wph
    @78
    wa
    cC
    cT
    @77
    cJ
    cK
    stoweidlem52.4
    stoweidlem52.7
    stoweidlem52.8
    wph
    cA
    cC
    @77
    stoweidlem52.9
    sselda
    fcnre
    #
    sylan
    @71
    wph
    @78
    vg
    cv
    #
    cA
    wcel
    #
    vt
    cT
    @3
    @77
    cfv
    #
    @3
    @81
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    #
    @76
    stoweidlem52.10
    syl3an1
    @71
    wph
    @78
    @82
    vt
    cT
    @83
    @84
    cmul
    co
    cmpt
    cA
    wcel
    #
    @76
    stoweidlem52.11
    syl3an1
    @71
    wph
    va
    cv
    #
    cr
    wcel
    #
    vt
    cT
    @87
    cmpt
    cA
    wcel
    #
    @76
    stoweidlem52.12
    sylan
    wph
    @58
    @69
    @68
    simpllr
    @70
    @63
    @65
    @67
    simpr1
    @70
    @63
    @65
    @67
    simpr2
    @70
    @63
    @65
    @67
    simpr3
    stoweidlem41
    @59
    va
    vy
    vt
    cA
    cD
    cP
    cT
    cU
    vf
    vg
    @6
    cV
    stoweidlem52.3
    @74
    stoweidlem52.5
    wph
    cD
    crp
    wcel
    @58
    stoweidlem52.13
    adantr
    wph
    cD
    c1
    clt
    wbr
    @58
    stoweidlem52.14
    adantr
    wph
    cP
    cA
    wcel
    @58
    stoweidlem52.17
    adantr
    wph
    @44
    @58
    @45
    adantr
    wph
    cc0
    @30
    cle
    wbr
    @30
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    @58
    stoweidlem52.18
    adantr
    wph
    @56
    @58
    stoweidlem52.20
    adantr
    wph
    @78
    @79
    @58
    @80
    adantlr
    wph
    @78
    @82
    @85
    @58
    stoweidlem52.10
    3adant1r
    wph
    @78
    @82
    @86
    @58
    stoweidlem52.11
    3adant1r
    wph
    @88
    @89
    @58
    stoweidlem52.12
    adantlr
    wph
    @58
    simpr
    stoweidlem49
    r19.29a
    ralrimiva
    jca31
    @24
    @15
    vv
    cV
    cJ
    @16
    cV
    wceq
    #
    @19
    @2
    @23
    @14
    @90
    @17
    @0
    @18
    @1
    @16
    cV
    cZ
    eleq2
    @16
    cV
    cU
    sseq1
    anbi12d
    @90
    @22
    @13
    ve
    crp
    @90
    @21
    @12
    vx
    cA
    @90
    @20
    @8
    @5
    @11
    @7
    vt
    @16
    cV
    vt
    @16
    nfcv
    @38
    raleqf
    3anbi2d
    rexbidv
    ralbidv
    anbi12d
    rspcev
    syl2anc
end
