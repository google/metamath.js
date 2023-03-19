include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "cfv.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cmin.mm"
include "wa.mm"
include "wex.mm"
include "w3a.mm"
include "cn.mm"
include "wrex.mm"
include "cc0.mm"
include "cle.mm"
include "c0.mm"
include "wne.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "cdif.mm"
include "crp.mm"
include "nfcri.mm"
include "nfan.mm"
include "ccmp.mm"
include "adantr.mm"
include "caddc.mm"
include "cmpt.mm"
include "3adant1r.mm"
include "cmul.mm"
include "cr.mm"
include "adantlr.mm"
include "ccld.mm"
include "ctop.mm"
include "wb.mm"
include "cmptop.mm"
include "iscld.mm"
include "3syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "syl5eqel.mm"
include "cldss.mm"
include "syl.mm"
include "sselda.mm"
include "wn.mm"
include "wceq.mm"
include "disjr.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "eldifd.mm"
include "syl6eleqr.mm"
include "stoweidlem56.mm"
include "simpl.mm"
include "simprll.mm"
include "simprr.mm"
include "rabeq2i.mm"
include "sylanbrc.mm"
include "jca32.mm"
include "reximi2.mm"
include "rexex.mm"
include "nfcv.mm"
include "crab.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "elunif.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "wi.mm"
include "crest.mm"
include "cmpcld.mm"
include "syl2anc.mm"
include "cmpsub.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cvv.mm"
include "rabexd.mm"
include "elpwg.mm"
include "mpbiri.mm"
include "unieq.mm"
include "sseq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspccva.mm"
include "mpd.mm"
include "csn.mm"
include "elinel1.mm"
include "elpwi.mm"
include "ssdifssd.mm"
include "vex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "elpw.mm"
include "elinel2.mm"
include "diffi.mm"
include "elind.mm"
include "3ad2ant2.mm"
include "unidif0.mm"
include "sseq2i.mm"
include "biimpri.mm"
include "3ad2ant3.mm"
include "eldifsni.mm"
include "rgen.mm"
include "a1i.mm"
include "raleq.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimdv3a.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfral.mm"
include "nfrab.mm"
include "nfpw.mm"
include "nfin.mm"
include "nf3an.mm"
include "nfra1.mm"
include "nfrex.mm"
include "nfss.mm"
include "simp2.mm"
include "simp3l.mm"
include "3ad2ant1.mm"
include "simpld.mm"
include "ccn.mm"
include "cioo.mm"
include "ctg.mm"
include "retop.mm"
include "eqeltri.mm"
include "cnfex.mm"
include "sylancl.mm"
include "syl6sseq.mm"
include "ssexd.mm"
include "stoweidlem39.mm"
include "cmpt2.mm"
include "cseq.mm"
include "nfex.mm"
include "nff.mm"
include "nfe1.mm"
include "eqid.mm"
include "simp1ll.mm"
include "syld3an1.mm"
include "fcnre.mm"
include "ad4ant14.mm"
include "simplr.mm"
include "simpr1.mm"
include "ad2antrr.mm"
include "simpr2.mm"
include "feq3.mm"
include "biimpi.mm"
include "anim1i.mm"
include "eximi.mm"
include "adantl.mm"
include "uniexg.mm"
include "c3.mm"
include "stoweidlem54.mm"
include "exlimdv.mm"
include "rexlimdva.mm"

theorem stoweidlem57
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cJ: class J
  let cK: class K
  let cV: class V
  let cY: class Y
  let vr: setvar r
  let vq: setvar q
  let va: setvar a
  let vs: setvar s
  let vm: setvar m
  let vi: setvar i
  let vv: setvar v
  let vy: setvar y
  let vk: setvar k
  let vu: setvar u
  assume stoweidlem57.1: |- F/_ t D
  assume stoweidlem57.2: |- F/_ t U
  assume stoweidlem57.3: |- F/ t ph
  assume stoweidlem57.4: |- Y = { h e. A | A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) }
  assume stoweidlem57.5: |- V = { w e. J | A. e e. RR+ E. h e. A ( A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) /\ A. t e. w ( h ` t ) < e /\ A. t e. ( T \ U ) ( 1 - e ) < ( h ` t ) ) }
  assume stoweidlem57.6: |- K = ( topGen ` ran (,) )
  assume stoweidlem57.7: |- T = U. J
  assume stoweidlem57.8: |- C = ( J Cn K )
  assume stoweidlem57.9: |- U = ( T \ B )
  assume stoweidlem57.10: |- ( ph -> J e. Comp )
  assume stoweidlem57.11: |- ( ph -> A C_ C )
  assume stoweidlem57.12: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem57.13: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem57.14: |- ( ( ph /\ a e. RR ) -> ( t e. T |-> a ) e. A )
  assume stoweidlem57.15: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. q e. A ( q ` r ) =/= ( q ` t ) )
  assume stoweidlem57.16: |- ( ph -> B e. ( Clsd ` J ) )
  assume stoweidlem57.17: |- ( ph -> D e. ( Clsd ` J ) )
  assume stoweidlem57.18: |- ( ph -> ( B i^i D ) = (/) )
  assume stoweidlem57.19: |- ( ph -> D =/= (/) )
  assume stoweidlem57.20: |- ( ph -> E e. RR+ )
  assume stoweidlem57.21: |- ( ph -> E < ( 1 / 3 ) )

  disjoint a e
  disjoint a f
  disjoint a t
  disjoint e f
  disjoint e t
  disjoint f t
  disjoint a q
  disjoint a r
  disjoint f q
  disjoint f r
  disjoint q r
  disjoint q t
  disjoint r t
  disjoint A a
  disjoint A e
  disjoint A f
  disjoint A t
  disjoint D a
  disjoint D e
  disjoint D f
  disjoint T a
  disjoint T e
  disjoint T f
  disjoint T t
  disjoint U a
  disjoint U e
  disjoint U f
  disjoint a ph
  disjoint e ph
  disjoint f ph
  disjoint e g
  disjoint e h
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint g t
  disjoint A g
  disjoint h t
  disjoint A h
  disjoint e w
  disjoint h w
  disjoint t w
  disjoint A w
  disjoint E e
  disjoint E f
  disjoint E g
  disjoint E h
  disjoint E t
  disjoint g r
  disjoint h r
  disjoint A r
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint t x
  disjoint A x
  disjoint B f
  disjoint B g
  disjoint B r
  disjoint V f
  disjoint V g
  disjoint V r
  disjoint Y f
  disjoint Y g
  disjoint Y r
  disjoint g q
  disjoint D g
  disjoint D h
  disjoint D r
  disjoint J g
  disjoint J h
  disjoint J t
  disjoint T g
  disjoint T h
  disjoint T r
  disjoint U g
  disjoint U h
  disjoint U r
  disjoint g ph
  disjoint h ph
  disjoint ph r
  disjoint r w
  disjoint E r
  disjoint E w
  disjoint A q
  disjoint D q
  disjoint T q
  disjoint U q
  disjoint ph q
  disjoint D w
  disjoint B w
  disjoint K t
  disjoint ph w
  disjoint J w
  disjoint T w
  disjoint U w
  disjoint Y w
  disjoint B x
  disjoint D x
  disjoint E x
  disjoint T x
  disjoint a s
  disjoint e s
  disjoint f s
  disjoint s t
  disjoint q s
  disjoint r s
  disjoint D s
  disjoint ph s
  disjoint e m
  disjoint f m
  disjoint g m
  disjoint h m
  disjoint m t
  disjoint A m
  disjoint m w
  disjoint E m
  disjoint f i
  disjoint f v
  disjoint f y
  disjoint g i
  disjoint g v
  disjoint g y
  disjoint h i
  disjoint h v
  disjoint h y
  disjoint i m
  disjoint i r
  disjoint i t
  disjoint i v
  disjoint i y
  disjoint A i
  disjoint m r
  disjoint m v
  disjoint m y
  disjoint r v
  disjoint r y
  disjoint t v
  disjoint t y
  disjoint v y
  disjoint A v
  disjoint A y
  disjoint m x
  disjoint v x
  disjoint x y
  disjoint B i
  disjoint B m
  disjoint B v
  disjoint B y
  disjoint V i
  disjoint V m
  disjoint V v
  disjoint V y
  disjoint Y i
  disjoint Y y
  disjoint g s
  disjoint D i
  disjoint D m
  disjoint D v
  disjoint D y
  disjoint T i
  disjoint T m
  disjoint T v
  disjoint T y
  disjoint U i
  disjoint U y
  disjoint i ph
  disjoint m ph
  disjoint ph v
  disjoint ph y
  disjoint i w
  disjoint v w
  disjoint w y
  disjoint E i
  disjoint E v
  disjoint E y
  disjoint k u
  disjoint D k
  disjoint D u
  disjoint J k
  disjoint J u
  disjoint T k
  disjoint T u
  disjoint V k
  disjoint V u
  disjoint r u
  disjoint u w
  disjoint s w
  disjoint V s
  disjoint B s
  disjoint ph u
  disjoint k x
  assert |- ( ph -> E. x e. A ( A. t e. T ( 0 <_ ( x ` t ) /\ ( x ` t ) <_ 1 ) /\ A. t e. D ( x ` t ) < E /\ A. t e. B ( 1 - E ) < ( x ` t ) ) )

  proof
    wph
    c1
    vm
    cv
    #
    cfz
    co
    #
    cV
    vv
    cv
    #
    wf
    #
    cD
    @2
    crn
    cuni
    #
    wss
    #
    @1
    cY
    vy
    cv
    #
    wf
    #
    vt
    cv
    #
    vi
    cv
    #
    @6
    cfv
    cfv
    #
    cE
    @0
    cdiv
    co
    #
    clt
    wbr
    #
    vt
    @9
    @2
    cfv
    #
    wral
    #
    c1
    @11
    cmin
    co
    @10
    clt
    wbr
    #
    vt
    cB
    wral
    #
    wa
    #
    vi
    @1
    wral
    #
    wa
    #
    vy
    wex
    #
    w3a
    #
    vv
    wex
    #
    vm
    cn
    wrex
    #
    cc0
    @8
    vx
    cv
    cfv
    #
    cle
    wbr
    @24
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    @24
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
    @24
    clt
    wbr
    vt
    cB
    wral
    w3a
    vx
    cA
    wrex
    #
    wph
    cD
    vr
    cv
    #
    cuni
    #
    wss
    #
    vw
    cv
    #
    c0
    wne
    #
    vw
    @26
    wral
    #
    wa
    #
    vr
    cV
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @23
    wph
    cD
    vu
    cv
    #
    cuni
    #
    wss
    #
    vu
    @34
    wrex
    #
    @35
    wph
    cD
    cV
    cuni
    #
    wss
    #
    @39
    wph
    vs
    cD
    @40
    wph
    vs
    cv
    #
    cD
    wcel
    #
    @42
    @40
    wcel
    #
    wph
    @43
    wa
    #
    @42
    @29
    wcel
    #
    @29
    cV
    wcel
    #
    wa
    #
    vw
    wex
    #
    @44
    @45
    @46
    @29
    cU
    wss
    #
    wa
    #
    cc0
    @8
    vh
    cv
    cfv
    #
    cle
    wbr
    @52
    c1
    cle
    wbr
    wa
    #
    vt
    cT
    wral
    #
    @52
    ve
    cv
    #
    clt
    wbr
    #
    vt
    @29
    wral
    #
    c1
    @55
    cmin
    co
    @52
    clt
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
    vh
    cA
    wrex
    #
    ve
    crp
    wral
    #
    wa
    #
    vw
    cJ
    wrex
    @48
    vw
    cJ
    wrex
    @49
    @45
    vh
    va
    vw
    vt
    cA
    cC
    cT
    cU
    ve
    vf
    vg
    cJ
    cK
    @42
    vr
    vq
    stoweidlem57.2
    wph
    @43
    vt
    stoweidlem57.3
    vt
    vs
    cD
    stoweidlem57.1
    nfcri
    nfan
    stoweidlem57.6
    wph
    cJ
    ccmp
    wcel
    #
    @43
    stoweidlem57.10
    adantr
    stoweidlem57.7
    stoweidlem57.8
    wph
    cA
    cC
    wss
    @43
    stoweidlem57.11
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
    @8
    @66
    cfv
    #
    @8
    @68
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    @43
    stoweidlem57.12
    3adant1r
    wph
    @67
    @69
    vt
    cT
    @70
    @71
    cmul
    co
    cmpt
    #
    cA
    wcel
    #
    @43
    stoweidlem57.13
    3adant1r
    wph
    va
    cv
    #
    cr
    wcel
    vt
    cT
    @74
    cmpt
    cA
    wcel
    @43
    stoweidlem57.14
    adantlr
    wph
    @26
    cT
    wcel
    @8
    cT
    wcel
    @26
    @8
    wne
    w3a
    @26
    vq
    cv
    #
    cfv
    @8
    @75
    cfv
    wne
    vq
    cA
    wrex
    @43
    stoweidlem57.15
    adantlr
    wph
    cU
    cJ
    wcel
    @43
    wph
    cU
    cT
    cB
    cdif
    #
    cJ
    stoweidlem57.9
    wph
    cB
    cT
    wss
    #
    @76
    cJ
    wcel
    #
    wph
    cB
    cJ
    ccld
    cfv
    #
    wcel
    #
    @77
    @78
    wa
    #
    stoweidlem57.16
    wph
    @65
    cJ
    ctop
    wcel
    #
    @80
    @81
    wb
    stoweidlem57.10
    cJ
    cmptop
    #
    cB
    cJ
    cT
    stoweidlem57.7
    iscld
    3syl
    mpbid
    #
    simprd
    syl5eqel
    adantr
    @45
    @42
    @76
    cU
    @45
    @42
    cT
    cB
    wph
    cD
    cT
    @42
    wph
    cD
    @79
    wcel
    #
    cD
    cT
    wss
    #
    stoweidlem57.17
    cD
    cJ
    cT
    stoweidlem57.7
    cldss
    syl
    #
    sselda
    wph
    @42
    cB
    wcel
    wn
    #
    vs
    cD
    wph
    cB
    cD
    cin
    c0
    wceq
    @88
    vs
    cD
    wral
    stoweidlem57.18
    vs
    cB
    cD
    disjr
    sylib
    r19.21bi
    eldifd
    stoweidlem57.9
    syl6eleqr
    stoweidlem56
    @64
    @48
    vw
    cJ
    cJ
    @29
    cJ
    wcel
    #
    @64
    wa
    #
    @89
    @46
    @47
    @89
    @64
    simpl
    #
    @89
    @46
    @50
    @63
    simprll
    @90
    @89
    @63
    @47
    @91
    @89
    @51
    @63
    simprr
    @63
    vw
    cV
    cJ
    stoweidlem57.5
    rabeq2i
    sylanbrc
    jca32
    reximi2
    @48
    vw
    cJ
    rexex
    3syl
    vw
    @42
    cV
    vw
    @42
    nfcv
    vw
    cV
    @63
    vw
    cJ
    crab
    #
    stoweidlem57.5
    @63
    vw
    cJ
    nfrab1
    nfcxfr
    #
    elunif
    sylibr
    ex
    ssrdv
    wph
    cD
    vk
    cv
    #
    cuni
    #
    wss
    #
    @38
    vu
    @94
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vk
    cJ
    cpw
    #
    wral
    #
    cV
    @101
    wcel
    #
    @41
    @39
    wi
    #
    wph
    cJ
    cD
    crest
    co
    ccmp
    wcel
    #
    @102
    wph
    @65
    @85
    @105
    stoweidlem57.10
    stoweidlem57.17
    cD
    cJ
    cmpcld
    syl2anc
    wph
    @82
    @86
    @105
    @102
    wb
    wph
    @65
    @82
    stoweidlem57.10
    @83
    syl
    #
    @87
    cD
    cJ
    cT
    vk
    vu
    stoweidlem57.7
    cmpsub
    syl2anc
    mpbid
    wph
    @103
    cV
    cJ
    wss
    #
    cV
    @92
    cJ
    stoweidlem57.5
    @63
    vw
    cJ
    ssrab2
    eqsstri
    wph
    cV
    cvv
    wcel
    #
    @103
    @107
    wb
    wph
    @63
    vw
    cJ
    cV
    ccmp
    stoweidlem57.5
    stoweidlem57.10
    rabexd
    #
    cV
    cJ
    cvv
    elpwg
    syl
    mpbiri
    @100
    @104
    vk
    cV
    @101
    @94
    cV
    wceq
    #
    @96
    @41
    @99
    @39
    @110
    @95
    @40
    cD
    @94
    cV
    unieq
    sseq2d
    @110
    @38
    vu
    @98
    @34
    @110
    @97
    @33
    cfn
    @94
    cV
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspccva
    syl2anc
    mpd
    wph
    @38
    @35
    vu
    @34
    wph
    @36
    @34
    wcel
    #
    @38
    w3a
    #
    @36
    c0
    csn
    #
    cdif
    #
    @34
    wcel
    #
    cD
    @114
    cuni
    #
    wss
    #
    @30
    vw
    @114
    wral
    #
    @35
    @111
    wph
    @115
    @38
    @111
    @33
    cfn
    @114
    @111
    @36
    @33
    wcel
    #
    @114
    @33
    wcel
    #
    @36
    @33
    cfn
    elinel1
    @119
    @114
    cV
    wss
    @120
    @119
    @36
    cV
    @113
    @36
    cV
    elpwi
    ssdifssd
    @114
    cV
    @36
    cvv
    wcel
    @114
    cvv
    wcel
    vu
    vex
    @36
    @113
    cvv
    difexg
    ax-mp
    elpw
    sylibr
    syl
    @111
    @36
    cfn
    wcel
    @114
    cfn
    wcel
    @36
    @33
    cfn
    elinel2
    @36
    @113
    diffi
    syl
    elind
    3ad2ant2
    @38
    wph
    @117
    @111
    @117
    @38
    @116
    @37
    cD
    @36
    unidif0
    sseq2i
    biimpri
    3ad2ant3
    @118
    @112
    @30
    vw
    @114
    @29
    @36
    c0
    eldifsni
    rgen
    a1i
    @32
    @117
    @118
    wa
    vr
    @114
    @34
    @26
    @114
    wceq
    #
    @28
    @117
    @31
    @118
    @121
    @27
    @116
    cD
    @26
    @114
    unieq
    sseq2d
    @30
    vw
    @26
    @114
    raleq
    anbi12d
    rspcev
    syl12anc
    rexlimdv3a
    mpd
    wph
    @32
    @23
    vr
    @34
    wph
    @26
    @34
    wcel
    #
    @32
    w3a
    vy
    vw
    vv
    vt
    cA
    cB
    cD
    cT
    cU
    ve
    vh
    vi
    vm
    cE
    cJ
    cV
    cY
    vr
    wph
    @122
    @32
    vh
    wph
    vh
    nfv
    vh
    vr
    @34
    vh
    @33
    cfn
    vh
    cV
    vh
    cV
    @92
    stoweidlem57.5
    @63
    vh
    vw
    cJ
    @62
    vh
    ve
    crp
    vh
    crp
    nfcv
    @61
    vh
    cA
    nfre1
    nfral
    vh
    cJ
    nfcv
    nfrab
    nfcxfr
    nfpw
    vh
    cfn
    nfcv
    nfin
    nfcri
    @32
    vh
    nfv
    nf3an
    wph
    @122
    @32
    vt
    stoweidlem57.3
    vt
    vr
    @34
    vt
    @33
    cfn
    vt
    cV
    vt
    cV
    @92
    stoweidlem57.5
    @63
    vt
    vw
    cJ
    @62
    vt
    ve
    crp
    vt
    crp
    nfcv
    @61
    vt
    vh
    cA
    vt
    cA
    nfcv
    #
    @54
    @57
    @60
    vt
    @53
    vt
    cT
    nfra1
    #
    @56
    vt
    @29
    nfra1
    @58
    vt
    @59
    nfra1
    nf3an
    nfrex
    nfral
    vt
    cJ
    nfcv
    nfrab
    nfcxfr
    #
    nfpw
    vt
    cfn
    nfcv
    nfin
    nfcri
    @28
    @31
    vt
    vt
    cD
    @27
    stoweidlem57.1
    vt
    @27
    nfcv
    nfss
    @31
    vt
    nfv
    nfan
    nf3an
    wph
    @122
    @32
    vw
    wph
    vw
    nfv
    vw
    vr
    @34
    vw
    @33
    cfn
    vw
    cV
    @93
    nfpw
    vw
    cfn
    nfcv
    nfin
    nfcri
    @28
    @31
    vw
    @28
    vw
    nfv
    @30
    vw
    @26
    nfra1
    nfan
    nf3an
    stoweidlem57.9
    stoweidlem57.4
    stoweidlem57.5
    wph
    @122
    @32
    simp2
    wph
    @122
    @28
    @31
    simp3l
    wph
    @122
    cD
    c0
    wne
    @32
    stoweidlem57.19
    3ad2ant1
    wph
    @122
    cE
    crp
    wcel
    #
    @32
    stoweidlem57.20
    3ad2ant1
    wph
    @122
    @77
    @32
    wph
    @77
    @78
    @84
    simpld
    3ad2ant1
    wph
    @122
    @108
    @32
    @109
    3ad2ant1
    wph
    @122
    cA
    cvv
    wcel
    @32
    wph
    cA
    cJ
    cK
    ccn
    co
    #
    cvv
    wph
    @82
    cK
    ctop
    wcel
    @127
    cvv
    wcel
    @106
    cK
    cioo
    crn
    ctg
    cfv
    ctop
    stoweidlem57.6
    retop
    eqeltri
    cJ
    cK
    cnfex
    sylancl
    wph
    cA
    cC
    @127
    stoweidlem57.11
    stoweidlem57.8
    syl6sseq
    ssexd
    3ad2ant1
    stoweidlem39
    rexlimdv3a
    mpd
    wph
    @22
    @25
    vm
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @21
    @25
    vv
    @129
    @21
    @25
    @129
    @21
    wa
    #
    vx
    vy
    vw
    vt
    cA
    cB
    cD
    vf
    vg
    @54
    vh
    cA
    crab
    #
    @131
    @72
    cmpt2
    #
    cT
    cU
    ve
    vf
    vg
    vh
    vi
    cE
    vt
    cT
    vi
    @1
    @10
    cmpt
    cmpt
    #
    cJ
    @0
    cV
    @2
    @131
    vt
    cT
    @0
    cmul
    @8
    @133
    cfv
    c1
    cseq
    cfv
    cmpt
    #
    @129
    @21
    vi
    @129
    vi
    nfv
    @3
    @5
    @20
    vi
    @3
    vi
    nfv
    @5
    vi
    nfv
    @19
    vi
    vy
    @7
    @18
    vi
    @7
    vi
    nfv
    @17
    vi
    @1
    nfra1
    nfan
    nfex
    nf3an
    nfan
    @129
    @21
    vt
    wph
    @128
    vt
    stoweidlem57.3
    @128
    vt
    nfv
    nfan
    @3
    @5
    @20
    vt
    vt
    @1
    cV
    @2
    vt
    @2
    nfcv
    vt
    @1
    nfcv
    #
    @125
    nff
    vt
    cD
    @4
    stoweidlem57.1
    vt
    @4
    nfcv
    nfss
    @19
    vt
    vy
    @7
    @18
    vt
    vt
    @1
    cY
    @6
    vt
    @6
    nfcv
    @135
    vt
    cY
    @131
    stoweidlem57.4
    @54
    vt
    vh
    cA
    @124
    @123
    nfrab
    nfcxfr
    nff
    @17
    vt
    vi
    @1
    @135
    @14
    @16
    vt
    @12
    vt
    @13
    nfra1
    @15
    vt
    cB
    nfra1
    nfan
    nfral
    nfan
    nfex
    nf3an
    nfan
    @129
    @21
    vy
    @129
    vy
    nfv
    @3
    @5
    @20
    vy
    @3
    vy
    nfv
    @5
    vy
    nfv
    @19
    vy
    nfe1
    nf3an
    nfan
    @129
    @21
    vw
    @129
    vw
    nfv
    @3
    @5
    @20
    vw
    vw
    @1
    cV
    @2
    vw
    @2
    nfcv
    vw
    @1
    nfcv
    @93
    nff
    @5
    vw
    nfv
    @20
    vw
    nfv
    nf3an
    nfan
    stoweidlem57.7
    @131
    eqid
    @132
    eqid
    @133
    eqid
    @134
    eqid
    stoweidlem57.5
    wph
    @67
    @130
    @69
    @73
    wph
    @128
    @21
    @67
    @69
    simp1ll
    stoweidlem57.13
    syld3an1
    wph
    @67
    cT
    cr
    @66
    wf
    @128
    @21
    wph
    @67
    wa
    cC
    cT
    @66
    cJ
    cK
    stoweidlem57.6
    stoweidlem57.7
    stoweidlem57.8
    wph
    cA
    cC
    @66
    stoweidlem57.11
    sselda
    fcnre
    ad4ant14
    wph
    @128
    @21
    simplr
    @129
    @3
    @5
    @20
    simpr1
    wph
    @77
    @128
    @21
    wph
    @80
    @77
    stoweidlem57.16
    cB
    cJ
    cT
    stoweidlem57.7
    cldss
    syl
    ad2antrr
    @129
    @3
    @5
    @20
    simpr2
    wph
    @86
    @128
    @21
    @87
    ad2antrr
    @21
    @1
    @131
    @6
    wf
    #
    @18
    wa
    #
    vy
    wex
    #
    @129
    @20
    @3
    @138
    @5
    @19
    @137
    vy
    @7
    @136
    @18
    @7
    @136
    cY
    @131
    wceq
    @7
    @136
    wb
    stoweidlem57.4
    cY
    @131
    @1
    @6
    feq3
    ax-mp
    biimpi
    anim1i
    eximi
    3ad2ant3
    adantl
    wph
    cT
    cvv
    wcel
    @128
    @21
    wph
    cT
    cJ
    cuni
    #
    cvv
    stoweidlem57.7
    wph
    @65
    @139
    cvv
    wcel
    stoweidlem57.10
    cJ
    ccmp
    uniexg
    syl
    syl5eqel
    ad2antrr
    wph
    @126
    @128
    @21
    stoweidlem57.20
    ad2antrr
    wph
    cE
    c1
    c3
    cdiv
    co
    clt
    wbr
    @128
    @21
    stoweidlem57.21
    ad2antrr
    stoweidlem54
    ex
    exlimdv
    rexlimdva
    mpd
end
