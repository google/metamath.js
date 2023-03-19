include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "ccvm.mm"
include "co.mm"
include "wss.mm"
include "w3a.mm"
include "n0.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cres.mm"
include "crest.mm"
include "chmeo.mm"
include "simpl2.mm"
include "wf.mm"
include "wel.mm"
include "ctop.mm"
include "simpl1.mm"
include "cvmtop1.mm"
include "syl.mm"
include "adantr.mm"
include "cvmsss.mm"
include "adantl.mm"
include "sselda.mm"
include "ccn.mm"
include "cvmcn.mm"
include "cnima.mm"
include "syl2anc.mm"
include "inopn.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "cvmsn0.mm"
include "cdm.mm"
include "cvv.mm"
include "dmmptg.mm"
include "inex1g.mm"
include "mprg.mm"
include "eqeq1i.mm"
include "dm0rn0.mm"
include "bitr3i.mm"
include "necon3bii.mm"
include "sylib.mm"
include "jca.mm"
include "cpw.mm"
include "inss2.mm"
include "wb.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "sspwuni.mm"
include "simpl3.mm"
include "imass2.mm"
include "cvmsuni.mm"
include "sseqtr4d.mm"
include "wrex.mm"
include "weq.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "ad2antrl.mm"
include "vex.mm"
include "inex1.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "simprr.mm"
include "simplr.mm"
include "elind.mm"
include "eleq2.mm"
include "rexlimdvaa.mm"
include "eluni2.mm"
include "3imtr4g.mm"
include "mpd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "eldifsn.mm"
include "wi.mm"
include "wn.mm"
include "equcoms.mm"
include "necon3ai.mm"
include "wo.mm"
include "simpllr.mm"
include "simpr.mm"
include "cvmsdisj.mm"
include "ord.mm"
include "inss1.mm"
include "sseq0.mm"
include "mpan.mm"
include "syl56.mm"
include "neeq1.mm"
include "ineq2.mm"
include "inindir.mm"
include "syl6eqr.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "impd.mm"
include "ralrimiv.mm"
include "resabs1.mm"
include "cvmshmeo.mm"
include "adantll.mm"
include "elssuni.mm"
include "restuni.mm"
include "syl5sseq.mm"
include "hmeores.mm"
include "syl5eqelr.mm"
include "a1i.mm"
include "restabs.mm"
include "incom.mm"
include "cnvresima.mm"
include "eqtr4i.mm"
include "imaeq2i.mm"
include "wfo.mm"
include "wf1o.mm"
include "cvmsf1o.mm"
include "f1ofo.mm"
include "foimacnv.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "cvmtop2.mm"
include "cvmsrcl.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "eleqtrd.mm"
include "ralrimiva.mm"
include "rgenw.mm"
include "cbvmptv.mm"
include "sneq.mm"
include "difeq2d.mm"
include "raleqbidv.mm"
include "reseq2.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "ralrnmpt.mm"
include "cvmscbv.mm"
include "cvmsval.mm"
include "mpbir3and.mm"
include "ne0i.mm"
include "exlimdv.mm"

theorem cvmsss2
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cS: class S
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cV: class V
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cT: class T
  let cW: class W
  let cX: class X
  let cA: class A
  let cB: class B
  assume cvmcov.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )

  disjoint k s
  disjoint k u
  disjoint k v
  disjoint C k
  disjoint s u
  disjoint s v
  disjoint C s
  disjoint u v
  disjoint C u
  disjoint C v
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint V k
  disjoint V s
  disjoint V u
  disjoint V v
  disjoint a b
  disjoint a k
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b k
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint C t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint J a
  disjoint J b
  disjoint J t
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint S t
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint U t
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint T z
  disjoint V a
  disjoint V b
  disjoint V t
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B t
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( ( F e. ( C CovMap J ) /\ V e. J /\ V C_ U ) -> ( ( S ` U ) =/= (/) -> ( S ` V ) =/= (/) ) )

  proof
    cU
    cS
    cfv
    #
    c0
    wne
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cV
    cJ
    wcel
    #
    cV
    cU
    wss
    #
    w3a
    #
    cV
    cS
    cfv
    #
    c0
    wne
    #
    vx
    @0
    n0
    @6
    @2
    @8
    vx
    @6
    @2
    @8
    @6
    @2
    wa
    #
    vy
    @1
    vy
    cv
    #
    cF
    ccnv
    #
    cV
    cima
    #
    cin
    #
    cmpt
    #
    crn
    #
    @7
    wcel
    #
    @8
    @9
    @16
    @4
    @15
    cC
    wss
    #
    @15
    c0
    wne
    #
    wa
    #
    @15
    cuni
    #
    @12
    wceq
    #
    vw
    cv
    #
    vz
    cv
    #
    cin
    #
    c0
    wceq
    #
    vz
    @15
    @22
    csn
    #
    cdif
    #
    wral
    #
    cF
    @22
    cres
    #
    cC
    @22
    crest
    co
    #
    cJ
    cV
    crest
    co
    #
    chmeo
    co
    #
    wcel
    #
    wa
    #
    vw
    @15
    wral
    #
    wa
    #
    @3
    @4
    @5
    @2
    simpl2
    #
    @9
    @17
    @18
    @9
    @1
    cC
    @14
    wf
    @17
    @9
    vy
    @1
    @13
    cC
    @14
    @9
    vy
    vx
    wel
    #
    wa
    #
    cC
    ctop
    wcel
    #
    @10
    cC
    wcel
    @12
    cC
    wcel
    #
    @13
    cC
    wcel
    @9
    @40
    @38
    @9
    @3
    @40
    @3
    @4
    @5
    @2
    simpl1
    #
    cC
    cF
    cJ
    cvmtop1
    syl
    #
    adantr
    @9
    @1
    cC
    @10
    @2
    @1
    cC
    wss
    @6
    vv
    vu
    cC
    cS
    @1
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsss
    adantl
    #
    sselda
    @9
    @41
    @38
    @9
    cF
    cC
    cJ
    ccn
    co
    wcel
    #
    @4
    @41
    @9
    @3
    @45
    @42
    cC
    cF
    cJ
    cvmcn
    syl
    @37
    cV
    cF
    cC
    cJ
    cnima
    syl2anc
    adantr
    #
    @10
    @12
    cC
    inopn
    syl3anc
    @14
    eqid
    #
    fmptd
    @1
    cC
    @14
    frn
    syl
    @9
    @1
    c0
    wne
    #
    @18
    @2
    @48
    @6
    vv
    vu
    cC
    cS
    @1
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsn0
    adantl
    @1
    c0
    @15
    c0
    @1
    c0
    wceq
    @14
    cdm
    #
    c0
    wceq
    @15
    c0
    wceq
    @49
    @1
    c0
    @13
    cvv
    wcel
    @49
    @1
    wceq
    vy
    @1
    vy
    @1
    @13
    cvv
    dmmptg
    @10
    @12
    @1
    inex1g
    mprg
    eqeq1i
    @14
    dm0rn0
    bitr3i
    necon3bii
    sylib
    jca
    @9
    @21
    @35
    @9
    @20
    @12
    @9
    @15
    @12
    cpw
    #
    wss
    #
    @20
    @12
    wss
    @9
    @1
    @50
    @14
    wf
    @51
    @9
    vy
    @1
    @13
    @50
    @14
    @39
    @13
    @50
    wcel
    #
    @13
    @12
    wss
    #
    @10
    @12
    inss2
    @39
    @41
    @52
    @53
    wb
    @46
    @13
    @12
    cC
    elpw2g
    syl
    mpbiri
    @47
    fmptd
    @1
    @50
    @14
    frn
    syl
    @15
    @12
    sspwuni
    sylib
    @9
    vz
    @12
    @20
    @9
    @23
    @12
    wcel
    #
    @23
    @20
    wcel
    #
    @9
    @54
    wa
    #
    @23
    @1
    cuni
    #
    wcel
    #
    @55
    @9
    @12
    @57
    @23
    @9
    @12
    @11
    cU
    cima
    #
    @57
    @9
    @5
    @12
    @59
    wss
    @3
    @4
    @5
    @2
    simpl3
    #
    cV
    cU
    @11
    imass2
    syl
    @2
    @57
    @59
    wceq
    @6
    vv
    vu
    cC
    cS
    @1
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsuni
    adantl
    sseqtr4d
    sselda
    @56
    vz
    vt
    wel
    #
    vt
    @1
    wrex
    vz
    vw
    wel
    #
    vw
    @15
    wrex
    #
    @58
    @55
    @56
    @61
    @63
    vt
    @1
    @56
    vt
    vx
    wel
    #
    @61
    wa
    #
    wa
    #
    vt
    cv
    #
    @12
    cin
    #
    @15
    wcel
    #
    @23
    @68
    wcel
    #
    @63
    @66
    @68
    @13
    wceq
    #
    vy
    @1
    wrex
    #
    @69
    @64
    @72
    @56
    @61
    @64
    @68
    @68
    wceq
    #
    @72
    @68
    eqid
    @71
    @73
    vy
    @67
    @1
    vy
    vt
    weq
    @13
    @68
    @68
    @10
    @67
    @12
    ineq1
    #
    eqeq2d
    rspcev
    mpan2
    ad2antrl
    @68
    cvv
    wcel
    #
    @69
    @72
    wb
    @67
    @12
    vt
    vex
    inex1
    #
    vy
    @1
    @13
    @68
    @14
    cvv
    @47
    elrnmpt
    ax-mp
    sylibr
    @66
    @67
    @12
    @23
    @56
    @64
    @61
    simprr
    @9
    @54
    @65
    simplr
    elind
    @62
    @70
    vw
    @68
    @15
    @22
    @68
    @23
    eleq2
    rspcev
    syl2anc
    rexlimdvaa
    vt
    @23
    @1
    eluni2
    vw
    @23
    @15
    eluni2
    3imtr4g
    mpd
    ex
    ssrdv
    eqssd
    @9
    @68
    @23
    cin
    #
    c0
    wceq
    #
    vz
    @15
    @68
    csn
    #
    cdif
    #
    wral
    #
    cF
    @68
    cres
    #
    cC
    @68
    crest
    co
    #
    @31
    chmeo
    co
    #
    wcel
    #
    wa
    #
    vt
    @1
    wral
    #
    @35
    @9
    @86
    vt
    @1
    @9
    @64
    wa
    #
    @81
    @85
    @88
    @78
    vz
    @80
    @23
    @80
    wcel
    @23
    @15
    wcel
    #
    @23
    @68
    wne
    #
    wa
    @88
    @78
    @23
    @15
    @68
    eldifsn
    @88
    @89
    @90
    @78
    @89
    @23
    @13
    wceq
    #
    vy
    @1
    wrex
    #
    @88
    @90
    @78
    wi
    #
    @23
    cvv
    wcel
    @89
    @92
    wb
    vz
    vex
    vy
    @1
    @13
    @23
    @14
    cvv
    @47
    elrnmpt
    ax-mp
    @88
    @91
    @93
    vy
    @1
    @88
    @38
    wa
    #
    @93
    @91
    @13
    @68
    wne
    #
    @67
    @10
    cin
    #
    @12
    cin
    #
    c0
    wceq
    #
    wi
    @95
    vt
    vy
    weq
    #
    wn
    @94
    @96
    c0
    wceq
    #
    @98
    @99
    @13
    @68
    @13
    @68
    wceq
    vy
    vt
    @74
    equcoms
    necon3ai
    @94
    @99
    @100
    @94
    @2
    @64
    @38
    @99
    @100
    wo
    @6
    @2
    @64
    @38
    simpllr
    @9
    @64
    @38
    simplr
    @88
    @38
    simpr
    vv
    vu
    @67
    @10
    cC
    cS
    @1
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsdisj
    syl3anc
    ord
    @97
    @96
    wss
    @100
    @98
    @96
    @12
    inss1
    @97
    @96
    sseq0
    mpan
    syl56
    @91
    @90
    @95
    @78
    @98
    @23
    @13
    @68
    neeq1
    @91
    @77
    @97
    c0
    @91
    @77
    @68
    @13
    cin
    @97
    @23
    @13
    @68
    ineq2
    @67
    @10
    @12
    inindir
    syl6eqr
    eqeq1d
    imbi12d
    syl5ibrcom
    rexlimdva
    syl5bi
    impd
    syl5bi
    ralrimiv
    @88
    @82
    cC
    @67
    crest
    co
    #
    @68
    crest
    co
    #
    cJ
    cU
    crest
    co
    #
    cF
    @67
    cres
    #
    @68
    cima
    #
    crest
    co
    #
    chmeo
    co
    #
    @84
    @88
    @82
    @104
    @68
    cres
    #
    @107
    @68
    @67
    wss
    #
    @108
    @82
    wceq
    @67
    @12
    inss1
    #
    cF
    @68
    @67
    resabs1
    ax-mp
    @88
    @104
    @101
    @103
    chmeo
    co
    wcel
    #
    @68
    @101
    cuni
    #
    wss
    @108
    @107
    wcel
    @2
    @64
    @111
    @6
    vv
    vu
    @67
    cC
    cS
    @1
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmshmeo
    adantll
    @88
    @67
    @68
    @112
    @110
    @88
    @40
    @67
    cC
    cuni
    #
    wss
    #
    @67
    @112
    wceq
    @9
    @40
    @64
    @43
    adantr
    #
    @88
    @67
    cC
    wcel
    @114
    @9
    @1
    cC
    @67
    @44
    sselda
    @67
    cC
    elssuni
    syl
    @67
    cC
    @113
    @113
    eqid
    restuni
    syl2anc
    syl5sseq
    @104
    @101
    @103
    @112
    @68
    @112
    eqid
    hmeores
    syl2anc
    syl5eqelr
    @88
    @102
    @83
    @106
    @31
    chmeo
    @88
    @40
    @109
    @64
    @102
    @83
    wceq
    @115
    @109
    @88
    @110
    a1i
    @9
    @64
    simpr
    #
    @68
    @67
    cC
    ctop
    @1
    restabs
    syl3anc
    @88
    @106
    @103
    cV
    crest
    co
    #
    @31
    @88
    @105
    cV
    @103
    crest
    @88
    @105
    @104
    @104
    ccnv
    cV
    cima
    #
    cima
    #
    cV
    @68
    @118
    @104
    @68
    @12
    @67
    cin
    @118
    @67
    @12
    incom
    @67
    cV
    cF
    cnvresima
    eqtr4i
    imaeq2i
    @88
    @67
    cU
    @104
    wfo
    #
    @5
    @119
    cV
    wceq
    @88
    @67
    cU
    @104
    wf1o
    #
    @120
    @88
    @3
    @2
    @64
    @121
    @9
    @3
    @64
    @42
    adantr
    @6
    @2
    @64
    simplr
    @116
    vv
    vu
    @67
    cC
    cS
    @1
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsf1o
    syl3anc
    @67
    cU
    @104
    f1ofo
    syl
    @9
    @5
    @64
    @60
    adantr
    @67
    cU
    cV
    @104
    foimacnv
    syl2anc
    syl5eq
    oveq2d
    @9
    @117
    @31
    wceq
    #
    @64
    @9
    cJ
    ctop
    wcel
    #
    @5
    cU
    cJ
    wcel
    #
    @122
    @9
    @3
    @123
    @42
    cC
    cF
    cJ
    cvmtop2
    syl
    @60
    @2
    @124
    @6
    vv
    vu
    cC
    cS
    @1
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsrcl
    adantl
    cV
    cU
    cJ
    ctop
    cJ
    restabs
    syl3anc
    adantr
    eqtrd
    oveq12d
    eleqtrd
    jca
    ralrimiva
    @75
    vt
    @1
    wral
    @35
    @87
    wb
    @75
    vt
    @1
    @76
    rgenw
    @34
    @86
    vt
    vw
    @1
    @68
    @14
    cvv
    vy
    vt
    @1
    @13
    @68
    @74
    cbvmptv
    @22
    @68
    wceq
    #
    @28
    @81
    @33
    @85
    @125
    @25
    @78
    vz
    @27
    @80
    @125
    @26
    @79
    @15
    @22
    @68
    sneq
    difeq2d
    @125
    @24
    @77
    c0
    @22
    @68
    @23
    ineq1
    eqeq1d
    raleqbidv
    @125
    @29
    @82
    @32
    @84
    @22
    @68
    cF
    reseq2
    @125
    @30
    @83
    @31
    chmeo
    @22
    @68
    cC
    crest
    oveq2
    oveq1d
    eleq12d
    anbi12d
    ralrnmpt
    ax-mp
    sylibr
    jca
    @9
    @40
    @16
    @4
    @19
    @36
    w3a
    wb
    @43
    vz
    vw
    cC
    cS
    @15
    cV
    va
    cF
    cJ
    ctop
    vb
    vv
    vu
    cC
    cS
    vk
    cF
    cJ
    vs
    va
    vb
    vw
    vz
    cvmcov.1
    cvmscbv
    cvmsval
    syl
    mpbir3and
    @7
    @15
    ne0i
    syl
    ex
    exlimdv
    syl5bi
end
