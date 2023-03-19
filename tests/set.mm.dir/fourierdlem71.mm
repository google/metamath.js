include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "cdm.mm"
include "cin.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crn.mm"
include "cuni.mm"
include "cpr.mm"
include "cfn.mm"
include "wcel.mm"
include "prfi.mm"
include "a1i.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "cun.mm"
include "simpl.mm"
include "simpr.mm"
include "cvv.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "ovex.mm"
include "fex.mm"
include "syl2anc.mm"
include "rnexg.mm"
include "inex1g.mm"
include "3syl.mm"
include "cfzo.mm"
include "c1.mm"
include "caddc.mm"
include "cioo.mm"
include "cmpt.mm"
include "mptex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "uniexg.mm"
include "syl.mm"
include "uniprg.mm"
include "eleqtrd.mm"
include "elinel2.mm"
include "adantl.mm"
include "wn.mm"
include "simpll.mm"
include "elunnel1.mm"
include "adantll.mm"
include "wfun.mm"
include "wb.mm"
include "funmpt2.mm"
include "elunirn.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "wi.mm"
include "w3a.mm"
include "wss.mm"
include "id.mm"
include "dmmpti.mm"
include "syl6eleq.mm"
include "fvmpt2.mm"
include "cres.mm"
include "cc.mm"
include "ccncf.mm"
include "cncff.mm"
include "fdm.mm"
include "sylan2.mm"
include "ssdmres.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "3adant3.mm"
include "simp3.mm"
include "sseldd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "pm2.61dan.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "abscld.mm"
include "fzfid.mm"
include "rnffi.mm"
include "infi.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "fimaxre3.mm"
include "adantlr.mm"
include "wne.mm"
include "neqne.mm"
include "elprn1.mm"
include "fzofi.mm"
include "rnmptfi.mm"
include "wfn.mm"
include "fnmpti.mm"
include "fvelrnb.mm"
include "elfzofz.mm"
include "fzofzp1.mm"
include "cncfioobd.mm"
include "fvres.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "mpan2.mm"
include "sylan9req.mm"
include "3adant1.mm"
include "raleqdv.mm"
include "bitrd.mm"
include "mpbid.mm"
include "eqimss.mm"
include "ssfiunibd.mm"
include "ad2antlr.mm"
include "elind.mm"
include "elun1.mm"
include "clt.mm"
include "crab.mm"
include "csup.mm"
include "cn.mm"
include "ad2antrr.mm"
include "elinel1.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "fveq2.mm"
include "cbvrabv.mm"
include "supeq1i.mm"
include "fourierdlem25.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "jca.mm"
include "syl6eleqr.mm"
include "impbida.mm"
include "rexbidv2.mm"
include "mpbird.mm"
include "elun2.mm"
include "dfss3.mm"
include "sseqtr4d.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "sselda.mm"
include "resubcld.mm"
include "syl5eqel.mm"
include "posdifd.mm"
include "syl6breqr.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "flcld.mm"
include "zred.mm"
include "remulcld.mm"
include "readdcld.mm"
include "cz.mm"
include "fvex.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "mpdan.mm"
include "eqtr2d.mm"
include "cbvralv.mm"
include "cioc.mm"
include "iocssicc.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fourierdlem4.mm"
include "sseldi.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "reximdv.mm"

theorem fourierdlem71
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cT: class T
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cL: class L
  let cM: class M
  let vw: setvar w
  let vb: setvar b
  let vt: setvar t
  let vj: setvar j
  assume fourierdlem71.dmf: |- ( ph -> dom F C_ RR )
  assume fourierdlem71.f: |- ( ph -> F : dom F --> RR )
  assume fourierdlem71.a: |- ( ph -> A e. RR )
  assume fourierdlem71.b: |- ( ph -> B e. RR )
  assume fourierdlem71.altb: |- ( ph -> A < B )
  assume fourierdlem71.t: |- T = ( B - A )
  assume fourierdlem71.7: |- ( ph -> M e. NN )
  assume fourierdlem71.q: |- ( ph -> Q : ( 0 ... M ) --> RR )
  assume fourierdlem71.q0: |- ( ph -> ( Q ` 0 ) = A )
  assume fourierdlem71.10: |- ( ph -> ( Q ` M ) = B )
  assume fourierdlem71.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem71.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) )
  assume fourierdlem71.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) )
  assume fourierdlem71.xpt: |- ( ( ( ph /\ x e. dom F ) /\ k e. ZZ ) -> ( x + ( k x. T ) ) e. dom F )
  assume fourierdlem71.fxpt: |- ( ( ( ph /\ x e. dom F ) /\ k e. ZZ ) -> ( F ` ( x + ( k x. T ) ) ) = ( F ` x ) )
  assume fourierdlem71.i: |- I = ( i e. ( 0 ..^ M ) |-> ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) )
  assume fourierdlem71.e: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B k
  disjoint B x
  disjoint k x
  disjoint B y
  disjoint F i
  disjoint F x
  disjoint i x
  disjoint F k
  disjoint i k
  disjoint F y
  disjoint I i
  disjoint I x
  disjoint I y
  disjoint L x
  disjoint M i
  disjoint M x
  disjoint M k
  disjoint Q i
  disjoint Q x
  disjoint Q k
  disjoint Q y
  disjoint R x
  disjoint T k
  disjoint T x
  disjoint T y
  disjoint i ph
  disjoint ph x
  disjoint k ph
  disjoint ph y
  disjoint k x
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint E w
  disjoint F b
  disjoint F t
  disjoint b i
  disjoint b t
  disjoint b x
  disjoint i t
  disjoint t x
  disjoint F w
  disjoint b w
  disjoint t w
  disjoint t y
  disjoint I b
  disjoint I t
  disjoint I w
  disjoint L b
  disjoint M b
  disjoint M j
  disjoint j k
  disjoint j x
  disjoint Q b
  disjoint Q j
  disjoint Q w
  disjoint R b
  disjoint b ph
  disjoint ph t
  disjoint ph w
  assert |- ( ph -> E. y e. RR A. x e. dom F ( abs ` ( F ` x ) ) <_ y )

  proof
    wph
    vx
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vx
    cA
    cB
    cicc
    co
    #
    cF
    cdm
    #
    cin
    #
    wral
    #
    vy
    cr
    wrex
    @4
    vx
    @6
    wral
    #
    vy
    cr
    wrex
    wph
    vw
    vy
    vx
    vy
    cQ
    crn
    #
    @6
    cin
    #
    cI
    crn
    #
    cuni
    #
    cpr
    #
    @2
    @7
    @14
    cfn
    wcel
    wph
    @11
    @13
    prfi
    a1i
    wph
    @0
    @14
    cuni
    #
    wcel
    #
    wa
    #
    @1
    @17
    @1
    @17
    @6
    cr
    @0
    cF
    wph
    @6
    cr
    cF
    wf
    #
    @16
    fourierdlem71.f
    adantr
    @17
    wph
    @0
    @11
    @13
    cun
    #
    wcel
    #
    @0
    @6
    wcel
    #
    wph
    @16
    simpl
    @17
    @0
    @15
    @19
    wph
    @16
    simpr
    @17
    @11
    cvv
    wcel
    #
    @13
    cvv
    wcel
    #
    @15
    @19
    wceq
    #
    wph
    @22
    @16
    wph
    cQ
    cvv
    wcel
    #
    @10
    cvv
    wcel
    @22
    wph
    cc0
    cM
    cfz
    co
    #
    cr
    cQ
    wf
    #
    @26
    cvv
    wcel
    #
    @25
    fourierdlem71.q
    @28
    wph
    cc0
    cM
    cfz
    ovex
    a1i
    @26
    cr
    cvv
    cQ
    fex
    syl2anc
    cQ
    cvv
    rnexg
    @10
    @6
    cvv
    inex1g
    3syl
    #
    adantr
    wph
    @23
    @16
    wph
    @12
    cvv
    wcel
    #
    @23
    @30
    wph
    cI
    cI
    vi
    cc0
    cM
    cfzo
    co
    #
    vi
    cv
    #
    cQ
    cfv
    #
    @32
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    cmpt
    cvv
    fourierdlem71.i
    vi
    @31
    @36
    cc0
    cM
    cfzo
    ovex
    mptex
    eqeltri
    rnex
    a1i
    @12
    cvv
    uniexg
    syl
    #
    adantr
    @11
    @13
    cvv
    cvv
    uniprg
    #
    syl2anc
    eleqtrd
    wph
    @20
    wa
    #
    @0
    @11
    wcel
    #
    @21
    @40
    @21
    @39
    @0
    @10
    @6
    elinel2
    #
    adantl
    @39
    @40
    wn
    #
    wa
    wph
    @0
    @13
    wcel
    #
    @21
    wph
    @20
    @42
    simpll
    @20
    @42
    @43
    wph
    @0
    @11
    @13
    elunnel1
    adantll
    wph
    @43
    wa
    #
    @0
    @32
    cI
    cfv
    #
    wcel
    #
    vi
    cI
    cdm
    #
    wrex
    #
    @21
    @43
    @48
    wph
    @43
    @48
    cI
    wfun
    @43
    @48
    wb
    vi
    @31
    @36
    cI
    fourierdlem71.i
    funmpt2
    vi
    @0
    cI
    elunirn
    ax-mp
    #
    biimpi
    adantl
    @44
    @46
    @21
    vi
    @47
    wph
    @32
    @47
    wcel
    #
    @46
    @21
    wi
    wi
    @43
    wph
    @50
    @46
    @21
    wph
    @50
    @46
    w3a
    @45
    @6
    @0
    wph
    @50
    @45
    @6
    wss
    @46
    wph
    @50
    wa
    #
    @45
    @36
    @6
    @51
    @32
    @31
    wcel
    #
    @36
    cvv
    wcel
    #
    @45
    @36
    wceq
    #
    @50
    @52
    wph
    @50
    @32
    @47
    @31
    @50
    id
    vi
    @31
    @36
    cI
    @33
    @35
    cioo
    ovex
    #
    fourierdlem71.i
    dmmpti
    #
    syl6eleq
    #
    adantl
    @53
    @51
    @55
    a1i
    vi
    @31
    @36
    cvv
    cI
    fourierdlem71.i
    fvmpt2
    #
    syl2anc
    @51
    cF
    @36
    cres
    #
    cdm
    @36
    wceq
    #
    @36
    @6
    wss
    @50
    wph
    @52
    @60
    @57
    wph
    @52
    wa
    #
    @59
    @36
    cc
    ccncf
    co
    wcel
    @36
    cc
    @59
    wf
    @60
    fourierdlem71.fcn
    @36
    cc
    @59
    cncff
    @36
    cc
    @59
    fdm
    3syl
    sylan2
    @36
    cF
    ssdmres
    sylibr
    eqsstrd
    3adant3
    wph
    @50
    @46
    simp3
    sseldd
    3exp
    adantr
    rexlimdv
    mpd
    #
    syl2anc
    pm2.61dan
    syl2anc
    ffvelrnd
    recnd
    abscld
    wph
    vw
    cv
    #
    @14
    wcel
    #
    wa
    #
    @63
    @11
    wceq
    #
    @4
    vx
    @63
    wral
    vy
    cr
    wrex
    #
    wph
    @66
    @67
    @64
    wph
    @66
    wa
    #
    @63
    cfn
    wcel
    @2
    cr
    wcel
    #
    vx
    @63
    wral
    @67
    @68
    @63
    @11
    cfn
    wph
    @66
    simpr
    wph
    @11
    cfn
    wcel
    #
    @66
    wph
    @10
    cfn
    wcel
    #
    @70
    wph
    @27
    @26
    cfn
    wcel
    @71
    fourierdlem71.q
    wph
    cc0
    cM
    fzfid
    @26
    cr
    cQ
    rnffi
    syl2anc
    @10
    @6
    infi
    syl
    adantr
    eqeltrd
    @68
    @69
    vx
    @63
    @68
    @0
    @63
    wcel
    #
    wa
    wph
    @40
    @69
    wph
    @66
    @72
    simpll
    @66
    @72
    @40
    wph
    @66
    @72
    wa
    @0
    @63
    @11
    @66
    @72
    simpr
    @66
    @72
    simpl
    eleqtrd
    adantll
    wph
    @40
    wa
    #
    @1
    @73
    @1
    @73
    @6
    cr
    @0
    cF
    wph
    @18
    @40
    fourierdlem71.f
    adantr
    @40
    @21
    wph
    @41
    adantl
    ffvelrnd
    recnd
    abscld
    syl2anc
    ralrimiva
    vy
    vx
    @63
    @2
    fimaxre3
    syl2anc
    adantlr
    @65
    @66
    wn
    #
    wa
    wph
    @63
    @13
    wceq
    #
    @67
    wph
    @64
    @74
    simpll
    @64
    @74
    @75
    wph
    @74
    @64
    @63
    @11
    wne
    @75
    @63
    @11
    neqne
    @63
    @11
    @13
    elprn1
    sylan2
    adantll
    wph
    @75
    wa
    #
    vt
    vb
    vx
    vy
    @12
    @2
    @63
    @12
    cfn
    wcel
    #
    @76
    @31
    cfn
    wcel
    @77
    cc0
    cM
    fzofi
    vi
    cI
    @31
    @36
    fourierdlem71.i
    rnmptfi
    ax-mp
    a1i
    @76
    @43
    wa
    @1
    wph
    @43
    @1
    cc
    wcel
    @75
    @44
    @1
    @44
    @6
    cr
    @0
    cF
    wph
    @18
    @43
    fourierdlem71.f
    adantr
    @62
    ffvelrnd
    recnd
    adantlr
    abscld
    wph
    vt
    cv
    #
    @12
    wcel
    #
    @2
    vb
    cv
    #
    cle
    wbr
    #
    vx
    @78
    wral
    #
    vb
    cr
    wrex
    #
    @75
    wph
    @79
    wa
    #
    @45
    @78
    wceq
    #
    vi
    @31
    wrex
    #
    @83
    @79
    @86
    wph
    @79
    @86
    cI
    @31
    wfn
    @79
    @86
    wb
    vi
    @31
    @36
    cI
    @55
    fourierdlem71.i
    fnmpti
    vi
    @31
    @78
    cI
    fvelrnb
    ax-mp
    biimpi
    adantl
    @84
    @85
    @83
    vi
    @31
    wph
    @52
    @85
    @83
    wi
    wi
    @79
    wph
    @52
    @85
    @83
    wph
    @52
    @85
    w3a
    #
    @0
    @59
    cfv
    #
    cabs
    cfv
    #
    @80
    cle
    wbr
    #
    vx
    @36
    wral
    #
    vb
    cr
    wrex
    #
    @83
    wph
    @52
    @92
    @85
    @61
    vb
    vx
    @33
    @35
    cR
    @59
    cL
    @61
    @26
    cr
    @32
    cQ
    wph
    @27
    @52
    fourierdlem71.q
    adantr
    #
    @52
    @32
    @26
    wcel
    wph
    @32
    cc0
    cM
    elfzofz
    adantl
    ffvelrnd
    @61
    @26
    cr
    @34
    cQ
    @93
    @52
    @34
    @26
    wcel
    wph
    cc0
    cM
    @32
    fzofzp1
    adantl
    ffvelrnd
    fourierdlem71.fcn
    fourierdlem71.l
    fourierdlem71.r
    cncfioobd
    3adant3
    @87
    @92
    @81
    vx
    @36
    wral
    #
    vb
    cr
    wrex
    #
    @83
    wph
    @52
    @92
    @95
    wb
    @85
    @61
    @91
    @94
    vb
    cr
    @61
    @90
    @81
    vx
    @36
    @0
    @36
    wcel
    #
    @90
    @81
    wb
    @61
    @96
    @89
    @2
    @80
    cle
    @96
    @88
    @1
    cabs
    @0
    @36
    cF
    fvres
    fveq2d
    breq1d
    adantl
    ralbidva
    rexbidv
    3adant3
    @87
    @94
    @82
    vb
    cr
    @87
    @81
    vx
    @36
    @78
    @52
    @85
    @36
    @78
    wceq
    wph
    @52
    @85
    @36
    @45
    @78
    @52
    @53
    @54
    @55
    @58
    mpan2
    #
    @85
    id
    sylan9req
    3adant1
    raleqdv
    rexbidv
    bitrd
    mpbid
    3exp
    adantr
    rexlimdv
    mpd
    adantlr
    @75
    @63
    @13
    wss
    wph
    @63
    @13
    eqimss
    adantl
    ssfiunibd
    syl2anc
    pm2.61dan
    wph
    @7
    @19
    @15
    wph
    @20
    vx
    @7
    wral
    @7
    @19
    wss
    wph
    @20
    vx
    @7
    wph
    @0
    @7
    wcel
    #
    wa
    #
    @0
    @10
    wcel
    #
    @20
    @99
    @100
    wa
    #
    @40
    @20
    @101
    @10
    @6
    @0
    @99
    @100
    simpr
    @98
    @21
    wph
    @100
    @0
    @5
    @6
    elinel2
    ad2antlr
    elind
    @0
    @11
    @13
    elun1
    syl
    @99
    @100
    wn
    #
    wa
    #
    @43
    @20
    @103
    @48
    @43
    @103
    @48
    @96
    vi
    @31
    wrex
    #
    @103
    @0
    cQ
    vi
    vj
    vk
    cv
    #
    cQ
    cfv
    #
    @0
    clt
    wbr
    #
    vk
    @31
    crab
    #
    cr
    clt
    csup
    cM
    wph
    cM
    cn
    wcel
    @98
    @102
    fourierdlem71.7
    ad2antrr
    wph
    @27
    @98
    @102
    fourierdlem71.q
    ad2antrr
    @99
    @0
    cc0
    cQ
    cfv
    #
    cM
    cQ
    cfv
    #
    cicc
    co
    #
    wcel
    @102
    @99
    @0
    @5
    @111
    @98
    @0
    @5
    wcel
    wph
    @0
    @5
    @6
    elinel1
    adantl
    @99
    cA
    @109
    cB
    @110
    cicc
    wph
    cA
    @109
    wceq
    @98
    wph
    @109
    cA
    fourierdlem71.q0
    eqcomd
    adantr
    wph
    cB
    @110
    wceq
    @98
    wph
    @110
    cB
    fourierdlem71.10
    eqcomd
    adantr
    oveq12d
    eleqtrd
    adantr
    @99
    @102
    simpr
    cr
    @108
    vj
    cv
    #
    cQ
    cfv
    #
    @0
    clt
    wbr
    #
    vj
    @31
    crab
    clt
    @107
    @114
    vk
    vj
    @31
    @105
    @112
    wceq
    @106
    @113
    @0
    clt
    @105
    @112
    cQ
    fveq2
    breq1d
    cbvrabv
    supeq1i
    fourierdlem25
    wph
    @48
    @104
    wb
    @98
    @102
    wph
    @46
    @96
    vi
    @47
    @31
    wph
    @50
    @46
    wa
    #
    @52
    @96
    wa
    #
    wph
    @115
    wa
    #
    @52
    @96
    @50
    @52
    wph
    @46
    @57
    ad2antrl
    #
    @117
    @0
    @45
    @36
    wph
    @50
    @46
    simprr
    @117
    @52
    @54
    @118
    @97
    syl
    eleqtrd
    jca
    wph
    @116
    wa
    #
    @50
    @46
    @52
    @50
    wph
    @96
    @52
    @32
    @31
    @47
    @52
    id
    @56
    syl6eleqr
    ad2antrl
    @119
    @0
    @36
    @45
    wph
    @52
    @96
    simprr
    @52
    @36
    @45
    wceq
    wph
    @96
    @52
    @45
    @36
    @97
    eqcomd
    ad2antrl
    eleqtrd
    jca
    impbida
    rexbidv2
    ad2antrr
    mpbird
    @49
    sylibr
    @0
    @13
    @11
    elun2
    syl
    pm2.61dan
    ralrimiva
    vx
    @7
    @19
    dfss3
    sylibr
    wph
    @22
    @23
    @24
    @29
    @37
    @38
    syl2anc
    sseqtr4d
    ssfiunibd
    wph
    @8
    @9
    vy
    cr
    wph
    @8
    @9
    wph
    @8
    wa
    #
    @4
    vx
    @6
    wph
    @8
    vx
    wph
    vx
    nfv
    @4
    vx
    @7
    nfra1
    nfan
    @120
    @21
    @4
    @120
    @21
    wa
    #
    @2
    @0
    cE
    cfv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    @3
    cle
    wph
    @21
    @2
    @124
    wceq
    @8
    wph
    @21
    wa
    #
    @1
    @123
    cabs
    @125
    @123
    @0
    cB
    @0
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @1
    @125
    @122
    @130
    cF
    @125
    @0
    cr
    wcel
    @130
    cr
    wcel
    @122
    @130
    wceq
    wph
    @6
    cr
    @0
    fourierdlem71.dmf
    sselda
    #
    @125
    @0
    @129
    @132
    @125
    @128
    cT
    @125
    @128
    @125
    @127
    @125
    @126
    cT
    @125
    cB
    @0
    wph
    cB
    cr
    wcel
    @21
    fourierdlem71.b
    adantr
    #
    @132
    resubcld
    wph
    cT
    cr
    wcel
    @21
    wph
    cT
    cB
    cA
    cmin
    co
    #
    cr
    fourierdlem71.t
    wph
    cB
    cA
    fourierdlem71.b
    fourierdlem71.a
    resubcld
    syl5eqel
    adantr
    #
    wph
    cT
    cc0
    wne
    @21
    wph
    cT
    wph
    cc0
    @134
    cT
    clt
    wph
    cA
    cB
    clt
    wbr
    #
    cc0
    @134
    clt
    wbr
    fourierdlem71.altb
    wph
    cA
    cB
    fourierdlem71.a
    fourierdlem71.b
    posdifd
    mpbid
    fourierdlem71.t
    syl6breqr
    gt0ne0d
    adantr
    redivcld
    flcld
    #
    zred
    @135
    remulcld
    readdcld
    vx
    cr
    @130
    cr
    cE
    fourierdlem71.e
    fvmpt2
    syl2anc
    #
    fveq2d
    @125
    @128
    cz
    wcel
    #
    @131
    @1
    wceq
    #
    @137
    @125
    @105
    cz
    wcel
    #
    wa
    #
    @0
    @105
    cT
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @1
    wceq
    #
    wi
    @125
    @139
    wa
    #
    @140
    wi
    vk
    @128
    @127
    cfl
    fvex
    #
    @105
    @128
    wceq
    #
    @142
    @147
    @146
    @140
    @149
    @141
    @139
    @125
    @105
    @128
    cz
    eleq1
    anbi2d
    #
    @149
    @145
    @131
    @1
    @149
    @144
    @130
    cF
    @149
    @143
    @129
    @0
    caddc
    @105
    @128
    cT
    cmul
    oveq1
    oveq2d
    #
    fveq2d
    eqeq1d
    imbi12d
    fourierdlem71.fxpt
    vtocl
    mpdan
    eqtr2d
    fveq2d
    adantlr
    @121
    @63
    cF
    cfv
    #
    cabs
    cfv
    #
    @3
    cle
    wbr
    #
    vw
    @7
    wral
    #
    @122
    @7
    wcel
    #
    @124
    @3
    cle
    wbr
    #
    @8
    @155
    wph
    @21
    @8
    @155
    @4
    @154
    vx
    vw
    @7
    @0
    @63
    wceq
    #
    @2
    @153
    @3
    cle
    @158
    @1
    @152
    cabs
    @0
    @63
    cF
    fveq2
    fveq2d
    breq1d
    cbvralv
    biimpi
    ad2antlr
    wph
    @21
    @156
    @8
    @125
    @5
    @6
    @122
    @125
    cA
    cB
    cioc
    co
    #
    @5
    @122
    cA
    cB
    iocssicc
    @125
    cr
    @159
    @0
    cE
    @125
    vy
    cA
    cB
    cT
    cE
    wph
    cA
    cr
    wcel
    @21
    fourierdlem71.a
    adantr
    @133
    wph
    @136
    @21
    fourierdlem71.altb
    adantr
    fourierdlem71.t
    cE
    vx
    cr
    @130
    cmpt
    vy
    cr
    @3
    cB
    @3
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    fourierdlem71.e
    vx
    vy
    cr
    @130
    @164
    @0
    @3
    wceq
    #
    @0
    @3
    @129
    @163
    caddc
    @165
    id
    @165
    @128
    @162
    cT
    cmul
    @165
    @127
    @161
    cfl
    @165
    @126
    @160
    cT
    cdiv
    @0
    @3
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    cbvmptv
    eqtri
    fourierdlem4
    @132
    ffvelrnd
    sseldi
    @125
    @122
    @130
    @6
    @138
    @125
    @139
    @130
    @6
    wcel
    #
    @137
    @142
    @144
    @6
    wcel
    #
    wi
    @147
    @166
    wi
    vk
    @128
    @148
    @149
    @142
    @147
    @167
    @166
    @150
    @149
    @144
    @130
    @6
    @151
    eleq1d
    imbi12d
    fourierdlem71.xpt
    vtocl
    mpdan
    eqeltrd
    elind
    adantlr
    @154
    @157
    vw
    @122
    @7
    @63
    @122
    wceq
    #
    @153
    @124
    @3
    cle
    @168
    @152
    @123
    cabs
    @63
    @122
    cF
    fveq2
    fveq2d
    breq1d
    rspccva
    syl2anc
    eqbrtrd
    ex
    ralrimi
    ex
    reximdv
    mpd
end
