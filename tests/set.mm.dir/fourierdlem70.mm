include "crn.mm"
include "cuni.mm"
include "cpr.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cicc.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "prfi.mm"
include "a1i.mm"
include "wa.mm"
include "cr.mm"
include "cun.mm"
include "simpr.mm"
include "wceq.mm"
include "cvv.mm"
include "cc0.mm"
include "cfz.mm"
include "wf.mm"
include "ovex.mm"
include "fex.mm"
include "sylancl.mm"
include "rnexg.mm"
include "syl.mm"
include "cfzo.mm"
include "fzofi.mm"
include "c1.mm"
include "caddc.mm"
include "cioo.mm"
include "rnmptfi.mm"
include "ax-mp.mm"
include "elexi.mm"
include "uniex.mm"
include "uniprg.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "wss.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "reex.mm"
include "elmap.mm"
include "sylibr.mm"
include "jca.mm"
include "ralrimiva.mm"
include "jca32.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "mpbird.mm"
include "fourierdlem15.mm"
include "frn.mm"
include "sselda.mm"
include "adantlr.mm"
include "wn.mm"
include "simpll.mm"
include "elunnel1.mm"
include "adantll.mm"
include "cdm.mm"
include "wrex.mm"
include "wfun.mm"
include "funmpt2.mm"
include "elunirn.mm"
include "mp1i.mm"
include "mpbid.mm"
include "wi.mm"
include "w3a.mm"
include "id.mm"
include "dmmpti.mm"
include "syl6eleq.mm"
include "fvmpt2.mm"
include "adantl.mm"
include "ioossicc.mm"
include "cxr.mm"
include "rexrd.mm"
include "fourierdlem8.mm"
include "syl5ss.mm"
include "eqsstrd.mm"
include "3adant3.mm"
include "simp3.mm"
include "sseldd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "syldan.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "abscld.mm"
include "cle.mm"
include "fzfid.mm"
include "rnffi.mm"
include "eqeltrd.mm"
include "ad2antrr.mm"
include "simpl.mm"
include "ffvelrnd.mm"
include "fimaxre3.mm"
include "wne.mm"
include "neqne.mm"
include "elprn1.mm"
include "sylan2.mm"
include "cc.mm"
include "ax-resscn.mm"
include "fssd.mm"
include "wfn.mm"
include "fnmpti.mm"
include "fvelrnb.mm"
include "biimpi.mm"
include "cres.mm"
include "elfzofz.mm"
include "fzofzp1.mm"
include "cncfioobd.mm"
include "fvres.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "mpan2.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "raleqdv.mm"
include "3adant1.mm"
include "eqimss.mm"
include "ssfiunibd.mm"
include "wo.mm"
include "csup.mm"
include "oveq12d.mm"
include "fveq2.mm"
include "cbvrabv.mm"
include "supeq1i.mm"
include "fourierdlem25.mm"
include "eleq2d.mm"
include "rexbiia.mm"
include "eqcomi.mm"
include "rexeqi.mm"
include "sylib.mm"
include "ex.mm"
include "orrd.mm"
include "elun.mm"
include "dfss3.mm"
include "sseqtr4d.mm"

theorem fourierdlem70
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let cF: class F
  let cI: class I
  let cL: class L
  let cM: class M
  let vs: setvar s
  let vt: setvar t
  let vv: setvar v
  let vy: setvar y
  let vw: setvar w
  let vb: setvar b
  let vz: setvar z
  let vj: setvar j
  let vk: setvar k
  assume fourierdlem70.a: |- ( ph -> A e. RR )
  assume fourierdlem70.2: |- ( ph -> B e. RR )
  assume fourierdlem70.aleb: |- ( ph -> A <_ B )
  assume fourierdlem70.f: |- ( ph -> F : ( A [,] B ) --> RR )
  assume fourierdlem70.m: |- ( ph -> M e. NN )
  assume fourierdlem70.q: |- ( ph -> Q : ( 0 ... M ) --> RR )
  assume fourierdlem70.q0: |- ( ph -> ( Q ` 0 ) = A )
  assume fourierdlem70.qm: |- ( ph -> ( Q ` M ) = B )
  assume fourierdlem70.qlt: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( Q ` i ) < ( Q ` ( i + 1 ) ) )
  assume fourierdlem70.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem70.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) )
  assume fourierdlem70.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) )
  assume fourierdlem70.i: |- I = ( i e. ( 0 ..^ M ) |-> ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) )

  disjoint A i
  disjoint B i
  disjoint F i
  disjoint F s
  disjoint i s
  disjoint F x
  disjoint s x
  disjoint I i
  disjoint I s
  disjoint I x
  disjoint L s
  disjoint M i
  disjoint M s
  disjoint Q i
  disjoint Q s
  disjoint Q x
  disjoint R s
  disjoint i ph
  disjoint ph s
  disjoint ph x
  disjoint A t
  disjoint i t
  disjoint A v
  disjoint A y
  disjoint i v
  disjoint i y
  disjoint v y
  disjoint A w
  disjoint t w
  disjoint B t
  disjoint B v
  disjoint B y
  disjoint B w
  disjoint F b
  disjoint F t
  disjoint b i
  disjoint b s
  disjoint b t
  disjoint s t
  disjoint F w
  disjoint b w
  disjoint s w
  disjoint w x
  disjoint F z
  disjoint s z
  disjoint t z
  disjoint w z
  disjoint I b
  disjoint I t
  disjoint I w
  disjoint I z
  disjoint L b
  disjoint M b
  disjoint M j
  disjoint M k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint M v
  disjoint M y
  disjoint Q b
  disjoint Q t
  disjoint Q j
  disjoint Q k
  disjoint j t
  disjoint k t
  disjoint Q v
  disjoint Q w
  disjoint Q z
  disjoint R b
  disjoint b ph
  disjoint ph t
  disjoint ph w
  disjoint ph z
  disjoint k x
  assert |- ( ph -> E. x e. RR A. s e. ( A [,] B ) ( abs ` ( F ` s ) ) <_ x )

  proof
    wph
    vw
    vz
    vs
    vx
    cQ
    crn
    #
    cI
    crn
    #
    cuni
    #
    cpr
    #
    vs
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cA
    cB
    cicc
    co
    #
    @3
    cfn
    wcel
    wph
    @0
    @2
    prfi
    a1i
    wph
    @4
    @3
    cuni
    #
    wcel
    #
    wa
    #
    @5
    @10
    @5
    wph
    @9
    @4
    @7
    wcel
    #
    @5
    cr
    wcel
    wph
    @9
    @4
    @0
    @2
    cun
    #
    wcel
    #
    @11
    @10
    @4
    @8
    @12
    wph
    @9
    simpr
    wph
    @8
    @12
    wceq
    #
    @9
    wph
    @0
    cvv
    wcel
    #
    @2
    cvv
    wcel
    @14
    wph
    cQ
    cvv
    wcel
    #
    @15
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
    @17
    cvv
    wcel
    @16
    fourierdlem70.q
    cc0
    cM
    cfz
    ovex
    #
    @17
    cr
    cvv
    cQ
    fex
    sylancl
    cQ
    cvv
    rnexg
    syl
    @1
    @1
    cfn
    cc0
    cM
    cfzo
    co
    #
    cfn
    wcel
    #
    @1
    cfn
    wcel
    #
    cc0
    cM
    fzofi
    #
    vi
    cI
    @20
    vi
    cv
    #
    cQ
    cfv
    #
    @24
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
    fourierdlem70.i
    rnmptfi
    #
    ax-mp
    elexi
    uniex
    @0
    @2
    cvv
    cvv
    uniprg
    sylancl
    #
    adantr
    eleqtrd
    wph
    @13
    wa
    #
    @4
    @0
    wcel
    #
    @11
    wph
    @32
    @11
    @13
    wph
    @0
    @7
    @4
    wph
    @17
    @7
    cQ
    wf
    #
    @0
    @7
    wss
    wph
    cA
    cB
    vy
    cn
    cc0
    vv
    cv
    #
    cfv
    cA
    wceq
    vy
    cv
    #
    @34
    cfv
    cB
    wceq
    wa
    @24
    @34
    cfv
    @26
    @34
    cfv
    clt
    wbr
    vi
    cc0
    @35
    cfzo
    co
    wral
    wa
    vv
    cr
    cc0
    @35
    cfz
    co
    cmap
    co
    crab
    cmpt
    #
    cQ
    vi
    vy
    cM
    vv
    @36
    eqid
    #
    fourierdlem70.m
    wph
    cQ
    cM
    @36
    cfv
    wcel
    #
    cQ
    cr
    @17
    cmap
    co
    wcel
    #
    cc0
    cQ
    cfv
    #
    cA
    wceq
    #
    cM
    cQ
    cfv
    #
    cB
    wceq
    #
    wa
    #
    @25
    @27
    clt
    wbr
    #
    vi
    @20
    wral
    #
    wa
    wa
    #
    wph
    @39
    @44
    @46
    wph
    @18
    @39
    fourierdlem70.q
    cr
    @17
    cQ
    reex
    @19
    elmap
    sylibr
    wph
    @41
    @43
    fourierdlem70.q0
    fourierdlem70.qm
    jca
    wph
    @45
    vi
    @20
    fourierdlem70.qlt
    ralrimiva
    jca32
    wph
    cM
    cn
    wcel
    #
    @38
    @47
    wb
    fourierdlem70.m
    cA
    cB
    @36
    cQ
    vi
    vy
    cM
    vv
    @37
    fourierdlem2
    syl
    mpbird
    fourierdlem15
    #
    @17
    @7
    cQ
    frn
    syl
    sselda
    #
    adantlr
    @31
    @32
    wn
    #
    wa
    wph
    @4
    @2
    wcel
    #
    @11
    wph
    @13
    @51
    simpll
    @13
    @51
    @52
    wph
    @4
    @0
    @2
    elunnel1
    adantll
    wph
    @52
    wa
    #
    @4
    @24
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
    @11
    @53
    @52
    @57
    wph
    @52
    simpr
    cI
    wfun
    #
    @52
    @57
    wb
    @53
    vi
    @20
    @28
    cI
    fourierdlem70.i
    funmpt2
    #
    vi
    @4
    cI
    elunirn
    mp1i
    mpbid
    @53
    @55
    @11
    vi
    @56
    wph
    @24
    @56
    wcel
    #
    @55
    @11
    wi
    wi
    @52
    wph
    @60
    @55
    @11
    wph
    @60
    @55
    w3a
    @54
    @7
    @4
    wph
    @60
    @54
    @7
    wss
    @55
    wph
    @60
    wa
    #
    @54
    @28
    @7
    @60
    @54
    @28
    wceq
    #
    wph
    @60
    @24
    @20
    wcel
    #
    @28
    cvv
    wcel
    #
    @62
    @60
    @24
    @56
    @20
    @60
    id
    vi
    @20
    @28
    cI
    @25
    @27
    cioo
    ovex
    #
    fourierdlem70.i
    dmmpti
    #
    syl6eleq
    #
    @65
    vi
    @20
    @28
    cvv
    cI
    fourierdlem70.i
    fvmpt2
    #
    sylancl
    adantl
    @61
    @28
    @25
    @27
    cicc
    co
    @7
    @25
    @27
    ioossicc
    @61
    cA
    cB
    cQ
    @24
    cM
    wph
    cA
    cxr
    wcel
    @60
    wph
    cA
    fourierdlem70.a
    rexrd
    adantr
    wph
    cB
    cxr
    wcel
    @60
    wph
    cB
    fourierdlem70.2
    rexrd
    adantr
    wph
    @33
    @60
    @49
    adantr
    @60
    @63
    wph
    @67
    adantl
    fourierdlem8
    syl5ss
    eqsstrd
    3adant3
    wph
    @60
    @55
    simp3
    sseldd
    3exp
    adantr
    rexlimdv
    mpd
    #
    syl2anc
    pm2.61dan
    syldan
    wph
    @7
    cr
    @4
    cF
    fourierdlem70.f
    ffvelrnda
    syldan
    recnd
    abscld
    wph
    vw
    cv
    #
    @3
    wcel
    #
    wa
    #
    @70
    @0
    wceq
    #
    @6
    vz
    cv
    cle
    wbr
    vs
    @70
    wral
    vz
    cr
    wrex
    #
    @72
    @73
    wa
    @70
    cfn
    wcel
    #
    @6
    cr
    wcel
    #
    vs
    @70
    wral
    #
    @74
    wph
    @73
    @75
    @71
    wph
    @73
    wa
    #
    @70
    @0
    cfn
    wph
    @73
    simpr
    @78
    @18
    @17
    cfn
    wcel
    @0
    cfn
    wcel
    wph
    @18
    @73
    fourierdlem70.q
    adantr
    @78
    cc0
    cM
    fzfid
    @17
    cr
    cQ
    rnffi
    syl2anc
    eqeltrd
    adantlr
    wph
    @73
    @77
    @71
    @78
    @76
    vs
    @70
    @78
    @4
    @70
    wcel
    #
    wa
    #
    @5
    @80
    @5
    @80
    @7
    cr
    @4
    cF
    wph
    @7
    cr
    cF
    wf
    @73
    @79
    fourierdlem70.f
    ad2antrr
    @80
    wph
    @32
    @11
    wph
    @73
    @79
    simpll
    @73
    @79
    @32
    wph
    @73
    @79
    wa
    @4
    @70
    @0
    @73
    @79
    simpr
    @73
    @79
    simpl
    eleqtrd
    adantll
    @50
    syl2anc
    ffvelrnd
    recnd
    abscld
    ralrimiva
    adantlr
    vz
    vs
    @70
    @6
    fimaxre3
    syl2anc
    @72
    @73
    wn
    #
    wa
    wph
    @70
    @2
    wceq
    #
    @74
    wph
    @71
    @81
    simpll
    @71
    @81
    @82
    wph
    @81
    @71
    @70
    @0
    wne
    @82
    @70
    @0
    neqne
    @70
    @0
    @2
    elprn1
    sylan2
    adantll
    wph
    @82
    wa
    #
    vt
    vb
    vs
    vz
    @1
    @6
    @70
    @21
    @22
    @83
    @23
    @29
    mp1i
    @83
    @52
    wa
    #
    @5
    @84
    @7
    cc
    @4
    cF
    wph
    @7
    cc
    cF
    wf
    @82
    @52
    wph
    @7
    cr
    cc
    cF
    fourierdlem70.f
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    fssd
    ad2antrr
    wph
    @52
    @11
    @82
    @69
    adantlr
    ffvelrnd
    abscld
    wph
    vt
    cv
    #
    @1
    wcel
    #
    @6
    vb
    cv
    #
    cle
    wbr
    #
    vs
    @85
    wral
    #
    vb
    cr
    wrex
    #
    @82
    wph
    @86
    wa
    #
    @54
    @85
    wceq
    #
    vi
    @20
    wrex
    #
    @90
    @86
    @93
    wph
    @86
    @93
    cI
    @20
    wfn
    @86
    @93
    wb
    vi
    @20
    @28
    cI
    @65
    fourierdlem70.i
    fnmpti
    vi
    @20
    @85
    cI
    fvelrnb
    ax-mp
    biimpi
    adantl
    @91
    @92
    @90
    vi
    @20
    wph
    @63
    @92
    @90
    wi
    wi
    @86
    wph
    @63
    @92
    @90
    wph
    @63
    @92
    w3a
    @88
    vs
    @28
    wral
    #
    vb
    cr
    wrex
    #
    @90
    wph
    @63
    @95
    @92
    wph
    @63
    wa
    #
    @4
    cF
    @28
    cres
    #
    cfv
    #
    cabs
    cfv
    #
    @87
    cle
    wbr
    #
    vs
    @28
    wral
    #
    vb
    cr
    wrex
    @95
    @96
    vb
    vs
    @25
    @27
    cR
    @97
    cL
    @96
    @17
    cr
    @24
    cQ
    wph
    @18
    @63
    fourierdlem70.q
    adantr
    #
    @63
    @24
    @17
    wcel
    wph
    @24
    cc0
    cM
    elfzofz
    adantl
    ffvelrnd
    @96
    @17
    cr
    @26
    cQ
    @102
    @63
    @26
    @17
    wcel
    wph
    cc0
    cM
    @24
    fzofzp1
    adantl
    ffvelrnd
    fourierdlem70.fcn
    fourierdlem70.l
    fourierdlem70.r
    cncfioobd
    @96
    @101
    @94
    vb
    cr
    @96
    @100
    @88
    vs
    @28
    @4
    @28
    wcel
    #
    @100
    @88
    wb
    @96
    @103
    @99
    @6
    @87
    cle
    @103
    @98
    @5
    cabs
    @4
    @28
    cF
    fvres
    fveq2d
    breq1d
    adantl
    ralbidva
    rexbidv
    mpbid
    3adant3
    @63
    @92
    @95
    @90
    wb
    wph
    @63
    @92
    wa
    #
    @94
    @89
    vb
    cr
    @104
    @88
    vs
    @28
    @85
    @104
    @28
    @54
    @85
    @63
    @28
    @54
    wceq
    @92
    @63
    @54
    @28
    @63
    @64
    @62
    @65
    @68
    mpan2
    #
    eqcomd
    adantr
    @63
    @92
    simpr
    eqtrd
    raleqdv
    rexbidv
    3adant1
    mpbid
    3exp
    adantr
    rexlimdv
    mpd
    adantlr
    @82
    @70
    @2
    wss
    wph
    @70
    @2
    eqimss
    adantl
    ssfiunibd
    syl2anc
    pm2.61dan
    wph
    @7
    @12
    @8
    wph
    @85
    @12
    wcel
    #
    vt
    @7
    wral
    @7
    @12
    wss
    wph
    @106
    vt
    @7
    wph
    @85
    @7
    wcel
    #
    wa
    #
    @85
    @0
    wcel
    #
    @85
    @2
    wcel
    #
    wo
    @106
    @108
    @109
    @110
    @108
    @109
    wn
    #
    @110
    @108
    @111
    wa
    #
    @110
    @85
    @54
    wcel
    #
    vi
    @56
    wrex
    #
    @112
    @113
    vi
    @20
    wrex
    #
    @114
    @112
    @85
    @28
    wcel
    #
    vi
    @20
    wrex
    @115
    @112
    @85
    cQ
    vi
    vj
    vk
    cv
    #
    cQ
    cfv
    #
    @85
    clt
    wbr
    #
    vk
    @20
    crab
    #
    cr
    clt
    csup
    cM
    wph
    @48
    @107
    @111
    fourierdlem70.m
    ad2antrr
    wph
    @18
    @107
    @111
    fourierdlem70.q
    ad2antrr
    @108
    @85
    @40
    @42
    cicc
    co
    #
    wcel
    @111
    @108
    @85
    @7
    @121
    wph
    @107
    simpr
    wph
    @7
    @121
    wceq
    @107
    wph
    cA
    @40
    cB
    @42
    cicc
    wph
    @40
    cA
    fourierdlem70.q0
    eqcomd
    wph
    @42
    cB
    fourierdlem70.qm
    eqcomd
    oveq12d
    adantr
    eleqtrd
    adantr
    @108
    @111
    simpr
    cr
    @120
    vj
    cv
    #
    cQ
    cfv
    #
    @85
    clt
    wbr
    #
    vj
    @20
    crab
    clt
    @119
    @124
    vk
    vj
    @20
    @117
    @122
    wceq
    @118
    @123
    @85
    clt
    @117
    @122
    cQ
    fveq2
    breq1d
    cbvrabv
    supeq1i
    fourierdlem25
    @113
    @116
    vi
    @20
    @63
    @54
    @28
    @85
    @105
    eleq2d
    rexbiia
    sylibr
    @113
    vi
    @20
    @56
    @56
    @20
    @66
    eqcomi
    rexeqi
    sylib
    @58
    @110
    @114
    wb
    @112
    @59
    vi
    @85
    cI
    elunirn
    mp1i
    mpbird
    ex
    orrd
    @85
    @0
    @2
    elun
    sylibr
    ralrimiva
    vt
    @7
    @12
    dfss3
    sylibr
    @30
    sseqtr4d
    ssfiunibd
end
