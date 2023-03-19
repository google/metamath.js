include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "wi.mm"
include "cr.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "caddc.mm"
include "cicc.mm"
include "wcel.mm"
include "1re.mm"
include "resubcl.mm"
include "sylancl.mm"
include "peano2re.mm"
include "syl.mm"
include "cc.mm"
include "cpr.mm"
include "ccpn.mm"
include "cres.mm"
include "reelprrecn.mm"
include "crn.mm"
include "cint.mm"
include "wss.mm"
include "cn0.mm"
include "wfn.mm"
include "ssid.mm"
include "fncpn.mm"
include "ax-mp.mm"
include "1nn0.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "intss1.mm"
include "cz.mm"
include "cply.mm"
include "plycpn.mm"
include "sseldi.mm"
include "cpnres.mm"
include "sylancr.mm"
include "cima.mm"
include "df-ima.mm"
include "wf.mm"
include "zssre.mm"
include "ax-resscn.mm"
include "plyss.mm"
include "plyreres.mm"
include "frn.mm"
include "syl5eqss.mm"
include "cdm.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "syl6ss.mm"
include "wceq.mm"
include "plyf.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "c1lip3.mm"
include "wa.mm"
include "w3a.mm"
include "simp2.mm"
include "recnd.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "abssubd.mm"
include "simp3.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "1red.mm"
include "elicc4abs.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "cc0.mm"
include "subidd.mm"
include "fveq2d.mm"
include "abs0.mm"
include "0le1.mm"
include "eqbrtri.mm"
include "syl6eqbr.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "breq12d.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "rspc2v.mm"
include "simp1l.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "ffvelrnd.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "sylibd.mm"
include "3exp.mm"
include "com34.mm"
include "com23.mm"
include "ralrimdv.mm"
include "reximdva.mm"
include "mpd.mm"
include "cdiv.mm"
include "cif.mm"
include "1rp.mm"
include "a1i.mm"
include "wn.mm"
include "wne.mm"
include "recn.mm"
include "adantl.mm"
include "df-ne.mm"
include "biimpri.mm"
include "absrpcl.mm"
include "syl2an.mm"
include "rpreccld.mm"
include "ifclda.mm"
include "wo.mm"
include "eqid.mm"
include "eqif.mm"
include "mpbi.mm"
include "simplrr.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "resubcld.mm"
include "abscld.mm"
include "mul02d.mm"
include "breqtrd.mm"
include "absge0d.mm"
include "0re.mm"
include "letri3.mm"
include "mpbir2and.mm"
include "ax-1cn.mm"
include "mul01i.mm"
include "syl6eq.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "simpllr.mm"
include "sylancom.mm"
include "rpcnne0d.mm"
include "divrec2.mm"
include "3expb.mm"
include "simplr.mm"
include "remulcld.mm"
include "simprr.mm"
include "leabs.mm"
include "ad2antlr.mm"
include "lemul1ad.mm"
include "letrd.mm"
include "ledivmuld.mm"
include "eqbrtrrd.mm"
include "sylan2br.mm"
include "jaod.mm"
include "mpi.mm"
include "expr.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"

theorem aalioulem3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cN: class N
  let vr: setvar r
  let vp: setvar p
  let vq: setvar q
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume aalioulem2.a: |- N = ( deg ` F )
  assume aalioulem2.b: |- ( ph -> F e. ( Poly ` ZZ ) )
  assume aalioulem2.c: |- ( ph -> N e. NN )
  assume aalioulem2.d: |- ( ph -> A e. RR )
  assume aalioulem3.e: |- ( ph -> ( F ` A ) = 0 )

  disjoint ph x
  disjoint ph r
  disjoint r x
  disjoint A x
  disjoint A r
  disjoint F x
  disjoint F r
  disjoint p ph
  disjoint ph q
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint p x
  disjoint q x
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint p q
  disjoint p r
  disjoint a p
  disjoint b p
  disjoint c p
  disjoint d p
  disjoint q r
  disjoint a q
  disjoint b q
  disjoint c q
  disjoint d q
  disjoint a r
  disjoint b r
  disjoint c r
  disjoint d r
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint A p
  disjoint A q
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint F p
  disjoint F q
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  assert |- ( ph -> E. x e. RR+ A. r e. RR ( ( abs ` ( A - r ) ) <_ 1 -> ( x x. ( abs ` ( F ` r ) ) ) <_ ( abs ` ( A - r ) ) ) )

  proof
    wph
    cA
    vr
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    @0
    cF
    cfv
    #
    cabs
    cfv
    #
    va
    cv
    #
    @2
    cmul
    co
    #
    cle
    wbr
    #
    wi
    #
    vr
    cr
    wral
    #
    va
    cr
    wrex
    #
    @3
    vx
    cv
    #
    @5
    cmul
    co
    #
    @2
    cle
    wbr
    #
    wi
    #
    vr
    cr
    wral
    #
    vx
    crp
    wrex
    #
    wph
    vc
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    @18
    @20
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vc
    cA
    c1
    cmin
    co
    #
    cA
    c1
    caddc
    co
    #
    cicc
    co
    #
    wral
    vb
    @30
    wral
    #
    va
    cr
    wrex
    @11
    wph
    vb
    vc
    @28
    @29
    va
    cF
    wph
    cA
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @28
    cr
    wcel
    #
    aalioulem2.d
    1re
    cA
    c1
    resubcl
    sylancl
    #
    wph
    @32
    @29
    cr
    wcel
    #
    aalioulem2.d
    cA
    peano2re
    syl
    #
    wph
    cr
    cr
    cc
    cpr
    wcel
    cF
    c1
    cc
    ccpn
    cfv
    #
    cfv
    #
    wcel
    cF
    cr
    cres
    #
    c1
    cr
    ccpn
    cfv
    cfv
    wcel
    reelprrecn
    wph
    @38
    crn
    #
    cint
    #
    @39
    cF
    @39
    @41
    wcel
    #
    @42
    @39
    wss
    @38
    cn0
    wfn
    #
    c1
    cn0
    wcel
    @43
    cc
    cc
    wss
    @44
    cc
    ssid
    cc
    fncpn
    ax-mp
    1nn0
    cn0
    c1
    @38
    fnfvelrn
    mp2an
    @39
    @41
    intss1
    ax-mp
    wph
    cF
    cz
    cply
    cfv
    #
    wcel
    #
    cF
    @42
    wcel
    aalioulem2.b
    cz
    cF
    plycpn
    syl
    sseldi
    cr
    cF
    c1
    cpnres
    sylancr
    wph
    cF
    cr
    cima
    @40
    crn
    #
    cr
    cF
    cr
    df-ima
    wph
    cr
    cr
    @40
    wf
    #
    @47
    cr
    wss
    wph
    cF
    cr
    cply
    cfv
    #
    wcel
    @48
    wph
    @45
    @49
    cF
    cz
    cr
    wss
    cr
    cc
    wss
    @45
    @49
    wss
    zssre
    ax-resscn
    cz
    cr
    plyss
    mp2an
    aalioulem2.b
    sseldi
    cF
    plyreres
    syl
    cr
    cr
    @40
    frn
    syl
    syl5eqss
    wph
    @30
    cc
    cF
    cdm
    #
    wph
    @30
    cr
    cc
    wph
    @34
    @36
    @30
    cr
    wss
    @35
    @37
    @28
    @29
    iccssre
    syl2anc
    ax-resscn
    syl6ss
    wph
    cc
    cc
    cF
    wf
    #
    @50
    cc
    wceq
    wph
    @46
    @51
    aalioulem2.b
    cz
    cF
    plyf
    syl
    #
    cc
    cc
    cF
    fdm
    syl
    sseqtr4d
    c1lip3
    wph
    @31
    @10
    va
    cr
    wph
    @6
    cr
    wcel
    #
    wa
    #
    @31
    @9
    vr
    cr
    @54
    @0
    cr
    wcel
    #
    @31
    @9
    @54
    @55
    @3
    @31
    @8
    @54
    @55
    @3
    @31
    @8
    wi
    @54
    @55
    @3
    w3a
    #
    @31
    cA
    cF
    cfv
    #
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    cle
    wbr
    #
    @8
    @56
    @0
    @30
    wcel
    #
    cA
    @30
    wcel
    #
    @31
    @60
    wi
    @56
    @61
    @0
    cA
    cmin
    co
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    @56
    @63
    @2
    c1
    cle
    @56
    @0
    cA
    @56
    @0
    @54
    @55
    @3
    simp2
    #
    recnd
    #
    @56
    cA
    @54
    @55
    @32
    @3
    wph
    @32
    @53
    aalioulem2.d
    adantr
    3ad2ant1
    #
    recnd
    abssubd
    @54
    @55
    @3
    simp3
    eqbrtrd
    @56
    @32
    @33
    @55
    @61
    @64
    wb
    @67
    @56
    1red
    @65
    cA
    c1
    @0
    elicc4abs
    syl3anc
    mpbird
    @54
    @55
    @62
    @3
    wph
    @62
    @53
    wph
    @62
    cA
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    wph
    @69
    cc0
    cabs
    cfv
    #
    c1
    cle
    wph
    @68
    cc0
    cabs
    wph
    cA
    wph
    cA
    aalioulem2.d
    recnd
    subidd
    fveq2d
    @71
    cc0
    c1
    cle
    abs0
    0le1
    eqbrtri
    syl6eqbr
    wph
    @32
    @33
    @32
    @62
    @70
    wb
    aalioulem2.d
    wph
    1red
    aalioulem2.d
    cA
    c1
    cA
    elicc4abs
    syl3anc
    mpbird
    adantr
    3ad2ant1
    @27
    @60
    @19
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    @18
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    vb
    vc
    @0
    cA
    @30
    @30
    @20
    @0
    wceq
    #
    @23
    @73
    @26
    @76
    cle
    @77
    @22
    @72
    cabs
    @77
    @21
    @4
    @19
    cmin
    @20
    @0
    cF
    fveq2
    oveq2d
    fveq2d
    @77
    @25
    @75
    @6
    cmul
    @77
    @24
    @74
    cabs
    @20
    @0
    @18
    cmin
    oveq2
    fveq2d
    oveq2d
    breq12d
    @18
    cA
    wceq
    #
    @73
    @59
    @76
    @7
    cle
    @78
    @72
    @58
    cabs
    @78
    @19
    @57
    @4
    cmin
    @18
    cA
    cF
    fveq2
    oveq1d
    fveq2d
    @78
    @75
    @2
    @6
    cmul
    @78
    @74
    @1
    cabs
    @18
    cA
    @0
    cmin
    oveq1
    fveq2d
    oveq2d
    breq12d
    rspc2v
    syl2anc
    @56
    @59
    @5
    @7
    cle
    @56
    @59
    @4
    @57
    cmin
    co
    #
    cabs
    cfv
    @5
    @56
    @57
    @4
    @56
    @57
    cc0
    cc
    @56
    wph
    @57
    cc0
    wceq
    wph
    @53
    @55
    @3
    simp1l
    aalioulem3.e
    syl
    #
    0cn
    syl6eqel
    @56
    cc
    cc
    @0
    cF
    @54
    @55
    @51
    @3
    wph
    @51
    @53
    @52
    adantr
    3ad2ant1
    @66
    ffvelrnd
    #
    abssubd
    @56
    @79
    @4
    cabs
    @56
    @79
    @4
    cc0
    cmin
    co
    @4
    @56
    @57
    cc0
    @4
    cmin
    @80
    oveq2d
    @56
    @4
    @81
    subid1d
    eqtrd
    fveq2d
    eqtrd
    breq1d
    sylibd
    3exp
    com34
    com23
    ralrimdv
    reximdva
    mpd
    wph
    @10
    @17
    va
    cr
    @54
    @6
    cc0
    wceq
    #
    c1
    c1
    @6
    cabs
    cfv
    #
    cdiv
    co
    #
    cif
    #
    crp
    wcel
    @10
    @3
    @85
    @5
    cmul
    co
    #
    @2
    cle
    wbr
    #
    wi
    #
    vr
    cr
    wral
    #
    @17
    @54
    @82
    c1
    @84
    crp
    c1
    crp
    wcel
    @54
    @82
    wa
    1rp
    a1i
    @54
    @82
    wn
    #
    wa
    @83
    @54
    @6
    cc
    wcel
    #
    @6
    cc0
    wne
    #
    @83
    crp
    wcel
    #
    @90
    @53
    @91
    wph
    @6
    recn
    adantl
    @92
    @90
    @6
    cc0
    df-ne
    #
    biimpri
    @6
    absrpcl
    #
    syl2an
    rpreccld
    ifclda
    @54
    @9
    @88
    vr
    cr
    @54
    @55
    wa
    @8
    @87
    @3
    @54
    @55
    @8
    @87
    @54
    @55
    @8
    wa
    #
    wa
    #
    @82
    @85
    c1
    wceq
    #
    wa
    #
    @90
    @85
    @84
    wceq
    #
    wa
    #
    wo
    #
    @87
    @85
    @85
    wceq
    @102
    @85
    eqid
    @82
    @85
    c1
    @84
    eqif
    mpbi
    @97
    @99
    @87
    @101
    @97
    @82
    @98
    @87
    @97
    @82
    wa
    #
    @87
    @98
    c1
    @5
    cmul
    co
    #
    @2
    cle
    wbr
    @103
    @104
    cc0
    @2
    cle
    @103
    @104
    c1
    cc0
    cmul
    co
    cc0
    @103
    @5
    cc0
    c1
    cmul
    @103
    @5
    cc0
    wceq
    #
    @5
    cc0
    cle
    wbr
    #
    cc0
    @5
    cle
    wbr
    #
    @103
    @5
    @7
    cc0
    cle
    @54
    @55
    @8
    @82
    simplrr
    @103
    @7
    cc0
    @2
    cmul
    co
    #
    cc0
    @82
    @7
    @108
    wceq
    @97
    @6
    cc0
    @2
    cmul
    oveq1
    adantl
    @103
    @2
    @97
    @2
    cc
    wcel
    @82
    @97
    @2
    @97
    @1
    @97
    @1
    @97
    cA
    @0
    wph
    @32
    @53
    @96
    aalioulem2.d
    ad2antrr
    @54
    @55
    @8
    simprl
    #
    resubcld
    recnd
    #
    abscld
    #
    recnd
    adantr
    mul02d
    eqtrd
    breqtrd
    @103
    @4
    @97
    @4
    cc
    wcel
    @82
    @97
    cc
    cc
    @0
    cF
    wph
    @51
    @53
    @96
    @52
    ad2antrr
    @97
    @0
    @109
    recnd
    ffvelrnd
    #
    adantr
    absge0d
    @103
    @5
    cr
    wcel
    #
    cc0
    cr
    wcel
    @105
    @106
    @107
    wa
    wb
    @97
    @113
    @82
    @97
    @4
    @112
    abscld
    #
    adantr
    0re
    @5
    cc0
    letri3
    sylancl
    mpbir2and
    oveq2d
    c1
    ax-1cn
    mul01i
    syl6eq
    @103
    @1
    @97
    @1
    cc
    wcel
    @82
    @110
    adantr
    absge0d
    eqbrtrd
    @98
    @86
    @104
    @2
    cle
    @85
    c1
    @5
    cmul
    oveq1
    breq1d
    syl5ibrcom
    expimpd
    @97
    @90
    @100
    @87
    @97
    @90
    wa
    @87
    @100
    @84
    @5
    cmul
    co
    #
    @2
    cle
    wbr
    #
    @90
    @97
    @92
    @116
    @94
    @97
    @92
    wa
    #
    @5
    @83
    cdiv
    co
    #
    @115
    @2
    cle
    @117
    @5
    cc
    wcel
    #
    @83
    cc
    wcel
    #
    @83
    cc0
    wne
    #
    wa
    @118
    @115
    wceq
    #
    @117
    @5
    @97
    @113
    @92
    @114
    adantr
    #
    recnd
    @117
    @83
    @97
    @92
    @91
    @93
    @117
    @6
    wph
    @53
    @96
    @92
    simpllr
    recnd
    @95
    sylancom
    #
    rpcnne0d
    @119
    @120
    @121
    @122
    @5
    @83
    divrec2
    3expb
    syl2anc
    @117
    @118
    @2
    cle
    wbr
    @5
    @83
    @2
    cmul
    co
    #
    cle
    wbr
    #
    @97
    @126
    @92
    @97
    @5
    @7
    @125
    @114
    @97
    @6
    @2
    wph
    @53
    @96
    simplr
    #
    @111
    remulcld
    @97
    @83
    @2
    @97
    @6
    @97
    @6
    @127
    recnd
    abscld
    #
    @111
    remulcld
    @54
    @55
    @8
    simprr
    @97
    @6
    @83
    @2
    @127
    @128
    @111
    @97
    @1
    @110
    absge0d
    @53
    @6
    @83
    cle
    wbr
    wph
    @96
    @6
    leabs
    ad2antlr
    lemul1ad
    letrd
    adantr
    @117
    @5
    @2
    @83
    @123
    @97
    @2
    cr
    wcel
    @92
    @111
    adantr
    @124
    ledivmuld
    mpbird
    eqbrtrrd
    sylan2br
    @100
    @86
    @115
    @2
    cle
    @85
    @84
    @5
    cmul
    oveq1
    breq1d
    syl5ibrcom
    expimpd
    jaod
    mpi
    expr
    imim2d
    ralimdva
    @16
    @89
    vx
    @85
    crp
    @12
    @85
    wceq
    #
    @15
    @88
    vr
    cr
    @129
    @14
    @87
    @3
    @129
    @13
    @86
    @2
    cle
    @12
    @85
    @5
    cmul
    oveq1
    breq1d
    imbi2d
    ralbidv
    rspcev
    syl6an
    rexlimdva
    mpd
end
