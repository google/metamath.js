include "con0.mm"
include "wcel.mm"
include "cuni.mm"
include "cdif.mm"
include "ccrd.mm"
include "cfv.mm"
include "csuc.mm"
include "wa.mm"
include "cardon.mm"
include "onsuci.mm"
include "a1i.mm"
include "onelon.mm"
include "sylan.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wral.mm"
include "r19.21v.mm"
include "wb.mm"
include "word.mm"
include "wss.mm"
include "onordi.mm"
include "ordelss.mm"
include "sselda.mm"
include "biimt.mm"
include "syl.mm"
include "ralbidva.mm"
include "c0.mm"
include "cima.mm"
include "cif.mm"
include "csn.mm"
include "cun.mm"
include "onssi.mm"
include "simprl.mm"
include "sseldi.mm"
include "ttukeylem3.mm"
include "syldan.mm"
include "ad3antrrr.mm"
include "wn.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wf.mm"
include "wex.mm"
include "wrex.mm"
include "inss2.mm"
include "simpr.mm"
include "ciun.mm"
include "inss1.mm"
include "elpwid.mm"
include "wfn.mm"
include "wfun.mm"
include "cvv.mm"
include "cdm.mm"
include "crn.mm"
include "cmpt.mm"
include "tfr1.mm"
include "fnfun.mm"
include "funiunfv.mm"
include "mp2b.mm"
include "syl6sseqr.mm"
include "dfss3.mm"
include "eliun.mm"
include "ralbii.mm"
include "bitri.mm"
include "sylib.mm"
include "eleq2d.mm"
include "ac6sfi.mm"
include "syl2anc.mm"
include "wne.mm"
include "simp-4l.mm"
include "simprrl.mm"
include "adantr.mm"
include "frn.mm"
include "onss.mm"
include "sstrd.mm"
include "wfo.mm"
include "adantrr.mm"
include "ffn.mm"
include "dffn4.mm"
include "fofi.mm"
include "dm0rn0.mm"
include "fdm.mm"
include "eqeq1d.mm"
include "syl5bbr.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "ordunifi.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "simplrr.mm"
include "ad2antrr.mm"
include "rspcv.mm"
include "sylc.mm"
include "ffvelrn.mm"
include "adantl.mm"
include "ad2antrl.mm"
include "vex.mm"
include "rnex.mm"
include "ssonunii.mm"
include "simprr.mm"
include "fnfvelrn.mm"
include "elssuni.mm"
include "ttukeylem5.mm"
include "syl13anc.mm"
include "sseld.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "expimpd.mm"
include "impr.mm"
include "sylibr.mm"
include "ttukeylem2.mm"
include "syl12anc.mm"
include "0ss.mm"
include "mpanr2.mm"
include "mpdan.mm"
include "pm2.61ne.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "ex.mm"
include "ssrdv.mm"
include "ttukeylem1.mm"
include "mpbird.mm"
include "ifclda.mm"
include "uneq2.mm"
include "un0.mm"
include "syl5eqr.mm"
include "vuniex.mm"
include "sucid.mm"
include "wo.mm"
include "eloni.mm"
include "orduniorsuc.mm"
include "3syl.mm"
include "orcanai.mm"
include "syl5eleqr.mm"
include "ifbothda.mm"
include "eqeltrd.mm"
include "sylbird.mm"
include "com23.mm"
include "a2i.mm"
include "sylbi.mm"
include "tfis3.mm"
include "impd.mm"
include "mpcom.mm"

theorem ttukeylem6
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let va: setvar a
  let vy: setvar y
  let cD: class D
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume ttukeylem.1: |- ( ph -> F : ( card ` ( U. A \ B ) ) -1-1-onto-> ( U. A \ B ) )
  assume ttukeylem.2: |- ( ph -> B e. A )
  assume ttukeylem.3: |- ( ph -> A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) )
  assume ttukeylem.4: |- G = recs ( ( z e. _V |-> if ( dom z = U. dom z , if ( dom z = (/) , B , U. ran z ) , ( ( z ` U. dom z ) u. if ( ( ( z ` U. dom z ) u. { ( F ` U. dom z ) } ) e. A , { ( F ` U. dom z ) } , (/) ) ) ) ) )

  disjoint x z
  disjoint C x
  disjoint C z
  disjoint G x
  disjoint G z
  disjoint ph z
  disjoint A x
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint F x
  disjoint F z
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint x y
  disjoint y z
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint a f
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint G a
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G y
  disjoint a ph
  disjoint f ph
  disjoint ph u
  disjoint ph w
  disjoint ph y
  disjoint A a
  disjoint A f
  disjoint A u
  disjoint A w
  disjoint A y
  disjoint B a
  disjoint B f
  disjoint B u
  disjoint B w
  disjoint B y
  assert |- ( ( ph /\ C e. suc ( card ` ( U. A \ B ) ) ) -> ( G ` C ) e. A )

  proof
    cC
    con0
    wcel
    #
    wph
    cC
    cA
    cuni
    cB
    cdif
    #
    ccrd
    cfv
    #
    csuc
    #
    wcel
    #
    wa
    cC
    cG
    cfv
    #
    cA
    wcel
    #
    wph
    @3
    con0
    wcel
    #
    @4
    @0
    @7
    wph
    @2
    @1
    cardon
    onsuci
    #
    a1i
    @3
    cC
    onelon
    sylan
    @0
    wph
    @4
    @6
    wph
    vy
    cv
    #
    @3
    wcel
    #
    @9
    cG
    cfv
    #
    cA
    wcel
    #
    wi
    #
    wi
    #
    wph
    va
    cv
    #
    @3
    wcel
    #
    @15
    cG
    cfv
    #
    cA
    wcel
    #
    wi
    #
    wi
    #
    wph
    @4
    @6
    wi
    #
    wi
    vy
    va
    cC
    @9
    @15
    wceq
    #
    @13
    @19
    wph
    @22
    @10
    @16
    @12
    @18
    @9
    @15
    @3
    eleq1
    @22
    @11
    @17
    cA
    @9
    @15
    cG
    fveq2
    eleq1d
    imbi12d
    imbi2d
    @9
    cC
    wceq
    #
    @13
    @21
    wph
    @23
    @10
    @4
    @12
    @6
    @9
    cC
    @3
    eleq1
    @23
    @11
    @5
    cA
    @9
    cC
    cG
    fveq2
    eleq1d
    imbi12d
    imbi2d
    @20
    va
    @9
    wral
    #
    @14
    wi
    @9
    con0
    wcel
    #
    @24
    wph
    @19
    va
    @9
    wral
    #
    wi
    @14
    wph
    @19
    va
    @9
    r19.21v
    wph
    @26
    @13
    wph
    @10
    @26
    @12
    wph
    @10
    @26
    @12
    wi
    wph
    @10
    wa
    #
    @26
    @18
    va
    @9
    wral
    #
    @12
    @27
    @18
    @19
    va
    @9
    @27
    @15
    @9
    wcel
    wa
    @16
    @18
    @19
    wb
    @27
    @9
    @3
    @15
    wph
    @3
    word
    #
    @10
    @9
    @3
    wss
    @29
    wph
    @3
    @8
    onordi
    a1i
    @3
    @9
    ordelss
    sylan
    sselda
    @16
    @18
    biimt
    syl
    ralbidva
    wph
    @10
    @28
    @12
    wph
    @10
    @28
    wa
    #
    wa
    #
    @11
    @9
    @9
    cuni
    #
    wceq
    #
    @9
    c0
    wceq
    #
    cB
    cG
    @9
    cima
    cuni
    #
    cif
    #
    @32
    cG
    cfv
    #
    @37
    @32
    cF
    cfv
    csn
    #
    cun
    #
    cA
    wcel
    #
    @38
    c0
    cif
    #
    cun
    #
    cif
    #
    cA
    wph
    @30
    @25
    @11
    @43
    wceq
    @31
    @3
    con0
    @9
    @3
    @8
    onssi
    wph
    @10
    @28
    simprl
    sseldi
    #
    wph
    vx
    vz
    cA
    cB
    @9
    cF
    cG
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem.4
    ttukeylem3
    syldan
    @31
    @33
    @36
    @42
    cA
    @31
    @33
    wa
    #
    @34
    cB
    @35
    cA
    wph
    cB
    cA
    wcel
    #
    @30
    @33
    @34
    ttukeylem.2
    ad3antrrr
    @45
    @35
    cA
    wcel
    #
    @34
    wn
    @45
    @47
    @35
    cpw
    #
    cfn
    cin
    #
    cA
    wss
    #
    @45
    vw
    @49
    cA
    @45
    vw
    cv
    #
    @49
    wcel
    #
    @51
    cA
    wcel
    #
    @45
    @52
    wa
    #
    @51
    @9
    vf
    cv
    #
    wf
    #
    vu
    cv
    #
    @57
    @55
    cfv
    #
    cG
    cfv
    #
    wcel
    #
    vu
    @51
    wral
    #
    wa
    #
    vf
    wex
    #
    @53
    @54
    @51
    cfn
    wcel
    #
    @57
    vv
    cv
    #
    cG
    cfv
    #
    wcel
    #
    vv
    @9
    wrex
    #
    vu
    @51
    wral
    #
    @63
    @54
    @49
    cfn
    @51
    @48
    cfn
    inss2
    @45
    @52
    simpr
    #
    sseldi
    #
    @54
    @51
    vv
    @9
    @66
    ciun
    #
    wss
    #
    @69
    @54
    @51
    @35
    @72
    @54
    @51
    @35
    @54
    @49
    @48
    @51
    @48
    cfn
    inss1
    @70
    sseldi
    elpwid
    cG
    con0
    wfn
    cG
    wfun
    @72
    @35
    wceq
    cG
    vz
    cvv
    vz
    cv
    #
    cdm
    #
    @75
    cuni
    #
    wceq
    @75
    c0
    wceq
    cB
    @74
    crn
    cuni
    cif
    @76
    @74
    cfv
    #
    @77
    @76
    cF
    cfv
    csn
    #
    cun
    cA
    wcel
    @78
    c0
    cif
    cun
    cif
    cmpt
    ttukeylem.4
    tfr1
    con0
    cG
    fnfun
    vv
    @9
    cG
    funiunfv
    mp2b
    syl6sseqr
    @73
    @57
    @72
    wcel
    #
    vu
    @51
    wral
    @69
    vu
    @51
    @72
    dfss3
    @79
    @68
    vu
    @51
    vv
    @57
    @9
    @66
    eliun
    ralbii
    bitri
    sylib
    @67
    @60
    vu
    vv
    @51
    @9
    vf
    @65
    @58
    wceq
    @66
    @59
    @57
    @65
    @58
    cG
    fveq2
    eleq2d
    ac6sfi
    syl2anc
    @54
    @62
    @53
    vf
    @45
    @52
    @62
    @53
    @45
    @52
    @62
    wa
    #
    wa
    #
    @53
    c0
    cA
    wcel
    #
    @51
    c0
    @51
    c0
    cA
    eleq1
    @81
    @51
    c0
    wne
    #
    wa
    #
    wph
    @55
    crn
    #
    cuni
    #
    cG
    cfv
    #
    cA
    wcel
    #
    @51
    @87
    wss
    #
    @53
    wph
    @30
    @33
    @80
    @83
    simp-4l
    @84
    @86
    @9
    wcel
    @28
    @88
    @84
    @85
    @9
    @86
    @84
    @56
    @85
    @9
    wss
    #
    @81
    @56
    @83
    @45
    @52
    @56
    @61
    simprrl
    #
    adantr
    #
    @51
    @9
    @55
    frn
    #
    syl
    #
    @84
    @85
    con0
    wss
    #
    @85
    cfn
    wcel
    #
    @85
    c0
    wne
    #
    @86
    @85
    wcel
    @84
    @85
    @9
    con0
    @94
    @84
    @25
    @9
    con0
    wss
    #
    @31
    @25
    @33
    @80
    @83
    @44
    ad3antrrr
    @9
    onss
    #
    syl
    sstrd
    @84
    @64
    @51
    @85
    @55
    wfo
    #
    @96
    @81
    @64
    @83
    @45
    @52
    @64
    @62
    @71
    adantrr
    adantr
    @84
    @55
    @51
    wfn
    #
    @100
    @84
    @56
    @101
    @92
    @51
    @9
    @55
    ffn
    #
    syl
    @51
    @55
    dffn4
    sylib
    @51
    @85
    @55
    fofi
    syl2anc
    @81
    @97
    @83
    @81
    @85
    c0
    @51
    c0
    @85
    c0
    wceq
    @55
    cdm
    #
    c0
    wceq
    @81
    @51
    c0
    wceq
    @55
    dm0rn0
    @81
    @103
    @51
    c0
    @81
    @56
    @103
    @51
    wceq
    @91
    @51
    @9
    @55
    fdm
    syl
    eqeq1d
    syl5bbr
    necon3bid
    biimpar
    @85
    ordunifi
    syl3anc
    sseldd
    @45
    @28
    @80
    @83
    wph
    @10
    @28
    @33
    simplrr
    ad2antrr
    @18
    @88
    va
    @86
    @9
    @15
    @86
    wceq
    @17
    @87
    cA
    @15
    @86
    cG
    fveq2
    eleq1d
    rspcv
    sylc
    @84
    @57
    @87
    wcel
    #
    vu
    @51
    wral
    #
    @89
    @81
    @105
    @83
    @45
    @52
    @62
    @105
    @54
    @56
    @61
    @105
    @54
    @56
    wa
    @60
    @104
    vu
    @51
    @54
    @56
    @57
    @51
    wcel
    #
    @60
    @104
    wi
    @54
    @56
    @106
    wa
    #
    wa
    #
    @59
    @87
    @57
    @108
    wph
    @58
    con0
    wcel
    @86
    con0
    wcel
    #
    @58
    @86
    wss
    #
    @59
    @87
    wss
    wph
    @30
    @33
    @52
    @107
    simp-4l
    @108
    @9
    con0
    @58
    @108
    @25
    @98
    @31
    @25
    @33
    @52
    @107
    @44
    ad3antrrr
    @99
    syl
    #
    @107
    @58
    @9
    wcel
    @54
    @51
    @9
    @57
    @55
    ffvelrn
    adantl
    sseldd
    @108
    @95
    @109
    @108
    @85
    @9
    con0
    @56
    @90
    @54
    @106
    @93
    ad2antrl
    @111
    sstrd
    @85
    @55
    vf
    vex
    rnex
    ssonunii
    syl
    @108
    @58
    @85
    wcel
    #
    @110
    @108
    @101
    @106
    @112
    @56
    @101
    @54
    @106
    @102
    ad2antrl
    @54
    @56
    @106
    simprr
    @51
    @57
    @55
    fnfvelrn
    syl2anc
    @58
    @85
    elssuni
    syl
    wph
    vx
    vz
    cA
    cB
    @58
    @86
    cF
    cG
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem.4
    ttukeylem5
    syl13anc
    sseld
    anassrs
    ralimdva
    expimpd
    impr
    adantr
    vu
    @51
    @87
    dfss3
    sylibr
    wph
    vx
    cA
    cB
    @87
    @51
    cF
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem2
    syl12anc
    wph
    @82
    @30
    @33
    @80
    wph
    @46
    @82
    ttukeylem.2
    wph
    @46
    c0
    cB
    wss
    @82
    cB
    0ss
    wph
    vx
    cA
    cB
    cB
    c0
    cF
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem2
    mpanr2
    mpdan
    ad3antrrr
    pm2.61ne
    expr
    exlimdv
    mpd
    ex
    ssrdv
    wph
    @47
    @50
    wb
    @30
    @33
    wph
    vx
    cA
    cB
    @35
    cF
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem1
    ad2antrr
    mpbird
    adantr
    ifclda
    @40
    @40
    @37
    cA
    wcel
    #
    @42
    cA
    wcel
    @31
    @33
    wn
    #
    wa
    #
    @38
    c0
    @38
    @41
    wceq
    @39
    @42
    cA
    @38
    @41
    @37
    uneq2
    eleq1d
    c0
    @41
    wceq
    #
    @37
    @42
    cA
    @116
    @37
    @37
    c0
    cun
    @42
    @37
    un0
    c0
    @41
    @37
    uneq2
    syl5eqr
    eleq1d
    @115
    @40
    simpr
    @115
    @113
    @40
    wn
    @115
    @32
    @9
    wcel
    @28
    @113
    @115
    @32
    @32
    csuc
    #
    @9
    @32
    vy
    vuniex
    sucid
    @31
    @33
    @9
    @117
    wceq
    #
    @31
    @25
    @9
    word
    @33
    @118
    wo
    @44
    @9
    eloni
    @9
    orduniorsuc
    3syl
    orcanai
    syl5eleqr
    wph
    @10
    @28
    @114
    simplrr
    @18
    @113
    va
    @32
    @9
    @15
    @32
    wceq
    @17
    @37
    cA
    @15
    @32
    cG
    fveq2
    eleq1d
    rspcv
    sylc
    adantr
    ifbothda
    ifclda
    eqeltrd
    expr
    sylbird
    ex
    com23
    a2i
    sylbi
    a1i
    tfis3
    impd
    mpcom
end
