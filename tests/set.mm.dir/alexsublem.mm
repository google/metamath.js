include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wss.mm"
include "wa.mm"
include "c0.mm"
include "cflim.mm"
include "co.mm"
include "wcel.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "eldif.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "biimpa.mm"
include "adantlr.mm"
include "tg2.mm"
include "syl.mm"
include "cfil.mm"
include "cufil.mm"
include "ufilfil.mm"
include "ad3antrrr.mm"
include "cint.mm"
include "csn.mm"
include "wb.mm"
include "cvv.mm"
include "elfvexd.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "elfi2.mm"
include "adantr.mm"
include "wne.mm"
include "ad2antrr.mm"
include "simplrr.mm"
include "intss1.mm"
include "adantl.mm"
include "simplr.mm"
include "sseldd.mm"
include "ad2antlr.mm"
include "eldifsn.mm"
include "simplbi.mm"
include "ad2antrl.mm"
include "elfpw.mm"
include "sselda.mm"
include "anasss.mm"
include "anim1i.mm"
include "elunii.mm"
include "syl2anc.mm"
include "ex.mm"
include "mt3d.mm"
include "expr.mm"
include "ssrdv.mm"
include "simprbi.mm"
include "elfir.mm"
include "syl13anc.mm"
include "filfi.mm"
include "eleqtrd.mm"
include "eleq2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "imp32.mm"
include "adantrrr.mm"
include "elssuni.mm"
include "ctopon.mm"
include "ctb.mm"
include "fibas.mm"
include "tgtopon.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "fiuni.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "toponuni.mm"
include "sseqtr4d.mm"
include "simprrr.mm"
include "filss.mm"
include "rexlimddv.mm"
include "ralrimiva.mm"
include "imdistanda.mm"
include "syl5bi.mm"
include "flimopn.mm"
include "sylibrd.mm"
include "sseq0.mm"
include "ssdif0.mm"
include "difss.mm"
include "unissi.mm"
include "syl5sseqr.mm"
include "eqssd.mm"
include "jctil.mm"
include "difexg.mm"
include "sseq1.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "vtoclg.mm"
include "mpcom.mm"
include "mpdan.mm"
include "uni0.mm"
include "syl6eq.mm"
include "neeq2d.mm"
include "ciin.mm"
include "cmpt.mm"
include "crn.mm"
include "difssd.mm"
include "ralrimivw.mm"
include "riinn0.mm"
include "sylan.mm"
include "cab.mm"
include "dfiin2g.mm"
include "eqid.mm"
include "rnmpt.mm"
include "inteqi.mm"
include "syl6eqr.mm"
include "wf.mm"
include "eldifbd.mm"
include "difss2d.mm"
include "ufilb.mm"
include "mpbid.mm"
include "fmptd.mm"
include "frn.mm"
include "cdm.mm"
include "dmmptd.mm"
include "simpr.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "abrexfi.mm"
include "syl5eqel.mm"
include "filintn0.mm"
include "disj3.mm"
include "ciun.mm"
include "iundif2.mm"
include "dfss4.mm"
include "iuneq2dv.mm"
include "uniiun.mm"
include "syl5eqr.mm"
include "neeqtrd.mm"
include "filtop.mm"
include "fileln0.mm"
include "pm2.61ne.mm"
include "neneqd.mm"
include "nrexdv.mm"
include "pm2.65i.mm"

theorem alexsublem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F
  let cJ: class J
  let cX: class X
  let vz: setvar z
  let vf: setvar f
  assume alexsub.1: |- ( ph -> X e. UFL )
  assume alexsub.2: |- ( ph -> X = U. B )
  assume alexsub.3: |- ( ph -> J = ( topGen ` ( fi ` B ) ) )
  assume alexsub.4: |- ( ( ph /\ ( x C_ B /\ X = U. x ) ) -> E. y e. ( ~P x i^i Fin ) X = U. y )
  assume alexsub.5: |- ( ph -> F e. ( UFil ` X ) )
  assume alexsub.6: |- ( ph -> ( J fLim F ) = (/) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint J z
  disjoint f ph
  disjoint ph z
  disjoint X f
  disjoint X z
  disjoint F z
  assert |- -. ph

  proof
    wph
    cX
    vy
    cv
    #
    cuni
    #
    wceq
    #
    vy
    cB
    cF
    cdif
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wph
    @3
    cB
    wss
    #
    cX
    @3
    cuni
    #
    wceq
    #
    wa
    #
    @6
    wph
    @9
    @7
    wph
    cX
    @8
    wph
    cX
    @8
    cdif
    #
    c0
    wceq
    #
    cX
    @8
    wss
    wph
    @11
    cJ
    cF
    cflim
    co
    #
    wss
    @13
    c0
    wceq
    @12
    wph
    vx
    @11
    @13
    wph
    vx
    cv
    #
    @11
    wcel
    #
    @14
    cX
    wcel
    #
    vx
    vy
    wel
    #
    @0
    cF
    wcel
    #
    wi
    #
    vy
    cJ
    wral
    #
    wa
    #
    @14
    @13
    wcel
    #
    @15
    @16
    @14
    @8
    wcel
    #
    wn
    #
    wa
    #
    wph
    @21
    @14
    cX
    @8
    eldif
    wph
    @16
    @24
    @20
    wph
    @16
    @24
    @20
    wph
    @25
    wa
    #
    @19
    vy
    cJ
    @26
    @0
    cJ
    wcel
    #
    @17
    @18
    @26
    @27
    @17
    wa
    #
    wa
    #
    vx
    vz
    wel
    #
    vz
    cv
    #
    @0
    wss
    #
    wa
    #
    @18
    vz
    cB
    cfi
    cfv
    #
    @29
    @0
    @34
    ctg
    cfv
    #
    wcel
    #
    @17
    wa
    #
    @33
    vz
    @34
    wrex
    wph
    @28
    @37
    @25
    wph
    @28
    @37
    wph
    @27
    @36
    @17
    wph
    cJ
    @35
    @0
    alexsub.3
    eleq2d
    anbi1d
    biimpa
    adantlr
    vz
    @0
    @34
    @14
    tg2
    syl
    @29
    @31
    @34
    wcel
    #
    @33
    wa
    #
    wa
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    @31
    cF
    wcel
    #
    @0
    cX
    wss
    #
    @32
    @18
    wph
    @41
    @25
    @28
    @39
    wph
    cF
    cX
    cufil
    cfv
    wcel
    #
    @41
    alexsub.5
    cF
    cX
    ufilfil
    syl
    #
    ad3antrrr
    @26
    @39
    @42
    @28
    @26
    @38
    @30
    @42
    @32
    @26
    @38
    @30
    @42
    @26
    @38
    @31
    @0
    cint
    #
    wceq
    #
    vy
    cB
    cpw
    cfn
    cin
    #
    c0
    csn
    cdif
    #
    wrex
    #
    @30
    @42
    wi
    #
    wph
    @38
    @50
    wb
    #
    @25
    wph
    cB
    cvv
    wcel
    #
    @52
    wph
    cB
    cuni
    #
    cvv
    wcel
    @53
    wph
    cX
    @54
    cvv
    alexsub.2
    wph
    cF
    cufil
    cX
    alexsub.5
    elfvexd
    #
    eqeltrrd
    cB
    uniexb
    sylibr
    #
    vy
    @31
    cB
    cvv
    elfi2
    syl
    adantr
    @26
    @47
    @51
    vy
    @49
    @26
    @0
    @49
    wcel
    #
    wa
    @51
    @47
    @14
    @46
    wcel
    #
    @46
    cF
    wcel
    #
    wi
    @26
    @57
    @58
    @59
    @26
    @57
    @58
    wa
    #
    wa
    #
    @46
    cF
    cfi
    cfv
    #
    cF
    @61
    @41
    @0
    cF
    wss
    @0
    c0
    wne
    #
    @0
    cfn
    wcel
    #
    @46
    @62
    wcel
    wph
    @41
    @25
    @60
    @45
    ad2antrr
    #
    @61
    vz
    @0
    cF
    @26
    @60
    vz
    vy
    wel
    #
    @42
    @26
    @60
    @66
    wa
    #
    wa
    #
    @42
    @23
    wph
    @16
    @24
    @67
    simplrr
    @68
    @42
    wn
    #
    @23
    @68
    @69
    wa
    #
    @30
    @31
    @3
    wcel
    #
    @23
    @67
    @30
    @26
    @69
    @67
    @46
    @31
    @14
    @66
    @46
    @31
    wss
    @60
    @31
    @0
    intss1
    adantl
    @57
    @58
    @66
    simplr
    sseldd
    ad2antlr
    @70
    @31
    cB
    wcel
    #
    @69
    wa
    @71
    @68
    @72
    @69
    @26
    @60
    @66
    @72
    @61
    @0
    cB
    @31
    @61
    @0
    @48
    wcel
    #
    @0
    cB
    wss
    #
    @57
    @73
    @26
    @58
    @57
    @73
    @63
    @0
    @48
    c0
    eldifsn
    #
    simplbi
    ad2antrl
    #
    @73
    @74
    @64
    @0
    cB
    elfpw
    #
    simplbi
    syl
    sselda
    anasss
    anim1i
    @31
    cB
    cF
    eldif
    sylibr
    @14
    @31
    @3
    elunii
    syl2anc
    ex
    mt3d
    expr
    ssrdv
    @57
    @63
    @26
    @58
    @57
    @73
    @63
    @75
    simprbi
    ad2antrl
    @61
    @73
    @64
    @76
    @73
    @74
    @64
    @77
    simprbi
    syl
    @0
    cF
    @40
    elfir
    syl13anc
    @61
    @41
    @62
    cF
    wceq
    @65
    cF
    cX
    filfi
    syl
    eleqtrd
    expr
    @47
    @30
    @58
    @42
    @59
    @31
    @46
    @14
    eleq2
    @31
    @46
    cF
    eleq1
    imbi12d
    syl5ibrcom
    rexlimdva
    sylbid
    imp32
    adantrrr
    adantlr
    @29
    @43
    @39
    @29
    @0
    cJ
    cuni
    #
    cX
    @27
    @0
    @78
    wss
    @26
    @17
    @0
    cJ
    elssuni
    ad2antrl
    wph
    cX
    @78
    wceq
    #
    @25
    @28
    wph
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    @79
    wph
    cJ
    @34
    cuni
    #
    ctopon
    cfv
    #
    @80
    wph
    cJ
    @35
    @83
    alexsub.3
    @34
    ctb
    wcel
    @35
    @83
    wcel
    cB
    fibas
    @34
    tgtopon
    ax-mp
    syl6eqel
    wph
    cX
    @82
    ctopon
    wph
    cX
    @54
    @82
    alexsub.2
    wph
    @53
    @54
    @82
    wceq
    @56
    cB
    cvv
    fiuni
    syl
    eqtrd
    fveq2d
    eleqtrrd
    #
    cX
    cJ
    toponuni
    syl
    ad2antrr
    sseqtr4d
    adantr
    @29
    @38
    @30
    @32
    simprrr
    @31
    @0
    cF
    cX
    filss
    syl13anc
    rexlimddv
    expr
    ralrimiva
    expr
    imdistanda
    syl5bi
    wph
    @81
    @41
    @22
    @21
    wb
    @84
    @45
    vy
    @14
    cF
    cJ
    cX
    flimopn
    syl2anc
    sylibrd
    ssrdv
    alexsub.6
    @11
    @13
    sseq0
    syl2anc
    cX
    @8
    ssdif0
    sylibr
    wph
    @54
    @8
    cX
    @3
    cB
    cB
    cF
    difss
    #
    unissi
    alexsub.2
    syl5sseqr
    eqssd
    @85
    jctil
    @3
    cvv
    wcel
    #
    wph
    @10
    wa
    #
    @6
    wph
    @86
    @10
    wph
    @53
    @86
    @56
    cB
    cF
    cvv
    difexg
    syl
    adantr
    wph
    @14
    cB
    wss
    #
    cX
    @14
    cuni
    #
    wceq
    #
    wa
    #
    wa
    #
    @2
    vy
    @14
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    @87
    @6
    wi
    vx
    @3
    cvv
    @14
    @3
    wceq
    #
    @92
    @87
    @95
    @6
    @96
    @91
    @10
    wph
    @96
    @88
    @7
    @90
    @9
    @14
    @3
    cB
    sseq1
    @96
    @89
    @8
    cX
    @14
    @3
    unieq
    eqeq2d
    anbi12d
    anbi2d
    @96
    @2
    vy
    @94
    @5
    @96
    @93
    @4
    cfn
    @14
    @3
    pweq
    ineq1d
    rexeqdv
    imbi12d
    alexsub.4
    vtoclg
    mpcom
    mpdan
    wph
    @2
    vy
    @5
    wph
    @0
    @5
    wcel
    #
    wa
    #
    cX
    @1
    @98
    cX
    @1
    wne
    cX
    c0
    wne
    #
    @0
    c0
    @0
    c0
    wceq
    #
    @1
    c0
    cX
    @100
    @1
    c0
    cuni
    c0
    @0
    c0
    unieq
    uni0
    syl6eq
    neeq2d
    @98
    @63
    wa
    #
    cX
    cX
    vz
    @0
    cX
    @31
    cdif
    #
    ciin
    #
    cdif
    #
    @1
    @101
    cX
    @103
    cin
    #
    c0
    wne
    cX
    @104
    wne
    @101
    @105
    vz
    @0
    @102
    cmpt
    #
    crn
    #
    cint
    #
    c0
    @101
    @105
    @103
    @108
    @98
    @102
    cX
    wss
    #
    vz
    @0
    wral
    @63
    @105
    @103
    wceq
    @98
    @109
    vz
    @0
    @98
    cX
    @31
    difssd
    ralrimivw
    vz
    cX
    @102
    @0
    riinn0
    sylan
    @101
    @103
    @14
    @102
    wceq
    vz
    @0
    wrex
    vx
    cab
    #
    cint
    #
    @108
    @101
    @102
    cvv
    wcel
    #
    vz
    @0
    wral
    @103
    @111
    wceq
    @101
    @112
    vz
    @0
    @101
    cX
    cvv
    wcel
    #
    @112
    wph
    @113
    @97
    @63
    @55
    ad2antrr
    cX
    @31
    cvv
    difexg
    syl
    ralrimivw
    vz
    vx
    @0
    @102
    cvv
    dfiin2g
    syl
    @107
    @110
    vz
    vx
    @0
    @102
    @106
    @106
    eqid
    #
    rnmpt
    #
    inteqi
    syl6eqr
    eqtrd
    @101
    @41
    @107
    cF
    wss
    #
    @107
    c0
    wne
    #
    @107
    cfn
    wcel
    #
    @108
    c0
    wne
    wph
    @41
    @97
    @63
    @45
    ad2antrr
    @101
    @0
    cF
    @106
    wf
    @116
    @101
    vz
    @0
    @102
    cF
    @106
    @101
    @66
    wa
    #
    @69
    @102
    cF
    wcel
    #
    @119
    @31
    cB
    cF
    @101
    @0
    @3
    @31
    @97
    @0
    @3
    wss
    #
    wph
    @63
    @97
    @121
    @64
    @0
    @3
    elfpw
    #
    simplbi
    ad2antlr
    #
    sselda
    eldifbd
    @119
    @44
    @31
    cX
    wss
    #
    @69
    @120
    wb
    wph
    @44
    @97
    @63
    @66
    alexsub.5
    ad3antrrr
    @119
    @31
    @54
    cX
    @119
    @72
    @31
    @54
    wss
    @101
    @0
    cB
    @31
    @101
    @0
    cB
    cF
    @123
    difss2d
    sselda
    @31
    cB
    elssuni
    syl
    wph
    cX
    @54
    wceq
    @97
    @63
    @66
    alexsub.2
    ad3antrrr
    sseqtr4d
    #
    @31
    cF
    cX
    ufilb
    syl2anc
    mpbid
    #
    @114
    fmptd
    @0
    cF
    @106
    frn
    syl
    @101
    @106
    cdm
    #
    c0
    wne
    @117
    @101
    @127
    @0
    c0
    @101
    vz
    @106
    @0
    @102
    cF
    @114
    @126
    dmmptd
    @98
    @63
    simpr
    eqnetrd
    @127
    c0
    @107
    c0
    @106
    dm0rn0
    necon3bii
    sylib
    @101
    @64
    @118
    @97
    @64
    wph
    @63
    @97
    @121
    @64
    @122
    simprbi
    ad2antlr
    @64
    @107
    @110
    cfn
    @115
    vz
    vx
    @0
    @102
    abrexfi
    syl5eqel
    syl
    @107
    cF
    cX
    filintn0
    syl13anc
    eqnetrd
    @105
    c0
    cX
    @104
    cX
    @103
    disj3
    necon3bii
    sylib
    @101
    @104
    vz
    @0
    cX
    @102
    cdif
    #
    ciun
    #
    @1
    vz
    @0
    cX
    @102
    iundif2
    @101
    @129
    vz
    @0
    @31
    ciun
    @1
    @101
    vz
    @0
    @128
    @31
    @119
    @124
    @128
    @31
    wceq
    @125
    @31
    cX
    dfss4
    sylib
    iuneq2dv
    vz
    @0
    uniiun
    syl6eqr
    syl5eqr
    neeqtrd
    @98
    @41
    @99
    wph
    @41
    @97
    @45
    adantr
    @41
    cX
    cF
    wcel
    @99
    cF
    cX
    filtop
    cX
    cF
    cX
    fileln0
    mpdan
    syl
    pm2.61ne
    neneqd
    nrexdv
    pm2.65i
end
