include "ccnext.mm"
include "co.mm"
include "cfv.mm"
include "ccn.mm"
include "wcel.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "csn.mm"
include "cnei.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "simpll.mm"
include "cin.mm"
include "ccl.mm"
include "w3a.mm"
include "simpr3.mm"
include "ctop.mm"
include "ad2antrr.mm"
include "simpr2.mm"
include "neii2.mm"
include "syl2anc.mm"
include "wi.mm"
include "vex.mm"
include "snss.mm"
include "biimpri.mm"
include "anim1i.mm"
include "anim2i.mm"
include "ex.mm"
include "3anass.mm"
include "anbi1i.mm"
include "anass.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "opnneip.mm"
include "syl3an1.mm"
include "adantr.mm"
include "imdistanri.mm"
include "jca.mm"
include "sylbir.mm"
include "syl6.mm"
include "cha.mm"
include "haustop.mm"
include "syl.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "frn.mm"
include "syl5ss.mm"
include "ssrin.mm"
include "imass2.mm"
include "adantl.mm"
include "clsss.mm"
include "syl3anc.mm"
include "sstr.mm"
include "sylan.mm"
include "an32s.mm"
include "anim2d.mm"
include "syld.mm"
include "reximdv2.mm"
include "imp.mm"
include "syl21anc.mm"
include "3anassrs.mm"
include "crest.mm"
include "simpr.mm"
include "simp-4l.mm"
include "simplr.mm"
include "wceq.mm"
include "cvv.mm"
include "wb.mm"
include "fvexd.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "elfvexd.mm"
include "ssexd.mm"
include "elrest.mm"
include "biimpa.mm"
include "imaeq2.mm"
include "fveq2d.mm"
include "sseq1d.mm"
include "biimpcd.mm"
include "reximdv.mm"
include "syl5.mm"
include "syl12anc.mm"
include "simplll.mm"
include "cflf.mm"
include "cuni.mm"
include "c0.mm"
include "wne.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "sneq.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "cnextfvval.mm"
include "fvex.mm"
include "uniex.mm"
include "snid.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cfil.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "trnei.mm"
include "mpbid.mm"
include "hausflf2.mm"
include "syl31anc.mm"
include "en1b.mm"
include "syl5eleqr.mm"
include "eqeltrd.mm"
include "flfnei.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "ad3antrrr.mm"
include "neii1.mm"
include "3an1rs.mm"
include "adantllr.mm"
include "mpd.mm"
include "creg.mm"
include "simprl.mm"
include "regsep.mm"
include "expcom.mm"
include "ad2antll.mm"
include "reximi.mm"
include "r19.29a.mm"
include "3expib.mm"
include "anim1d.mm"
include "syl5bir.mm"
include "sylc.mm"
include "eltopss.mm"
include "sseldd.mm"
include "3expa.mm"
include "elrestr.mm"
include "cfm.mm"
include "cflim.mm"
include "flfval.mm"
include "cfbas.mm"
include "cfg.mm"
include "uniexg.mm"
include "syl5eqel.mm"
include "filfbas.mm"
include "fgfil.mm"
include "eleqtrrd.mm"
include "eqid.mm"
include "imaelfm.mm"
include "flimclsi.mm"
include "eqsstrd.mm"
include "eqsstr3d.mm"
include "sylibr.mm"
include "adantlr.mm"
include "ralrimiva.mm"
include "expl.mm"
include "wfun.mm"
include "cdm.mm"
include "cnextf.mm"
include "ffun.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "biimprd.mm"
include "reximdva.mm"
include "cnnei.mm"
include "mpbird.mm"

theorem cnextcn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let vy: setvar y
  let cX: class X
  let vb: setvar b
  let vd: setvar d
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let vw: setvar w
  let vc: setvar c
  assume cnextf.1: |- C = U. J
  assume cnextf.2: |- B = U. K
  assume cnextf.3: |- ( ph -> J e. Top )
  assume cnextf.4: |- ( ph -> K e. Haus )
  assume cnextf.5: |- ( ph -> F : A --> B )
  assume cnextf.a: |- ( ph -> A C_ C )
  assume cnextf.6: |- ( ph -> ( ( cls ` J ) ` A ) = C )
  assume cnextf.7: |- ( ( ph /\ x e. C ) -> ( ( K fLimf ( ( ( nei ` J ) ` { x } ) |`t A ) ) ` F ) =/= (/) )
  assume cnextcn.8: |- ( ph -> K e. Reg )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  disjoint J x
  disjoint K x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint J y
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint ph y
  disjoint b d
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint b w
  disjoint B b
  disjoint u w
  disjoint B u
  disjoint v w
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint b c
  disjoint C b
  disjoint c d
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint C c
  disjoint d w
  disjoint C d
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint F b
  disjoint c z
  disjoint F c
  disjoint F d
  disjoint F u
  disjoint F v
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint J b
  disjoint J c
  disjoint J d
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint K b
  disjoint K c
  disjoint K d
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K z
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> ( ( J CnExt K ) ` F ) e. ( J Cn K ) )

  proof
    wph
    cF
    cJ
    cK
    ccnext
    co
    cfv
    #
    cJ
    cK
    ccn
    co
    wcel
    #
    @0
    vv
    cv
    #
    cima
    vw
    cv
    #
    wss
    #
    vv
    vx
    cv
    #
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    wrex
    #
    vw
    @5
    @0
    cfv
    #
    csn
    #
    cK
    cnei
    cfv
    cfv
    #
    wral
    #
    vx
    cC
    wral
    #
    wph
    @13
    vx
    cC
    wph
    @5
    cC
    wcel
    #
    wa
    #
    @9
    vw
    @12
    @16
    @3
    @12
    wcel
    #
    wa
    #
    wph
    vz
    cv
    #
    @0
    cfv
    #
    @3
    wcel
    #
    vz
    @2
    wral
    #
    vv
    @8
    wrex
    #
    @9
    wph
    @15
    @17
    simpll
    @18
    @2
    cJ
    wcel
    #
    cF
    @2
    cA
    cin
    #
    cima
    #
    cK
    ccl
    cfv
    #
    cfv
    #
    @3
    wss
    #
    wa
    #
    vv
    @8
    wrex
    #
    @23
    @18
    cF
    vd
    cv
    #
    cA
    cin
    #
    cima
    #
    @27
    cfv
    #
    @3
    wss
    #
    @31
    vd
    @8
    @16
    @17
    @32
    @8
    wcel
    #
    @36
    @31
    @16
    @17
    @37
    @36
    w3a
    #
    wa
    #
    wph
    @36
    @6
    @2
    wss
    #
    @2
    @32
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    @31
    wph
    @15
    @38
    simpll
    @16
    @17
    @37
    @36
    simpr3
    @39
    cJ
    ctop
    wcel
    #
    @37
    @43
    wph
    @44
    @15
    @38
    cnextf.3
    ad2antrr
    @16
    @17
    @37
    @36
    simpr2
    @6
    vv
    cJ
    @32
    neii2
    syl2anc
    wph
    @36
    wa
    #
    @43
    @31
    @45
    @42
    @30
    vv
    cJ
    @8
    @45
    @24
    @42
    wa
    #
    @2
    @8
    wcel
    #
    @24
    @41
    wa
    #
    wa
    #
    @47
    @30
    wa
    wph
    @46
    @49
    wi
    @36
    wph
    @46
    wph
    @24
    @5
    @2
    wcel
    #
    @41
    wa
    #
    wa
    #
    wa
    #
    @49
    wph
    @46
    @53
    @46
    @52
    wph
    @42
    @51
    @24
    @40
    @50
    @41
    @50
    @40
    @5
    @2
    vx
    vex
    snss
    biimpri
    anim1i
    anim2i
    anim2i
    ex
    @53
    wph
    @24
    @50
    w3a
    #
    @41
    wa
    #
    @49
    @55
    wph
    @24
    @50
    wa
    #
    wa
    #
    @41
    wa
    wph
    @56
    @41
    wa
    #
    wa
    @53
    @54
    @57
    @41
    wph
    @24
    @50
    3anass
    anbi1i
    wph
    @56
    @41
    anass
    @58
    @52
    wph
    @24
    @50
    @41
    anass
    anbi2i
    3bitri
    @55
    @47
    @48
    @54
    @47
    @41
    wph
    @44
    @24
    @50
    @47
    cnextf.3
    @5
    cJ
    @2
    opnneip
    syl3an1
    adantr
    @41
    @54
    @24
    @41
    @54
    @24
    @41
    wph
    @24
    @50
    simpr2
    ex
    imdistanri
    jca
    sylbir
    syl6
    adantr
    @45
    @48
    @30
    @47
    @45
    @41
    @29
    @24
    @45
    @41
    @29
    wph
    @41
    @36
    @29
    wph
    @41
    wa
    #
    @28
    @35
    wss
    #
    @36
    @29
    @59
    cK
    ctop
    wcel
    #
    @34
    cB
    wss
    #
    @26
    @34
    wss
    #
    @60
    wph
    @61
    @41
    wph
    cK
    cha
    wcel
    #
    @61
    cnextf.4
    cK
    haustop
    syl
    #
    adantr
    wph
    @62
    @41
    wph
    @34
    cF
    crn
    #
    cB
    cF
    @33
    imassrn
    wph
    cA
    cB
    cF
    wf
    #
    @66
    cB
    wss
    cnextf.5
    cA
    cB
    cF
    frn
    syl
    syl5ss
    adantr
    @41
    @63
    wph
    @41
    @25
    @33
    wss
    @63
    @2
    @32
    cA
    ssrin
    @25
    @33
    cF
    imass2
    syl
    adantl
    @34
    @26
    cK
    cB
    cnextf.2
    clsss
    syl3anc
    @28
    @35
    @3
    sstr
    sylan
    an32s
    ex
    anim2d
    anim2d
    syld
    reximdv2
    imp
    syl21anc
    3anassrs
    @18
    cF
    vu
    cv
    #
    cima
    #
    @27
    cfv
    #
    @3
    wss
    #
    @36
    vd
    @8
    wrex
    #
    vu
    @8
    cA
    crest
    co
    #
    @18
    @68
    @73
    wcel
    #
    wa
    #
    @71
    wa
    @71
    wph
    @74
    @72
    @75
    @71
    simpr
    wph
    @15
    @17
    @74
    @71
    simp-4l
    @18
    @74
    @71
    simplr
    @71
    wph
    @74
    wa
    #
    @72
    @76
    @68
    @33
    wceq
    #
    vd
    @8
    wrex
    #
    @71
    @72
    wph
    @74
    @78
    wph
    @8
    cvv
    wcel
    cA
    cvv
    wcel
    #
    @74
    @78
    wb
    wph
    @6
    @7
    fvexd
    wph
    cA
    cC
    cvv
    wph
    cJ
    ctopon
    cC
    wph
    @44
    cJ
    cC
    ctopon
    cfv
    wcel
    #
    cnextf.3
    cJ
    cC
    cnextf.1
    toptopon
    sylib
    #
    elfvexd
    cnextf.a
    ssexd
    #
    vd
    @68
    cA
    @8
    cvv
    cvv
    elrest
    syl2anc
    biimpa
    @71
    @77
    @36
    vd
    @8
    @77
    @71
    @36
    @77
    @70
    @35
    @3
    @77
    @69
    @34
    @27
    @68
    @33
    cF
    imaeq2
    fveq2d
    sseq1d
    biimpcd
    reximdv
    syl5
    imp
    syl12anc
    @18
    vb
    cv
    #
    @27
    cfv
    #
    @3
    wss
    #
    @71
    vu
    @73
    wrex
    #
    vb
    @12
    @18
    @83
    @12
    wcel
    #
    wa
    @85
    wa
    #
    @69
    @83
    wss
    #
    vu
    @73
    wrex
    #
    @86
    @88
    @16
    @87
    @90
    @16
    @17
    @87
    @85
    simplll
    @18
    @87
    @85
    simplr
    @16
    @90
    vb
    @12
    @16
    @10
    cB
    wcel
    #
    @90
    vb
    @12
    wral
    #
    @16
    @10
    cF
    cK
    @73
    cflf
    co
    #
    cfv
    #
    wcel
    #
    @91
    @92
    wa
    #
    @16
    @10
    @94
    cuni
    #
    @94
    wph
    vy
    cA
    cB
    cC
    cF
    cJ
    cK
    @5
    cnextf.1
    cnextf.2
    cnextf.3
    cnextf.4
    cnextf.5
    cnextf.a
    cnextf.6
    @16
    @94
    c0
    wne
    #
    wi
    #
    wph
    vy
    cv
    #
    cC
    wcel
    #
    wa
    #
    cF
    cK
    @100
    csn
    #
    @7
    cfv
    #
    cA
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    c0
    wne
    #
    wi
    vx
    vy
    vx
    vy
    weq
    #
    @16
    @102
    @98
    @108
    @109
    @15
    @101
    wph
    @5
    @100
    cC
    eleq1
    anbi2d
    @109
    @94
    @107
    c0
    @109
    cF
    @93
    @106
    @109
    @73
    @105
    cK
    cflf
    @109
    @8
    @104
    cA
    crest
    @109
    @6
    @103
    @7
    @5
    @100
    sneq
    fveq2d
    oveq1d
    oveq2d
    fveq1d
    neeq1d
    imbi12d
    cnextf.7
    chvarv
    cnextfvval
    @16
    @97
    @97
    csn
    #
    @94
    @97
    @94
    cF
    @93
    fvex
    uniex
    snid
    @16
    @94
    c1o
    cen
    wbr
    #
    @94
    @110
    wceq
    @16
    @64
    @73
    cA
    cfil
    cfv
    #
    wcel
    #
    @67
    @98
    @111
    wph
    @64
    @15
    cnextf.4
    adantr
    @16
    @5
    cA
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    @113
    wph
    @115
    @15
    wph
    @114
    cC
    @5
    cnextf.6
    eleq2d
    biimpar
    @16
    @80
    cA
    cC
    wss
    #
    @15
    @115
    @113
    wb
    wph
    @80
    @15
    @81
    adantr
    wph
    @116
    @15
    cnextf.a
    adantr
    wph
    @15
    simpr
    cA
    @5
    cJ
    cC
    trnei
    syl3anc
    mpbid
    #
    wph
    @67
    @15
    cnextf.5
    adantr
    #
    cnextf.7
    cF
    cK
    @73
    cB
    cA
    cnextf.2
    hausflf2
    syl31anc
    @94
    en1b
    sylib
    syl5eleqr
    eqeltrd
    @16
    cK
    cB
    ctopon
    cfv
    wcel
    #
    @113
    @67
    @95
    @96
    wb
    wph
    @119
    @15
    wph
    @61
    @119
    @65
    cK
    cB
    cnextf.2
    toptopon
    sylib
    #
    adantr
    @117
    @118
    @10
    vb
    cF
    cK
    @73
    cB
    cA
    vu
    flfnei
    syl3anc
    mpbid
    simprd
    r19.21bi
    syl2anc
    @16
    @87
    @85
    @90
    @86
    wi
    #
    @17
    @16
    @87
    wa
    #
    @85
    wa
    #
    @61
    @83
    cB
    wss
    #
    @85
    @121
    wph
    @61
    @15
    @87
    @85
    @65
    ad3antrrr
    #
    @123
    @61
    @87
    @124
    @125
    @16
    @87
    @85
    simplr
    @11
    cK
    @83
    cB
    cnextf.2
    neii1
    syl2anc
    @122
    @85
    simpr
    @61
    @124
    @85
    w3a
    #
    @89
    @71
    vu
    @73
    @126
    @89
    @71
    @61
    @124
    @89
    @85
    @71
    @61
    @124
    @89
    w3a
    @70
    @84
    wss
    @85
    @71
    @83
    @69
    cK
    cB
    cnextf.2
    clsss
    @70
    @84
    @3
    sstr
    sylan
    3an1rs
    ex
    reximdv
    syl3anc
    adantllr
    mpd
    @18
    @61
    @10
    @83
    wcel
    #
    @85
    wa
    #
    vb
    cK
    wrex
    #
    @85
    vb
    @12
    wrex
    wph
    @61
    @15
    @17
    @65
    ad2antrr
    #
    @18
    @10
    vc
    cv
    #
    wcel
    #
    @131
    @3
    wss
    #
    wa
    #
    @129
    vc
    cK
    @18
    @131
    cK
    wcel
    #
    wa
    #
    @134
    wa
    #
    @127
    @84
    @131
    wss
    #
    wa
    #
    vb
    cK
    wrex
    #
    @129
    @137
    cK
    creg
    wcel
    #
    @135
    @132
    @140
    @18
    @141
    @135
    @134
    wph
    @141
    @15
    @17
    cnextcn.8
    ad2antrr
    ad2antrr
    @18
    @135
    @134
    simplr
    @136
    @132
    @133
    simprl
    vb
    @10
    @131
    cK
    regsep
    syl3anc
    @133
    @140
    @129
    wi
    @136
    @132
    @133
    @139
    @128
    vb
    cK
    @133
    @138
    @85
    @127
    @138
    @133
    @85
    @84
    @131
    @3
    sstr
    expcom
    anim2d
    reximdv
    ad2antll
    mpd
    @18
    @61
    @17
    @134
    vc
    cK
    wrex
    #
    @130
    @16
    @17
    simpr
    @61
    @17
    wa
    @11
    @131
    wss
    #
    @133
    wa
    #
    vc
    cK
    wrex
    @142
    @11
    vc
    cK
    @3
    neii2
    @144
    @134
    vc
    cK
    @134
    @144
    @132
    @143
    @133
    @10
    @131
    @5
    @0
    fvex
    snss
    anbi1i
    biimpri
    reximi
    syl
    syl2anc
    r19.29a
    @61
    @128
    @85
    vb
    cK
    @12
    @83
    cK
    wcel
    #
    @128
    wa
    @145
    @127
    wa
    #
    @85
    wa
    @61
    @87
    @85
    wa
    @145
    @127
    @85
    anass
    @61
    @146
    @87
    @85
    @61
    @145
    @127
    @87
    @10
    cK
    @83
    opnneip
    3expib
    anim1d
    syl5bir
    reximdv2
    sylc
    r19.29a
    r19.29a
    r19.29a
    wph
    @31
    @23
    wi
    @15
    @17
    wph
    @30
    @22
    vv
    @8
    wph
    @24
    @29
    @22
    wph
    @24
    wa
    #
    @29
    wa
    #
    @21
    vz
    @2
    @148
    @19
    @2
    wcel
    #
    wa
    @28
    @3
    @20
    @147
    @29
    @149
    simplr
    @147
    @149
    @20
    @28
    wcel
    #
    @29
    @147
    @149
    wa
    #
    wph
    @19
    cC
    wcel
    #
    @25
    @19
    csn
    #
    @7
    cfv
    #
    cA
    crest
    co
    #
    wcel
    #
    @150
    wph
    @24
    @149
    simpll
    @151
    @2
    cC
    @19
    @151
    @44
    @24
    @2
    cC
    wss
    #
    wph
    @44
    @24
    @149
    cnextf.3
    ad2antrr
    wph
    @24
    @149
    simplr
    @2
    cJ
    cC
    cnextf.1
    eltopss
    syl2anc
    @147
    @149
    simpr
    sseldd
    @151
    @154
    cvv
    wcel
    @79
    @2
    @154
    wcel
    #
    @156
    @151
    @153
    @7
    fvexd
    wph
    @79
    @24
    @149
    @82
    ad2antrr
    wph
    @24
    @149
    @158
    wph
    @44
    @24
    @149
    @158
    cnextf.3
    @19
    cJ
    @2
    opnneip
    syl3an1
    3expa
    @2
    cA
    @154
    cvv
    cvv
    elrestr
    syl3anc
    wph
    @152
    wa
    #
    @156
    wa
    #
    @20
    cF
    cK
    @155
    cflf
    co
    #
    cfv
    #
    cuni
    #
    @28
    @159
    @20
    @163
    wceq
    @156
    wph
    vx
    cA
    cB
    cC
    cF
    cJ
    cK
    @19
    cnextf.1
    cnextf.2
    cnextf.3
    cnextf.4
    cnextf.5
    cnextf.a
    cnextf.6
    cnextf.7
    cnextfvval
    adantr
    @160
    @163
    csn
    #
    @28
    wss
    @163
    @28
    wcel
    @160
    @164
    @162
    @28
    @159
    @162
    @164
    wceq
    #
    @156
    @159
    @162
    c1o
    cen
    wbr
    #
    @165
    @159
    @64
    @155
    @112
    wcel
    #
    @67
    @162
    c0
    wne
    #
    @166
    wph
    @64
    @152
    cnextf.4
    adantr
    @159
    @19
    @114
    wcel
    #
    @167
    wph
    @169
    @152
    wph
    @114
    cC
    @19
    cnextf.6
    eleq2d
    biimpar
    @159
    @80
    @116
    @152
    @169
    @167
    wb
    wph
    @80
    @152
    @81
    adantr
    wph
    @116
    @152
    cnextf.a
    adantr
    wph
    @152
    simpr
    cA
    @19
    cJ
    cC
    trnei
    syl3anc
    mpbid
    #
    wph
    @67
    @152
    cnextf.5
    adantr
    #
    @99
    @159
    @168
    wi
    vx
    vz
    vx
    vz
    weq
    #
    @16
    @159
    @98
    @168
    @172
    @15
    @152
    wph
    @5
    @19
    cC
    eleq1
    anbi2d
    @172
    @94
    @162
    c0
    @172
    cF
    @93
    @161
    @172
    @73
    @155
    cK
    cflf
    @172
    @8
    @154
    cA
    crest
    @172
    @6
    @153
    @7
    @5
    @19
    sneq
    fveq2d
    oveq1d
    oveq2d
    fveq1d
    neeq1d
    imbi12d
    cnextf.7
    chvarv
    cF
    cK
    @155
    cB
    cA
    cnextf.2
    hausflf2
    syl31anc
    @162
    en1b
    sylib
    adantr
    @160
    @162
    cK
    @155
    cB
    cF
    cfm
    co
    cfv
    #
    cflim
    co
    #
    @28
    @159
    @162
    @174
    wceq
    #
    @156
    @159
    @119
    @167
    @67
    @175
    wph
    @119
    @152
    @120
    adantr
    @170
    @171
    cF
    cK
    @155
    cB
    cA
    flfval
    syl3anc
    adantr
    @160
    @26
    @173
    wcel
    #
    @174
    @28
    wss
    @160
    cB
    cvv
    wcel
    @155
    cA
    cfbas
    cfv
    wcel
    #
    @67
    @25
    cA
    @155
    cfg
    co
    #
    wcel
    @176
    @160
    cB
    cK
    cuni
    #
    cvv
    cnextf.2
    wph
    @179
    cvv
    wcel
    #
    @152
    @156
    wph
    @64
    @180
    cnextf.4
    cK
    cha
    uniexg
    syl
    ad2antrr
    syl5eqel
    @160
    @167
    @177
    @159
    @167
    @156
    @170
    adantr
    @155
    cA
    filfbas
    syl
    wph
    @67
    @152
    @156
    cnextf.5
    ad2antrr
    @160
    @25
    @155
    @178
    @159
    @156
    simpr
    @159
    @178
    @155
    wceq
    #
    @156
    @159
    @167
    @181
    @170
    @155
    cA
    fgfil
    syl
    adantr
    eleqtrrd
    cvv
    @155
    @25
    cF
    @178
    cB
    cA
    @178
    eqid
    imaelfm
    syl31anc
    @26
    @173
    cK
    flimclsi
    syl
    eqsstrd
    eqsstr3d
    @163
    @28
    @162
    cF
    @161
    fvex
    uniex
    snss
    sylibr
    eqeltrd
    syl21anc
    adantlr
    sseldd
    ralrimiva
    expl
    reximdv
    ad2antrr
    mpd
    wph
    @22
    @4
    vv
    @8
    wph
    @47
    wa
    #
    @4
    @22
    @182
    @0
    wfun
    #
    @2
    @0
    cdm
    #
    wss
    @4
    @22
    wb
    wph
    @183
    @47
    wph
    cC
    cB
    @0
    wf
    #
    @183
    wph
    vx
    cA
    cB
    cC
    cF
    cJ
    cK
    cnextf.1
    cnextf.2
    cnextf.3
    cnextf.4
    cnextf.5
    cnextf.a
    cnextf.6
    cnextf.7
    cnextf
    #
    cC
    cB
    @0
    ffun
    syl
    adantr
    @182
    @2
    cC
    @184
    wph
    @44
    @47
    @157
    cnextf.3
    @6
    cJ
    @2
    cC
    cnextf.1
    neii1
    sylan
    wph
    @184
    cC
    wceq
    #
    @47
    wph
    @185
    @187
    @186
    cC
    cB
    @0
    fdm
    syl
    adantr
    sseqtr4d
    vz
    @2
    @3
    @0
    funimass4
    syl2anc
    biimprd
    reximdva
    sylc
    ralrimiva
    ralrimiva
    wph
    @44
    @61
    @185
    @1
    @14
    wb
    cnextf.3
    @65
    @186
    vw
    vv
    @0
    cJ
    cK
    cC
    cB
    vx
    cnextf.1
    cnextf.2
    cnnei
    syl3anc
    mpbird
end
