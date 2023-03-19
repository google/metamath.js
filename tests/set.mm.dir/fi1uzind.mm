include "wsbc.mm"
include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "df-clel.mm"
include "wal.mm"
include "cz.mm"
include "nn0z.mm"
include "mp1i.mm"
include "ad2antlr.mm"
include "wb.mm"
include "breq2.mm"
include "eqcoms.mm"
include "biimpcd.mm"
include "adantr.mm"
include "imp.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "2albidv.mm"
include "eqcom.mm"
include "sylan2b.mm"
include "gen2.mm"
include "a1i.mm"
include "w3a.mm"
include "simpl.mm"
include "simpr.mm"
include "sbceq1d.mm"
include "sbceqbid.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "cbval2v.mm"
include "cc0.mm"
include "nn0ge0.mm"
include "cr.mm"
include "0red.mm"
include "nn0re.mm"
include "zre.mm"
include "letr.mm"
include "syl3anc.mm"
include "cuz.mm"
include "0nn0.mm"
include "pm3.22.mm"
include "0z.mm"
include "eluz1.mm"
include "mpbird.mm"
include "eluznn0.mm"
include "sylancr.mm"
include "ex.mm"
include "syl6com.mm"
include "com14.mm"
include "pm2.43a.mm"
include "com12.mm"
include "mp2b.mm"
include "3adant1.mm"
include "clt.mm"
include "nn0p1gt0.mm"
include "breqtrrd.mm"
include "adantrl.mm"
include "cvv.mm"
include "vex.mm"
include "hashgt0elex.mm"
include "csn.mm"
include "cdif.mm"
include "brfi1indlem.mm"
include "syl5bi.mm"
include "peano2nn0.mm"
include "ad2antrr.mm"
include "simplrr.mm"
include "simprlr.mm"
include "3jca.mm"
include "jca.mm"
include "difexg.mm"
include "ax-mp.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "spc2gv.mm"
include "mp2an.mm"
include "expdimp.mm"
include "3anbi2i.mm"
include "anbi2i.mm"
include "sylanb.mm"
include "syl6an.mm"
include "exp41.mm"
include "com15.mm"
include "com23.mm"
include "mpcom.mm"
include "mpd.mm"
include "com4l.mm"
include "exlimiv.mm"
include "syl.mm"
include "com25.mm"
include "impcom.mm"
include "sylan.mm"
include "impancom.mm"
include "alrimivv.mm"
include "uzind.mm"
include "sbcex.mm"
include "sbccom.mm"
include "sylbi.mm"
include "expd.mm"
include "syl5com.mm"
include "exp31.mm"
include "expcom.mm"
include "com24.mm"
include "pm2.43i.mm"
include "hashcl.mm"
include "syl11.mm"
include "3imp.mm"

theorem fi1uzind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wrh: wff rh
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cL: class L
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume fi1uzind.f: |- F e. _V
  assume fi1uzind.l: |- L e. NN0
  assume fi1uzind.1: |- ( ( v = V /\ e = E ) -> ( ps <-> ph ) )
  assume fi1uzind.2: |- ( ( v = w /\ e = f ) -> ( ps <-> th ) )
  assume fi1uzind.3: |- ( ( [. v / a ]. [. e / b ]. rh /\ n e. v ) -> [. ( v \ { n } ) / a ]. [. F / b ]. rh )
  assume fi1uzind.4: |- ( ( w = ( v \ { n } ) /\ f = F ) -> ( th <-> ch ) )
  assume fi1uzind.base: |- ( ( [. v / a ]. [. e / b ]. rh /\ ( # ` v ) = L ) -> ps )
  assume fi1uzind.step: |- ( ( ( ( y + 1 ) e. NN0 /\ ( [. v / a ]. [. e / b ]. rh /\ ( # ` v ) = ( y + 1 ) /\ n e. v ) ) /\ ch ) -> ps )

  disjoint a b
  disjoint a e
  disjoint a n
  disjoint a v
  disjoint a y
  disjoint b e
  disjoint b n
  disjoint b v
  disjoint b y
  disjoint e n
  disjoint e v
  disjoint e y
  disjoint n v
  disjoint n y
  disjoint v y
  disjoint b f
  disjoint b w
  disjoint f w
  disjoint E a
  disjoint E e
  disjoint E n
  disjoint E v
  disjoint F a
  disjoint F f
  disjoint F w
  disjoint a f
  disjoint a w
  disjoint L e
  disjoint L n
  disjoint L v
  disjoint L y
  disjoint V a
  disjoint V b
  disjoint V e
  disjoint V n
  disjoint V v
  disjoint f ps
  disjoint n ps
  disjoint ps w
  disjoint ps y
  disjoint f n
  disjoint f y
  disjoint n w
  disjoint w y
  disjoint e th
  disjoint n th
  disjoint th v
  disjoint ch f
  disjoint ch w
  disjoint e ph
  disjoint n ph
  disjoint ph v
  disjoint e rh
  disjoint f rh
  disjoint n rh
  disjoint rh v
  disjoint rh w
  disjoint rh y
  disjoint e f
  disjoint e w
  disjoint f v
  disjoint v w
  disjoint a x
  disjoint b x
  disjoint e x
  disjoint n x
  disjoint v x
  disjoint x y
  disjoint L x
  disjoint ps x
  disjoint rh x
  assert |- ( ( [. V / a ]. [. E / b ]. rh /\ V e. Fin /\ L <_ ( # ` V ) ) -> ph )

  proof
    wrh
    vb
    cE
    wsbc
    #
    va
    cV
    wsbc
    #
    cV
    cfn
    wcel
    #
    cL
    cV
    chash
    cfv
    #
    cle
    wbr
    #
    wph
    @3
    cn0
    wcel
    #
    @1
    @4
    wph
    wi
    #
    @2
    @5
    vn
    cv
    #
    @3
    wceq
    #
    @7
    cn0
    wcel
    #
    wa
    #
    vn
    wex
    @1
    @6
    wi
    #
    vn
    @3
    cn0
    df-clel
    @10
    @11
    vn
    @8
    @9
    @11
    @8
    @9
    @11
    wi
    @8
    @1
    @9
    @8
    @6
    @1
    @8
    @9
    @8
    @6
    wi
    wi
    @4
    @9
    @8
    @1
    @8
    wa
    #
    wph
    @4
    @9
    @8
    @12
    wph
    wi
    #
    @4
    @9
    wa
    #
    @8
    wa
    #
    wrh
    vb
    ve
    cv
    #
    wsbc
    #
    va
    vv
    cv
    #
    wsbc
    #
    @7
    @18
    chash
    cfv
    #
    wceq
    #
    wa
    #
    wps
    wi
    #
    ve
    wal
    vv
    wal
    #
    @12
    wph
    @15
    cL
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    cL
    @7
    cle
    wbr
    #
    @24
    cL
    cn0
    wcel
    #
    @25
    @15
    fi1uzind.l
    cL
    nn0z
    mp1i
    @9
    @26
    @4
    @8
    @7
    nn0z
    ad2antlr
    @14
    @8
    @27
    @4
    @8
    @27
    wi
    @9
    @8
    @4
    @27
    @4
    @27
    wb
    @3
    @7
    @3
    @7
    cL
    cle
    breq2
    eqcoms
    biimpcd
    adantr
    imp
    @19
    vx
    cv
    #
    @20
    wceq
    #
    wa
    #
    wps
    wi
    #
    ve
    wal
    vv
    wal
    @19
    cL
    @20
    wceq
    #
    wa
    #
    wps
    wi
    #
    ve
    wal
    vv
    wal
    #
    @19
    vy
    cv
    #
    @20
    wceq
    #
    wa
    #
    wps
    wi
    #
    ve
    wal
    vv
    wal
    #
    @19
    @37
    c1
    caddc
    co
    #
    @20
    wceq
    #
    wa
    #
    wps
    wi
    #
    ve
    wal
    vv
    wal
    #
    @24
    vx
    vy
    cL
    @7
    @29
    cL
    wceq
    #
    @32
    @35
    vv
    ve
    @47
    @31
    @34
    wps
    @47
    @30
    @33
    @19
    @29
    cL
    @20
    eqeq1
    anbi2d
    imbi1d
    2albidv
    @29
    @37
    wceq
    #
    @32
    @40
    vv
    ve
    @48
    @31
    @39
    wps
    @48
    @30
    @38
    @19
    @29
    @37
    @20
    eqeq1
    anbi2d
    imbi1d
    2albidv
    @29
    @42
    wceq
    #
    @32
    @45
    vv
    ve
    @49
    @31
    @44
    wps
    @49
    @30
    @43
    @19
    @29
    @42
    @20
    eqeq1
    anbi2d
    imbi1d
    2albidv
    @29
    @7
    wceq
    #
    @32
    @23
    vv
    ve
    @50
    @31
    @22
    wps
    @50
    @30
    @21
    @19
    @29
    @7
    @20
    eqeq1
    anbi2d
    imbi1d
    2albidv
    @36
    @25
    @35
    vv
    ve
    @33
    @19
    @20
    cL
    wceq
    wps
    cL
    @20
    eqcom
    fi1uzind.base
    sylan2b
    gen2
    a1i
    @41
    wrh
    vb
    vf
    cv
    #
    wsbc
    #
    va
    vw
    cv
    #
    wsbc
    #
    @37
    @53
    chash
    cfv
    #
    wceq
    #
    wa
    #
    wth
    wi
    #
    vf
    wal
    vw
    wal
    #
    @25
    @37
    cz
    wcel
    #
    cL
    @37
    cle
    wbr
    #
    w3a
    #
    @46
    @40
    @58
    vv
    ve
    vw
    vf
    @18
    @53
    wceq
    #
    @16
    @51
    wceq
    #
    wa
    #
    @39
    @57
    wps
    wth
    @65
    @19
    @54
    @38
    @56
    @65
    @17
    @52
    va
    @18
    @53
    @63
    @64
    simpl
    @65
    wrh
    vb
    @16
    @51
    @63
    @64
    simpr
    sbceq1d
    sbceqbid
    @63
    @38
    @56
    wb
    @64
    @63
    @20
    @55
    @37
    @18
    @53
    chash
    fveq2
    eqeq2d
    adantr
    anbi12d
    fi1uzind.2
    imbi12d
    cbval2v
    @62
    @59
    @46
    @62
    @59
    wa
    @45
    vv
    ve
    @62
    @44
    @59
    wps
    @62
    @37
    cn0
    wcel
    #
    @44
    @59
    wps
    wi
    #
    @60
    @61
    @66
    @25
    @28
    cc0
    cL
    cle
    wbr
    #
    @60
    @61
    wa
    #
    @66
    wi
    fi1uzind.l
    cL
    nn0ge0
    @69
    @68
    @66
    @60
    @61
    @68
    @66
    wi
    #
    @61
    @60
    @70
    @68
    @61
    @60
    @60
    @66
    @68
    @61
    @60
    @60
    @66
    wi
    #
    wi
    @60
    @68
    @61
    wa
    #
    cc0
    @37
    cle
    wbr
    #
    @71
    @60
    cc0
    cr
    wcel
    cL
    cr
    wcel
    #
    @37
    cr
    wcel
    @72
    @73
    wi
    @60
    0red
    @28
    @74
    @60
    fi1uzind.l
    cL
    nn0re
    mp1i
    @37
    zre
    cc0
    cL
    @37
    letr
    syl3anc
    @73
    @60
    @66
    @73
    @60
    wa
    #
    cc0
    cn0
    wcel
    @37
    cc0
    cuz
    cfv
    wcel
    #
    @66
    0nn0
    @75
    @76
    @60
    @73
    wa
    #
    @73
    @60
    pm3.22
    cc0
    cz
    wcel
    @76
    @77
    wb
    @75
    0z
    cc0
    @37
    eluz1
    mp1i
    mpbird
    @37
    cc0
    eluznn0
    sylancr
    ex
    syl6com
    ex
    com14
    pm2.43a
    imp
    com12
    mp2b
    3adant1
    @66
    @44
    wa
    cc0
    @20
    clt
    wbr
    #
    @67
    @66
    @43
    @78
    @19
    @43
    @66
    @20
    @42
    wceq
    #
    @78
    @42
    @20
    eqcom
    #
    @66
    @79
    wa
    cc0
    @42
    @20
    clt
    @66
    cc0
    @42
    clt
    wbr
    @79
    @37
    nn0p1gt0
    adantr
    @66
    @79
    simpr
    breqtrrd
    sylan2b
    adantrl
    @44
    @66
    @78
    @67
    wi
    #
    @19
    @43
    @66
    @81
    wi
    #
    @18
    cvv
    wcel
    #
    @19
    @43
    @82
    wi
    wi
    vv
    vex
    #
    @83
    @78
    @43
    @66
    @19
    @67
    @83
    @78
    @43
    @66
    @19
    @67
    wi
    #
    wi
    wi
    #
    @83
    @78
    wa
    @7
    @18
    wcel
    #
    vn
    wex
    @86
    vn
    @18
    cvv
    hashgt0elex
    @87
    @86
    vn
    @19
    @87
    @43
    @66
    @67
    @19
    @87
    @43
    @66
    @67
    wi
    wi
    #
    @19
    @87
    wa
    wrh
    vb
    cF
    wsbc
    #
    va
    @18
    @7
    csn
    #
    cdif
    #
    wsbc
    #
    @88
    fi1uzind.3
    @19
    @87
    @92
    @88
    wi
    @66
    @87
    @92
    @43
    @19
    @67
    @66
    @87
    @92
    @43
    @85
    wi
    wi
    @66
    @87
    wa
    #
    @43
    @92
    @85
    @93
    @43
    @92
    @85
    wi
    #
    @91
    chash
    cfv
    #
    @37
    wceq
    #
    @93
    @43
    wa
    #
    @94
    @93
    @43
    @96
    @93
    @83
    @87
    @66
    @43
    @96
    wi
    @83
    @93
    @84
    a1i
    @66
    @87
    simpr
    @66
    @87
    simpl
    @43
    @79
    @83
    @87
    @66
    w3a
    @96
    @80
    @7
    @18
    cvv
    @37
    brfi1indlem
    syl5bi
    syl3anc
    imp
    @96
    @92
    @97
    @85
    @59
    @92
    @97
    @19
    @96
    wps
    @59
    @92
    @97
    @19
    @96
    wps
    wi
    @59
    @92
    wa
    #
    @97
    wa
    #
    @19
    wa
    #
    @42
    cn0
    wcel
    #
    @19
    @43
    @87
    w3a
    #
    wa
    #
    @96
    wch
    wps
    @100
    @101
    @102
    @97
    @101
    @98
    @19
    @66
    @101
    @87
    @43
    @37
    peano2nn0
    ad2antrr
    ad2antlr
    @100
    @19
    @43
    @87
    @99
    @19
    simpr
    @98
    @93
    @43
    @19
    simplrr
    @99
    @87
    @19
    @98
    @66
    @87
    @43
    simprlr
    adantr
    3jca
    jca
    @98
    @96
    wch
    wi
    @97
    @19
    @59
    @92
    @96
    wch
    @91
    cvv
    wcel
    #
    cF
    cvv
    wcel
    @59
    @92
    @96
    wa
    #
    wch
    wi
    #
    wi
    @83
    @104
    @84
    @18
    @90
    cvv
    difexg
    ax-mp
    fi1uzind.f
    @58
    @106
    vw
    vf
    @91
    cF
    cvv
    cvv
    @53
    @91
    wceq
    #
    @51
    cF
    wceq
    #
    wa
    #
    @57
    @105
    wth
    wch
    @109
    @54
    @92
    @56
    @96
    @109
    @52
    @89
    va
    @53
    @91
    @107
    @108
    simpl
    @109
    wrh
    vb
    @51
    cF
    @107
    @108
    simpr
    sbceq1d
    sbceqbid
    @107
    @56
    @96
    wb
    @108
    @56
    @55
    @37
    wceq
    @107
    @96
    @37
    @55
    eqcom
    @107
    @55
    @95
    @37
    @53
    @91
    chash
    fveq2
    eqeq1d
    syl5bb
    adantr
    anbi12d
    fi1uzind.4
    imbi12d
    spc2gv
    mp2an
    expdimp
    ad2antrr
    @103
    @101
    @19
    @79
    @87
    w3a
    #
    wa
    wch
    wps
    @102
    @110
    @101
    @43
    @79
    @19
    @87
    @80
    3anbi2i
    anbi2i
    fi1uzind.step
    sylanb
    syl6an
    exp41
    com15
    com23
    mpcom
    ex
    com23
    ex
    com15
    imp
    mpd
    ex
    com4l
    exlimiv
    syl
    ex
    com25
    ax-mp
    imp
    impcom
    mpd
    sylan
    impancom
    alrimivv
    ex
    syl5bi
    uzind
    syl3anc
    @1
    @8
    @24
    wph
    wi
    #
    cV
    cvv
    wcel
    #
    cE
    cvv
    wcel
    #
    wa
    #
    @1
    @8
    @111
    wi
    @1
    @112
    @113
    @0
    va
    cV
    sbcex
    @1
    wrh
    va
    cV
    wsbc
    #
    vb
    cE
    wsbc
    @113
    wrh
    va
    vb
    cV
    cE
    sbccom
    @115
    vb
    cE
    sbcex
    sylbi
    jca
    @114
    @1
    @8
    @111
    @114
    @24
    @12
    wph
    @23
    @13
    vv
    ve
    cV
    cE
    cvv
    cvv
    @18
    cV
    wceq
    #
    @16
    cE
    wceq
    #
    wa
    #
    @22
    @12
    wps
    wph
    @118
    @19
    @1
    @21
    @8
    @118
    @17
    @0
    va
    @18
    cV
    @116
    @117
    simpl
    @118
    wrh
    vb
    @16
    cE
    @116
    @117
    simpr
    sbceq1d
    sbceqbid
    @116
    @21
    @8
    wb
    @117
    @116
    @20
    @3
    @7
    @18
    cV
    chash
    fveq2
    eqeq2d
    adantr
    anbi12d
    fi1uzind.1
    imbi12d
    spc2gv
    com23
    expd
    mpcom
    imp
    syl5com
    exp31
    com14
    expcom
    com24
    pm2.43i
    imp
    exlimiv
    sylbi
    cV
    hashcl
    syl11
    3imp
end
