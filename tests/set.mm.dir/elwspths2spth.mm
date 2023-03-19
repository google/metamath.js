include "cupgr.mm"
include "wcel.mm"
include "c2.mm"
include "cwwspthsn.mm"
include "co.mm"
include "cv.mm"
include "cwwspthsnon.mm"
include "wrex.mm"
include "cs3.mm"
include "wceq.mm"
include "wa.mm"
include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "cc0.mm"
include "c1.mm"
include "w3a.mm"
include "wex.mm"
include "wb.mm"
include "wspthsnwspthsnon.mm"
include "a1i.mm"
include "elwspths2on.mm"
include "3expb.mm"
include "2rexbidva.mm"
include "rexcom.mm"
include "cwwlksnon.mm"
include "cspthson.mm"
include "wspthnon.mm"
include "ancom.mm"
include "19.41v.mm"
include "bitr4i.mm"
include "cwwlks.mm"
include "caddc.mm"
include "cvv.mm"
include "cword.mm"
include "simpr.mm"
include "anim12i.mm"
include "vex.mm"
include "s3cli.mm"
include "pm3.2i.mm"
include "isspthonpth.mm"
include "sylancl.mm"
include "cwwlksn.mm"
include "wwlknon.mm"
include "cn0.mm"
include "2nn0.mm"
include "iswwlksn.mm"
include "ax-mp.mm"
include "3anbi1d.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "adantr.mm"
include "simprl1.mm"
include "wi.mm"
include "cwlks.mm"
include "cmin.mm"
include "spthiswlk.mm"
include "wlklenvm1.mm"
include "simpl.mm"
include "oveq1.mm"
include "cc.mm"
include "2cn.mm"
include "pncan1.mm"
include "syl6eq.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "eqtrd.mm"
include "ex.mm"
include "3syl.mm"
include "imp.mm"
include "s3fv0.mm"
include "eqcomi.mm"
include "s3fv1.mm"
include "s3fv2.mm"
include "3pm3.2i.mm"
include "3jca.mm"
include "breq2.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "3anbi123d.mm"
include "3anbi13d.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "spcimedv.mm"
include "c3.mm"
include "wlklenvp1.mm"
include "2p1e3.mm"
include "biimpcd.mm"
include "3adant3.mm"
include "eqcom.mm"
include "3anbi123i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "jca.mm"
include "wlkpwrd.mm"
include "syl.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "eqwrds3.mm"
include "syl2anr.mm"
include "fveq2.mm"
include "3ad2ant2.mm"
include "wlkiswwlks1.mm"
include "syl5com.mm"
include "impcom.mm"
include "eleq1.mm"
include "bicomd.mm"
include "s3len.mm"
include "df-3.mm"
include "eqtri.mm"
include "jctir.mm"
include "mpdan.mm"
include "exlimdv.mm"
include "impbid.mm"
include "bitrd.mm"
include "exbidv.mm"
include "pm5.32da.mm"
include "rexbidva.mm"
include "3bitrd.mm"

theorem elwspths2spth
  let vf: setvar f
  let cG: class G
  let cV: class V
  let cW: class W
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume elwwlks2.v: |- V = ( Vtx ` G )

  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G f
  disjoint G p
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a p
  disjoint b c
  disjoint b f
  disjoint b p
  disjoint c f
  disjoint c p
  disjoint f p
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V f
  disjoint V p
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W f
  disjoint W p
  assert |- ( G e. UPGraph -> ( W e. ( 2 WSPathsN G ) <-> E. a e. V E. b e. V E. c e. V ( W = <" a b c "> /\ E. f E. p ( f ( SPaths ` G ) p /\ ( # ` f ) = 2 /\ ( a = ( p ` 0 ) /\ b = ( p ` 1 ) /\ c = ( p ` 2 ) ) ) ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cW
    c2
    cG
    cwwspthsn
    co
    wcel
    #
    cW
    va
    cv
    #
    vc
    cv
    #
    c2
    cG
    cwwspthsnon
    co
    co
    #
    wcel
    #
    vc
    cV
    wrex
    va
    cV
    wrex
    #
    cW
    @2
    vb
    cv
    #
    @3
    cs3
    #
    wceq
    #
    @8
    @4
    wcel
    #
    wa
    #
    vb
    cV
    wrex
    #
    vc
    cV
    wrex
    #
    va
    cV
    wrex
    @9
    vf
    cv
    #
    vp
    cv
    #
    cG
    cspths
    cfv
    #
    wbr
    #
    @14
    chash
    cfv
    #
    c2
    wceq
    #
    @2
    cc0
    @15
    cfv
    #
    wceq
    #
    @7
    c1
    @15
    cfv
    #
    wceq
    #
    @3
    c2
    @15
    cfv
    #
    wceq
    #
    w3a
    #
    w3a
    #
    vp
    wex
    #
    vf
    wex
    #
    wa
    #
    vc
    cV
    wrex
    vb
    cV
    wrex
    #
    va
    cV
    wrex
    @1
    @6
    wb
    @0
    cG
    c2
    cV
    cW
    va
    vc
    elwwlks2.v
    wspthsnwspthsnon
    a1i
    @0
    @5
    @12
    va
    vc
    cV
    cV
    @0
    @2
    cV
    wcel
    #
    @3
    cV
    wcel
    #
    @5
    @12
    wb
    @2
    @3
    cG
    cV
    cW
    vb
    elwwlks2.v
    elwspths2on
    3expb
    2rexbidva
    @0
    @13
    @31
    va
    cV
    @13
    @11
    vc
    cV
    wrex
    vb
    cV
    wrex
    @0
    @32
    wa
    #
    @31
    @11
    vc
    vb
    cV
    cV
    rexcom
    @34
    @11
    @30
    vb
    vc
    cV
    cV
    @34
    @7
    cV
    wcel
    #
    @33
    wa
    #
    wa
    #
    @9
    @10
    @29
    @10
    @8
    @2
    @3
    c2
    cG
    cwwlksnon
    co
    co
    wcel
    #
    @14
    @8
    @2
    @3
    cG
    cspthson
    cfv
    co
    wbr
    #
    vf
    wex
    #
    wa
    #
    @37
    @9
    wa
    #
    @29
    @2
    @3
    vf
    cG
    c2
    @8
    wspthnon
    @41
    @39
    @38
    wa
    #
    vf
    wex
    #
    @42
    @29
    @41
    @40
    @38
    wa
    @44
    @38
    @40
    ancom
    @39
    @38
    vf
    19.41v
    bitr4i
    @42
    @43
    @28
    vf
    @42
    @43
    @14
    @8
    @16
    wbr
    #
    cc0
    @8
    cfv
    #
    @2
    wceq
    #
    @18
    @8
    cfv
    #
    @3
    wceq
    #
    w3a
    #
    @8
    cG
    cwwlks
    cfv
    #
    wcel
    #
    @8
    chash
    cfv
    #
    c2
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    @47
    c2
    @8
    cfv
    #
    @3
    wceq
    #
    w3a
    #
    wa
    #
    @28
    @37
    @43
    @60
    wb
    @9
    @37
    @39
    @50
    @38
    @59
    @37
    @32
    @33
    wa
    @14
    cvv
    wcel
    #
    @8
    cvv
    cword
    #
    wcel
    #
    wa
    @39
    @50
    wb
    @34
    @32
    @36
    @33
    @0
    @32
    simpr
    #
    @35
    @33
    simpr
    anim12i
    @61
    @63
    vf
    vex
    @2
    @7
    @3
    s3cli
    #
    pm3.2i
    @2
    @3
    @8
    @14
    cG
    cV
    cvv
    @62
    elwwlks2.v
    isspthonpth
    sylancl
    @38
    @8
    c2
    cG
    cwwlksn
    co
    wcel
    #
    @47
    @58
    w3a
    @37
    @59
    @2
    @3
    cG
    c2
    @8
    wwlknon
    @37
    @66
    @56
    @47
    @58
    @66
    @56
    wb
    #
    @37
    c2
    cn0
    wcel
    @67
    2nn0
    cG
    c2
    @8
    iswwlksn
    ax-mp
    a1i
    3anbi1d
    syl5bb
    anbi12d
    adantr
    @37
    @60
    @28
    wb
    @9
    @37
    @60
    @28
    @37
    @27
    @60
    vp
    @8
    @62
    @63
    @37
    @65
    a1i
    @37
    @15
    @8
    wceq
    #
    wa
    #
    @60
    @27
    @69
    @60
    wa
    #
    @27
    @45
    @19
    @2
    @46
    wceq
    #
    @7
    c1
    @8
    cfv
    #
    wceq
    #
    @3
    @57
    wceq
    #
    w3a
    #
    w3a
    #
    @70
    @45
    @19
    @75
    @45
    @47
    @49
    @59
    @69
    simprl1
    @60
    @19
    @69
    @50
    @59
    @19
    @45
    @47
    @59
    @19
    wi
    #
    @49
    @45
    @14
    @8
    cG
    cwlks
    cfv
    #
    wbr
    @18
    @53
    c1
    cmin
    co
    #
    wceq
    #
    @77
    @8
    @14
    cG
    spthiswlk
    @8
    @14
    cG
    wlklenvm1
    @80
    @59
    @19
    @80
    @59
    wa
    @18
    @79
    c2
    @80
    @59
    simpl
    @59
    @79
    c2
    wceq
    #
    @80
    @56
    @47
    @81
    @58
    @55
    @81
    @52
    @55
    @79
    @54
    c1
    cmin
    co
    #
    c2
    @53
    @54
    c1
    cmin
    oveq1
    c2
    cc
    wcel
    @82
    c2
    wceq
    2cn
    c2
    pncan1
    ax-mp
    syl6eq
    adantl
    3ad2ant1
    adantl
    eqtrd
    ex
    3syl
    3ad2ant1
    imp
    adantl
    @75
    @70
    @71
    @73
    @74
    @46
    @2
    @2
    cvv
    wcel
    @47
    va
    vex
    @2
    @7
    @3
    cvv
    s3fv0
    ax-mp
    #
    eqcomi
    @72
    @7
    @7
    cvv
    wcel
    @72
    @7
    wceq
    vb
    vex
    @2
    @7
    @3
    cvv
    s3fv1
    ax-mp
    eqcomi
    @57
    @3
    @3
    cvv
    wcel
    @58
    vc
    vex
    @2
    @7
    @3
    cvv
    s3fv2
    ax-mp
    #
    eqcomi
    3pm3.2i
    a1i
    3jca
    @68
    @27
    @76
    wb
    @37
    @60
    @68
    @17
    @45
    @26
    @75
    @19
    @15
    @8
    @14
    @16
    breq2
    #
    @68
    @21
    @71
    @23
    @73
    @25
    @74
    @68
    @20
    @46
    @2
    cc0
    @15
    @8
    fveq1
    eqeq2d
    @68
    @22
    @72
    @7
    c1
    @15
    @8
    fveq1
    eqeq2d
    @68
    @24
    @57
    @3
    c2
    @15
    @8
    fveq1
    eqeq2d
    3anbi123d
    3anbi13d
    ad2antlr
    mpbird
    ex
    spcimedv
    @37
    @27
    @60
    vp
    @37
    @27
    @60
    @37
    @27
    wa
    #
    @68
    @60
    @86
    @68
    @15
    chash
    cfv
    #
    c3
    wceq
    #
    @20
    @2
    wceq
    #
    @22
    @7
    wceq
    #
    @24
    @3
    wceq
    #
    w3a
    #
    wa
    #
    @86
    @88
    @92
    @27
    @88
    @37
    @17
    @19
    @88
    @26
    @17
    @19
    @88
    @17
    @14
    @15
    @78
    wbr
    #
    @87
    @18
    c1
    caddc
    co
    #
    wceq
    #
    @19
    @88
    wi
    @15
    @14
    cG
    spthiswlk
    #
    @15
    @14
    cG
    wlklenvp1
    @19
    @96
    @88
    @19
    @95
    c3
    @87
    @19
    @95
    @54
    c3
    @18
    c2
    c1
    caddc
    oveq1
    2p1e3
    syl6eq
    eqeq2d
    biimpcd
    3syl
    imp
    3adant3
    adantl
    @27
    @92
    @37
    @26
    @17
    @92
    @19
    @26
    @92
    @21
    @89
    @23
    @90
    @25
    @91
    @2
    @20
    eqcom
    @7
    @22
    eqcom
    @3
    @24
    eqcom
    3anbi123i
    biimpi
    3ad2ant3
    adantl
    jca
    @27
    @15
    cV
    cword
    wcel
    #
    @32
    @35
    @33
    w3a
    #
    @68
    @93
    wb
    @37
    @17
    @19
    @98
    @26
    @17
    @94
    @98
    @97
    @15
    @14
    cG
    cV
    elwwlks2.v
    wlkpwrd
    syl
    3ad2ant1
    @37
    @32
    @36
    wa
    @99
    @34
    @32
    @36
    @64
    anim1i
    @32
    @35
    @33
    3anass
    sylibr
    @2
    @7
    @3
    cV
    @15
    eqwrds3
    syl2anr
    mpbird
    @86
    @68
    wa
    #
    @50
    @59
    @100
    @45
    @47
    @49
    @86
    @68
    @45
    @27
    @68
    @45
    wi
    #
    @37
    @17
    @19
    @101
    @26
    @68
    @17
    @45
    @85
    biimpcd
    3ad2ant1
    adantl
    imp
    @47
    @100
    @83
    a1i
    #
    @27
    @49
    @37
    @68
    @19
    @17
    @49
    @26
    @19
    @48
    @57
    @3
    @18
    c2
    @8
    fveq2
    @84
    syl6eq
    3ad2ant2
    ad2antlr
    3jca
    @100
    @56
    @47
    @58
    @100
    @52
    @55
    @100
    @52
    @15
    @51
    wcel
    #
    @86
    @103
    @68
    @27
    @37
    @103
    @17
    @19
    @37
    @103
    wi
    @26
    @17
    @94
    @37
    @103
    @97
    @34
    @94
    @103
    wi
    #
    @36
    @0
    @104
    @32
    @15
    @14
    cG
    wlkiswwlks1
    adantr
    adantr
    syl5com
    3ad2ant1
    impcom
    adantr
    @68
    @52
    @103
    wb
    @86
    @68
    @103
    @52
    @15
    @8
    @51
    eleq1
    bicomd
    adantl
    mpbird
    @53
    c3
    @54
    @2
    @7
    @3
    s3len
    df-3
    eqtri
    jctir
    @102
    @58
    @100
    @84
    a1i
    3jca
    jca
    mpdan
    ex
    exlimdv
    impbid
    adantr
    bitrd
    exbidv
    syl5bb
    syl5bb
    pm5.32da
    2rexbidva
    syl5bb
    rexbidva
    3bitrd
end
