include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "w3o.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cc0.mm"
include "cle.mm"
include "c1.mm"
include "cfz.mm"
include "wral.mm"
include "wceq.mm"
include "wa.mm"
include "brbtwn2.mm"
include "wb.mm"
include "3comr.mm"
include "colinearalglem3.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "colinearalglem2.mm"
include "3coml.mm"
include "3orbi123d.mm"
include "wi.mm"
include "cc.mm"
include "fveecn.mm"
include "subid.mm"
include "oveq2d.mm"
include "adantl.mm"
include "subcl.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "syl2an.mm"
include "anandirs.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "ralrimiva.mm"
include "3adant1.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "syl5ibcom.mm"
include "3mix1.mm"
include "syl6.mm"
include "a1dd.mm"
include "wne.mm"
include "wrex.mm"
include "wn.mm"
include "simp3.mm"
include "simp1.mm"
include "eqeefv.mm"
include "syl2anc.mm"
include "necon3abid.mm"
include "df-ne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "ralcom.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "ad2antrl.mm"
include "cr.mm"
include "fveere.mm"
include "3ad2antl1.mm"
include "3ad2antl2.mm"
include "3ad2antl3.mm"
include "3jca.mm"
include "anim1i.mm"
include "anasss.mm"
include "cdiv.mm"
include "caddc.mm"
include "adantlr.mm"
include "recn.mm"
include "3anim123i.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "simplrr.mm"
include "eqcom.mm"
include "simp12.mm"
include "simp11.mm"
include "simp22.mm"
include "simp21.mm"
include "subcld.mm"
include "simp23.mm"
include "simpr3.mm"
include "simpr1.mm"
include "subeq0ad.mm"
include "necon3bid.mm"
include "biimp3ar.mm"
include "divcld.mm"
include "simp13.mm"
include "mulcld.mm"
include "subadd2.mm"
include "bicomd.mm"
include "syl3anc.mm"
include "div23d.mm"
include "eqeq2d.mm"
include "divmuld.mm"
include "mulcomd.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "3bitr2d.mm"
include "ralbidva.mm"
include "3simpb.mm"
include "simpl2.mm"
include "simpl1.mm"
include "resubcld.mm"
include "simpl3.mm"
include "recnd.mm"
include "3ad2ant1.mm"
include "biimpar.mm"
include "redivcld.mm"
include "colinearalglem4.mm"
include "oveq1.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl.mm"
include "oveq2.mm"
include "syl5ibrcom.mm"
include "sylbird.mm"
include "syldan.mm"
include "syld.mm"
include "syl5bi.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"
include "pm2.61dne.mm"
include "pm4.71rd.mm"
include "wo.mm"
include "andir.mm"
include "orbi1i.mm"
include "df-3or.mm"
include "anbi1i.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "syl6rbb.mm"

theorem colinearalg
  let cA: class A
  let cB: class B
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let cN: class N
  let vp: setvar p

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint A i
  disjoint A j
  disjoint B i
  disjoint B j
  disjoint C i
  disjoint C j
  disjoint N p
  disjoint i p
  disjoint j p
  disjoint A p
  disjoint B p
  disjoint C p
  assert |- ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) -> ( ( A Btwn <. B , C >. \/ B Btwn <. C , A >. \/ C Btwn <. A , B >. ) <-> A. i e. ( 1 ... N ) A. j e. ( 1 ... N ) ( ( ( B ` i ) - ( A ` i ) ) x. ( ( C ` j ) - ( A ` j ) ) ) = ( ( ( B ` j ) - ( A ` j ) ) x. ( ( C ` i ) - ( A ` i ) ) ) ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cC
    @0
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cop
    cbtwn
    wbr
    #
    cB
    cC
    cA
    cop
    cbtwn
    wbr
    #
    cC
    cA
    cB
    cop
    cbtwn
    wbr
    #
    w3o
    vi
    cv
    #
    cB
    cfv
    #
    @8
    cA
    cfv
    #
    cmin
    co
    #
    @8
    cC
    cfv
    #
    @10
    cmin
    co
    #
    cmul
    co
    #
    cc0
    cle
    wbr
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    @11
    vj
    cv
    #
    cC
    cfv
    #
    @18
    cA
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    @18
    cB
    cfv
    #
    @20
    cmin
    co
    #
    @13
    cmul
    co
    #
    wceq
    #
    vj
    @16
    wral
    vi
    @16
    wral
    #
    wa
    #
    @12
    @9
    cmin
    co
    #
    @10
    @9
    cmin
    co
    #
    cmul
    co
    #
    cc0
    cle
    wbr
    #
    vi
    @16
    wral
    #
    @27
    wa
    #
    @10
    @12
    cmin
    co
    #
    @9
    @12
    cmin
    co
    #
    cmul
    co
    #
    cc0
    cle
    wbr
    #
    vi
    @16
    wral
    #
    @27
    wa
    #
    w3o
    #
    @27
    @4
    @5
    @28
    @6
    @34
    @7
    @40
    cA
    cB
    cC
    vi
    vj
    cN
    brbtwn2
    @4
    @6
    @33
    @29
    @20
    @23
    cmin
    co
    cmul
    co
    @19
    @23
    cmin
    co
    @30
    cmul
    co
    wceq
    vj
    @16
    wral
    vi
    @16
    wral
    #
    wa
    #
    @34
    @2
    @3
    @1
    @6
    @43
    wb
    cB
    cC
    cA
    vi
    vj
    cN
    brbtwn2
    3comr
    @4
    @42
    @27
    @33
    @2
    @3
    @1
    @42
    @27
    wb
    cB
    cC
    cA
    vi
    vj
    cN
    colinearalglem3
    3comr
    anbi2d
    bitrd
    @3
    @1
    @2
    @7
    @40
    wb
    @3
    @1
    @2
    w3a
    #
    @7
    @39
    @35
    @23
    @19
    cmin
    co
    cmul
    co
    @20
    @19
    cmin
    co
    @36
    cmul
    co
    wceq
    vj
    @16
    wral
    vi
    @16
    wral
    #
    wa
    @40
    cC
    cA
    cB
    vi
    vj
    cN
    brbtwn2
    @44
    @45
    @27
    @39
    cC
    cA
    cB
    vi
    vj
    cN
    colinearalglem2
    anbi2d
    bitrd
    3coml
    3orbi123d
    @4
    @27
    @17
    @33
    @39
    w3o
    #
    @27
    wa
    #
    @41
    @4
    @27
    @46
    @4
    @27
    @46
    wi
    #
    cC
    cA
    @4
    cC
    cA
    wceq
    #
    @46
    @27
    @4
    @49
    @17
    @46
    @4
    @36
    @12
    @12
    cmin
    co
    #
    cmul
    co
    #
    cc0
    cle
    wbr
    #
    vi
    @16
    wral
    #
    @49
    @17
    @2
    @3
    @53
    @1
    @2
    @3
    wa
    #
    @52
    vi
    @16
    @54
    @8
    @16
    wcel
    #
    wa
    @51
    cc0
    cc0
    cle
    @2
    @3
    @55
    @51
    cc0
    wceq
    #
    @2
    @55
    wa
    @9
    cc
    wcel
    #
    @12
    cc
    wcel
    #
    @56
    @3
    @55
    wa
    cB
    @8
    cN
    fveecn
    #
    cC
    @8
    cN
    fveecn
    #
    @57
    @58
    wa
    #
    @51
    @36
    cc0
    cmul
    co
    #
    cc0
    @58
    @51
    @62
    wceq
    @57
    @58
    @50
    cc0
    @36
    cmul
    @12
    subid
    oveq2d
    adantl
    @61
    @36
    @9
    @12
    subcl
    mul01d
    eqtrd
    syl2an
    anandirs
    0le0
    syl6eqbr
    ralrimiva
    3adant1
    @49
    @52
    @15
    vi
    @16
    @49
    @51
    @14
    cc0
    cle
    @49
    @36
    @11
    @50
    @13
    cmul
    @49
    @12
    @10
    @9
    cmin
    @8
    cC
    cA
    fveq1
    #
    oveq2d
    @49
    @12
    @10
    @12
    cmin
    @63
    oveq2d
    oveq12d
    breq1d
    ralbidv
    syl5ibcom
    @17
    @33
    @39
    3mix1
    syl6
    a1dd
    @4
    cC
    cA
    wne
    #
    vp
    cv
    #
    cC
    cfv
    #
    @65
    cA
    cfv
    #
    wne
    #
    vp
    @16
    wrex
    #
    @48
    @4
    @64
    @66
    @67
    wceq
    #
    vp
    @16
    wral
    #
    wn
    #
    @69
    @4
    @71
    cC
    cA
    @4
    @3
    @1
    @49
    @71
    wb
    @1
    @2
    @3
    simp3
    @1
    @2
    @3
    simp1
    cC
    cA
    vp
    cN
    eqeefv
    syl2anc
    necon3abid
    @69
    @70
    wn
    #
    vp
    @16
    wrex
    @72
    @68
    @73
    vp
    @16
    @66
    @67
    df-ne
    rexbii
    @70
    vp
    @16
    rexnal
    bitr2i
    syl6bb
    @4
    @68
    @48
    vp
    @16
    @27
    @26
    vi
    @16
    wral
    #
    vj
    @16
    wral
    #
    @4
    @65
    @16
    wcel
    #
    @68
    wa
    #
    wa
    #
    @46
    @26
    vi
    vj
    @16
    @16
    ralcom
    @78
    @75
    @11
    @66
    @67
    cmin
    co
    #
    cmul
    co
    #
    @65
    cB
    cfv
    #
    @67
    cmin
    co
    #
    @13
    cmul
    co
    #
    wceq
    #
    vi
    @16
    wral
    #
    @46
    @76
    @75
    @85
    wi
    @4
    @68
    @74
    @85
    vj
    @65
    @16
    vj
    vp
    weq
    #
    @26
    @84
    vi
    @16
    @86
    @22
    @80
    @25
    @83
    @86
    @21
    @79
    @11
    cmul
    @86
    @19
    @66
    @20
    @67
    cmin
    @18
    @65
    cC
    fveq2
    @18
    @65
    cA
    fveq2
    #
    oveq12d
    oveq2d
    @86
    @24
    @82
    @13
    cmul
    @86
    @23
    @81
    @20
    @67
    cmin
    @18
    @65
    cB
    fveq2
    @87
    oveq12d
    oveq1d
    eqeq12d
    ralbidv
    rspcv
    ad2antrl
    @4
    @77
    @67
    cr
    wcel
    #
    @81
    cr
    wcel
    #
    @66
    cr
    wcel
    #
    w3a
    #
    @68
    wa
    #
    @85
    @46
    wi
    @4
    @76
    @68
    @92
    @4
    @76
    wa
    #
    @91
    @68
    @93
    @88
    @89
    @90
    @1
    @2
    @76
    @88
    @3
    cA
    @65
    cN
    fveere
    3ad2antl1
    @2
    @1
    @76
    @89
    @3
    cB
    @65
    cN
    fveere
    3ad2antl2
    @3
    @1
    @76
    @90
    @2
    cC
    @65
    cN
    fveere
    3ad2antl3
    3jca
    anim1i
    anasss
    @4
    @92
    wa
    #
    @85
    @9
    @82
    @79
    cdiv
    co
    #
    @13
    cmul
    co
    #
    @10
    caddc
    co
    #
    wceq
    #
    vi
    @16
    wral
    #
    @46
    @94
    @98
    @84
    vi
    @16
    @94
    @55
    wa
    @10
    cc
    wcel
    #
    @57
    @58
    w3a
    #
    @67
    cc
    wcel
    #
    @81
    cc
    wcel
    #
    @66
    cc
    wcel
    #
    w3a
    #
    @68
    @98
    @84
    wb
    @4
    @55
    @101
    @92
    @4
    @55
    wa
    @100
    @57
    @58
    @1
    @2
    @55
    @100
    @3
    cA
    @8
    cN
    fveecn
    3ad2antl1
    @2
    @1
    @55
    @57
    @3
    @59
    3ad2antl2
    @3
    @1
    @55
    @58
    @2
    @60
    3ad2antl3
    3jca
    adantlr
    @92
    @105
    @4
    @55
    @91
    @105
    @68
    @88
    @102
    @89
    @103
    @90
    @104
    @67
    recn
    #
    @81
    recn
    @66
    recn
    3anim123i
    adantr
    ad2antlr
    @4
    @91
    @68
    @55
    simplrr
    @98
    @97
    @9
    wceq
    #
    @101
    @105
    @68
    w3a
    #
    @84
    @9
    @97
    eqcom
    @108
    @107
    @11
    @96
    wceq
    #
    @11
    @83
    @79
    cdiv
    co
    #
    wceq
    #
    @84
    @108
    @57
    @100
    @96
    cc
    wcel
    #
    @107
    @109
    wb
    @100
    @57
    @58
    @105
    @68
    simp12
    #
    @100
    @57
    @58
    @105
    @68
    simp11
    #
    @108
    @95
    @13
    @108
    @82
    @79
    @108
    @81
    @67
    @101
    @102
    @103
    @104
    @68
    simp22
    @101
    @102
    @103
    @104
    @68
    simp21
    #
    subcld
    #
    @108
    @66
    @67
    @101
    @102
    @103
    @104
    @68
    simp23
    @115
    subcld
    #
    @101
    @105
    @79
    cc0
    wne
    #
    @68
    @101
    @105
    wa
    #
    @79
    cc0
    @66
    @67
    @119
    @66
    @67
    @101
    @102
    @103
    @104
    simpr3
    @101
    @102
    @103
    @104
    simpr1
    subeq0ad
    necon3bid
    biimp3ar
    #
    divcld
    @108
    @12
    @10
    @100
    @57
    @58
    @105
    @68
    simp13
    @114
    subcld
    #
    mulcld
    @57
    @100
    @112
    w3a
    @109
    @107
    @9
    @10
    @96
    subadd2
    bicomd
    syl3anc
    @108
    @110
    @96
    @11
    @108
    @82
    @13
    @79
    @116
    @121
    @117
    @120
    div23d
    eqeq2d
    @111
    @110
    @11
    wceq
    #
    @108
    @84
    @11
    @110
    eqcom
    @108
    @122
    @79
    @11
    cmul
    co
    #
    @83
    wceq
    @84
    @108
    @83
    @79
    @11
    @108
    @82
    @13
    @116
    @121
    mulcld
    @117
    @108
    @9
    @10
    @113
    @114
    subcld
    #
    @120
    divmuld
    @108
    @123
    @80
    @83
    @108
    @79
    @11
    @117
    @124
    mulcomd
    eqeq1d
    bitrd
    syl5bb
    3bitr2d
    syl5bb
    syl3anc
    ralbidva
    @4
    @1
    @3
    wa
    #
    @95
    cr
    wcel
    #
    @99
    @46
    wi
    @92
    @1
    @2
    @3
    3simpb
    @92
    @82
    @79
    @92
    @81
    @67
    @88
    @89
    @90
    @68
    simpl2
    @88
    @89
    @90
    @68
    simpl1
    #
    resubcld
    @92
    @66
    @67
    @88
    @89
    @90
    @68
    simpl3
    @127
    resubcld
    @91
    @118
    @68
    @91
    @79
    cc0
    @66
    @67
    @91
    @66
    @67
    @91
    @66
    @88
    @89
    @90
    simp3
    recnd
    @88
    @89
    @102
    @90
    @106
    3ad2ant1
    subeq0ad
    necon3bid
    biimpar
    redivcld
    @125
    @126
    wa
    @46
    @99
    @97
    @10
    cmin
    co
    #
    @13
    cmul
    co
    #
    cc0
    cle
    wbr
    #
    vi
    @16
    wral
    #
    @12
    @97
    cmin
    co
    #
    @10
    @97
    cmin
    co
    #
    cmul
    co
    #
    cc0
    cle
    wbr
    #
    vi
    @16
    wral
    #
    @35
    @97
    @12
    cmin
    co
    #
    cmul
    co
    #
    cc0
    cle
    wbr
    #
    vi
    @16
    wral
    #
    w3o
    cA
    cC
    vi
    @95
    cN
    colinearalglem4
    @99
    @17
    @131
    @33
    @136
    @39
    @140
    @99
    @15
    @130
    wb
    #
    vi
    @16
    wral
    @17
    @131
    wb
    @98
    @141
    vi
    @16
    @98
    @14
    @129
    cc0
    cle
    @98
    @11
    @128
    @13
    cmul
    @9
    @97
    @10
    cmin
    oveq1
    oveq1d
    breq1d
    ralimi
    @15
    @130
    vi
    @16
    ralbi
    syl
    @99
    @32
    @135
    wb
    #
    vi
    @16
    wral
    @33
    @136
    wb
    @98
    @142
    vi
    @16
    @98
    @31
    @134
    cc0
    cle
    @98
    @29
    @132
    @30
    @133
    cmul
    @9
    @97
    @12
    cmin
    oveq2
    @9
    @97
    @10
    cmin
    oveq2
    oveq12d
    breq1d
    ralimi
    @32
    @135
    vi
    @16
    ralbi
    syl
    @99
    @38
    @139
    wb
    #
    vi
    @16
    wral
    @39
    @140
    wb
    @98
    @143
    vi
    @16
    @98
    @37
    @138
    cc0
    cle
    @98
    @36
    @137
    @35
    cmul
    @9
    @97
    @12
    cmin
    oveq1
    oveq2d
    breq1d
    ralimi
    @38
    @139
    vi
    @16
    ralbi
    syl
    3orbi123d
    syl5ibrcom
    syl2an
    sylbird
    syldan
    syld
    syl5bi
    rexlimdvaa
    sylbid
    pm2.61dne
    pm4.71rd
    @17
    @33
    wo
    #
    @27
    wa
    #
    @40
    wo
    #
    @28
    @34
    wo
    #
    @40
    wo
    @47
    @41
    @145
    @147
    @40
    @17
    @33
    @27
    andir
    orbi1i
    @47
    @144
    @39
    wo
    #
    @27
    wa
    @146
    @46
    @148
    @27
    @17
    @33
    @39
    df-3or
    anbi1i
    @144
    @39
    @27
    andir
    bitri
    @28
    @34
    @40
    df-3or
    3bitr4i
    syl6rbb
    bitrd
end
