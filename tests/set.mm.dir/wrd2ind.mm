include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "cn0.mm"
include "lencl.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantl.mm"
include "c0.mm"
include "eqcom.mm"
include "hasheq0.mm"
include "syl5bb.mm"
include "mpbiri.mm"
include "ex.mm"
include "syl6bi.mm"
include "com13.mm"
include "com24.mm"
include "imp31.mm"
include "sylbid.mm"
include "com23.mm"
include "impd.mm"
include "rgen2.mm"
include "fveq2.mm"
include "eqeqan12d.mm"
include "eqeq1d.mm"
include "adantr.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "ancoms.mm"
include "cbvraldva.mm"
include "cbvralv.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cs1.mm"
include "cconcat.mm"
include "wsbc.mm"
include "swrdcl.mm"
include "ad2antrl.mm"
include "wne.mm"
include "simprll.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "nnge1d.mm"
include "wrdlenge1n0.mm"
include "syl.mm"
include "mpbird.mm"
include "lswcl.mm"
include "syl2anc.mm"
include "jca.mm"
include "simprlr.mm"
include "ad2antll.mm"
include "jca32.mm"
include "adantlr.mm"
include "simprl.mm"
include "simplr.mm"
include "simprrl.mm"
include "oveq1d.mm"
include "cfz.mm"
include "cfzo.mm"
include "fzossfz.mm"
include "simprrr.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "fzo0end.mm"
include "sseldi.mm"
include "swrd0len.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eleq12d.mm"
include "3eqtr4d.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "3eqtrd.mm"
include "expcom.mm"
include "imp.mm"
include "vex.mm"
include "sbc2ie.mm"
include "bicomi.mm"
include "a1i.mm"
include "simpr.mm"
include "sbceq1d.mm"
include "dfsbcq.mm"
include "sbcbidv.mm"
include "3bitrd.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "syl3c.mm"
include "sbccom.mm"
include "syl6bb.mm"
include "eqeq2d.mm"
include "s1eq.mm"
include "oveq2d.mm"
include "imbi2d.mm"
include "bitrd.mm"
include "simpll.mm"
include "syl3anc.mm"
include "ovex.mm"
include "3imtr4g.mm"
include "vtocl4ga.mm"
include "sylc.mm"
include "eqtr2.mm"
include "cfn.mm"
include "wrdfin.mm"
include "hashnncl.mm"
include "mpbid.mm"
include "swrdccatwrd.mm"
include "eqcomd.mm"
include "sbceq1a.mm"
include "sylan9bb.mm"
include "expr.mm"
include "ralrimivva.mm"
include "syl5bi.mm"
include "nn0ind.mm"
include "3ad2ant1.mm"
include "anbi1d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "3ad2ant2.mm"
include "mpd.mm"
include "eqidd.mm"
include "expd.mm"
include "com34.mm"
include "3adant2.mm"
include "mp2d.mm"

theorem wrd2ind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wrh: wff rh
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vn: setvar n
  let vm: setvar m
  assume wrd2ind.1: |- ( ( x = (/) /\ w = (/) ) -> ( ph <-> ps ) )
  assume wrd2ind.2: |- ( ( x = y /\ w = u ) -> ( ph <-> ch ) )
  assume wrd2ind.3: |- ( ( x = ( y ++ <" z "> ) /\ w = ( u ++ <" s "> ) ) -> ( ph <-> th ) )
  assume wrd2ind.4: |- ( x = A -> ( rh <-> ta ) )
  assume wrd2ind.5: |- ( w = B -> ( ph <-> rh ) )
  assume wrd2ind.6: |- ps
  assume wrd2ind.7: |- ( ( ( y e. Word X /\ z e. X ) /\ ( u e. Word Y /\ s e. Y ) /\ ( # ` y ) = ( # ` u ) ) -> ( ch -> th ) )

  disjoint w x
  disjoint A w
  disjoint A x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint X s
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y s
  disjoint Y u
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint ch w
  disjoint ch x
  disjoint ph s
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint ta x
  disjoint th w
  disjoint th x
  disjoint rh w
  disjoint n w
  disjoint n x
  disjoint A n
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint m s
  disjoint m u
  disjoint X m
  disjoint n s
  disjoint n u
  disjoint X n
  disjoint Y m
  disjoint Y n
  disjoint m ph
  disjoint n ph
  assert |- ( ( A e. Word X /\ B e. Word Y /\ ( # ` A ) = ( # ` B ) ) -> ta )

  proof
    cA
    cX
    cword
    #
    wcel
    #
    cB
    cY
    cword
    #
    wcel
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    wceq
    #
    w3a
    #
    vx
    cv
    #
    chash
    cfv
    #
    @5
    wceq
    #
    @9
    @4
    wceq
    #
    wa
    #
    wrh
    wi
    #
    vx
    @0
    wral
    #
    @4
    @4
    wceq
    #
    wta
    @7
    @9
    vw
    cv
    #
    chash
    cfv
    #
    wceq
    #
    @11
    wa
    #
    wph
    wi
    #
    vx
    @0
    wral
    #
    vw
    @2
    wral
    #
    @14
    @1
    @3
    @22
    @6
    @1
    @4
    cn0
    wcel
    @22
    cX
    cA
    lencl
    @18
    @9
    vn
    cv
    #
    wceq
    #
    wa
    #
    wph
    wi
    #
    vx
    @0
    wral
    vw
    @2
    wral
    @18
    @9
    cc0
    wceq
    #
    wa
    #
    wph
    wi
    #
    vx
    @0
    wral
    vw
    @2
    wral
    @18
    @9
    vm
    cv
    #
    wceq
    #
    wa
    #
    wph
    wi
    #
    vx
    @0
    wral
    #
    vw
    @2
    wral
    #
    @18
    @9
    @30
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    wph
    wi
    #
    vx
    @0
    wral
    vw
    @2
    wral
    #
    @22
    vn
    vm
    @4
    @23
    cc0
    wceq
    #
    @26
    @29
    vw
    vx
    @2
    @0
    @41
    @25
    @28
    wph
    @41
    @24
    @27
    @18
    @23
    cc0
    @9
    eqeq2
    anbi2d
    imbi1d
    2ralbidv
    @23
    @30
    wceq
    #
    @26
    @33
    vw
    vx
    @2
    @0
    @42
    @25
    @32
    wph
    @42
    @24
    @31
    @18
    @23
    @30
    @9
    eqeq2
    anbi2d
    imbi1d
    2ralbidv
    @23
    @36
    wceq
    #
    @26
    @39
    vw
    vx
    @2
    @0
    @43
    @25
    @38
    wph
    @43
    @24
    @37
    @18
    @23
    @36
    @9
    eqeq2
    anbi2d
    imbi1d
    2ralbidv
    @23
    @4
    wceq
    #
    @26
    @20
    vw
    vx
    @2
    @0
    @44
    @25
    @19
    wph
    @44
    @24
    @11
    @18
    @23
    @4
    @9
    eqeq2
    anbi2d
    imbi1d
    2ralbidv
    @29
    vw
    vx
    @2
    @0
    @16
    @2
    wcel
    #
    @8
    @0
    wcel
    #
    wa
    #
    @18
    @27
    wph
    @47
    @27
    @18
    wph
    @47
    @27
    @18
    wph
    wi
    @47
    @27
    wa
    @18
    cc0
    @17
    wceq
    #
    wph
    @27
    @18
    @48
    wb
    @47
    @9
    cc0
    @17
    eqeq1
    adantl
    @45
    @46
    @27
    @48
    wph
    wi
    @45
    @48
    @27
    @46
    wph
    @45
    @48
    @16
    c0
    wceq
    #
    @27
    @46
    wph
    wi
    wi
    @48
    @17
    cc0
    wceq
    @45
    @49
    cc0
    @17
    eqcom
    @16
    @2
    hasheq0
    syl5bb
    @46
    @27
    @49
    wph
    @46
    @27
    @8
    c0
    wceq
    #
    @49
    wph
    wi
    @8
    @0
    hasheq0
    @50
    @49
    wph
    @50
    @49
    wa
    wph
    wps
    wrd2ind.6
    wrd2ind.1
    mpbiri
    ex
    syl6bi
    com13
    syl6bi
    com24
    imp31
    sylbid
    ex
    com23
    impd
    rgen2
    @35
    vy
    cv
    #
    chash
    cfv
    #
    vu
    cv
    #
    chash
    cfv
    #
    wceq
    #
    @52
    @30
    wceq
    #
    wa
    #
    wch
    wi
    #
    vy
    @0
    wral
    #
    vu
    @2
    wral
    #
    @30
    cn0
    wcel
    #
    @40
    @34
    @59
    vw
    vu
    @2
    @16
    @53
    wceq
    #
    @33
    @58
    vx
    vy
    @0
    @8
    @51
    wceq
    #
    @62
    @33
    @58
    wb
    @63
    @62
    wa
    #
    @32
    @57
    wph
    wch
    @64
    @18
    @55
    @31
    @56
    @63
    @62
    @9
    @52
    @17
    @54
    @8
    @51
    chash
    fveq2
    #
    @16
    @53
    chash
    fveq2
    eqeqan12d
    @63
    @31
    @56
    wb
    @62
    @63
    @9
    @52
    @30
    @65
    eqeq1d
    adantr
    anbi12d
    wrd2ind.2
    imbi12d
    ancoms
    cbvraldva
    cbvralv
    @61
    @60
    @40
    @61
    @60
    wa
    #
    @39
    vw
    vx
    @2
    @0
    @66
    @47
    @38
    wph
    @66
    @47
    @38
    wa
    #
    wa
    #
    wph
    wph
    vw
    @16
    cc0
    @17
    c1
    cmin
    co
    #
    cop
    csubstr
    co
    #
    @16
    clsw
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    wsbc
    #
    vx
    @8
    cc0
    @9
    c1
    cmin
    co
    #
    cop
    csubstr
    co
    #
    @8
    clsw
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    wsbc
    #
    @68
    @70
    @2
    wcel
    #
    @71
    cY
    wcel
    #
    wa
    #
    @76
    @0
    wcel
    #
    @77
    cX
    wcel
    #
    wa
    wa
    #
    wph
    vw
    @70
    wsbc
    #
    vx
    @76
    wsbc
    #
    @76
    chash
    cfv
    #
    @70
    chash
    cfv
    #
    wceq
    #
    wa
    #
    @80
    @61
    @67
    @86
    @60
    @61
    @67
    wa
    #
    @83
    @84
    @85
    @93
    @81
    @82
    @47
    @81
    @61
    @38
    @45
    @81
    @46
    cY
    @16
    cc0
    @69
    swrdcl
    adantr
    #
    ad2antrl
    @93
    @45
    @16
    c0
    wne
    #
    @82
    @61
    @45
    @46
    @38
    simprll
    #
    @93
    @95
    c1
    @17
    cle
    wbr
    #
    @93
    @17
    @67
    @61
    @17
    cn
    wcel
    #
    @38
    @61
    @98
    wi
    #
    @47
    @37
    @18
    @99
    @37
    @18
    @36
    @17
    wceq
    #
    @99
    @9
    @36
    @17
    eqeq1
    @61
    @98
    @100
    @36
    cn
    wcel
    #
    @30
    nn0p1nn
    #
    @98
    @101
    wb
    @17
    @36
    @17
    @36
    cn
    eleq1
    eqcoms
    syl5ibr
    syl6bi
    impcom
    adantl
    impcom
    nnge1d
    @93
    @45
    @95
    @97
    wb
    @96
    cY
    @16
    wrdlenge1n0
    syl
    mpbird
    cY
    @16
    lswcl
    syl2anc
    jca
    @47
    @84
    @61
    @38
    @46
    @84
    @45
    cX
    @8
    cc0
    @75
    swrdcl
    adantl
    #
    ad2antrl
    @93
    @46
    @8
    c0
    wne
    #
    @85
    @61
    @45
    @46
    @38
    simprlr
    #
    @93
    @104
    c1
    @9
    cle
    wbr
    #
    @93
    @9
    @67
    @61
    @9
    cn
    wcel
    #
    @37
    @61
    @107
    wi
    @47
    @18
    @61
    @107
    @37
    @101
    @102
    @9
    @36
    cn
    eleq1
    syl5ibr
    ad2antll
    impcom
    nnge1d
    @93
    @46
    @104
    @106
    wb
    @105
    cX
    @8
    wrdlenge1n0
    syl
    mpbird
    cX
    @8
    lswcl
    syl2anc
    jca32
    adantlr
    @68
    @88
    @91
    @68
    @47
    @60
    @91
    @89
    @30
    wceq
    #
    wa
    #
    @88
    @66
    @47
    @38
    simprl
    @61
    @60
    @67
    simplr
    @68
    @91
    @108
    @68
    @75
    @69
    @89
    @90
    @68
    @9
    @17
    c1
    cmin
    @66
    @47
    @18
    @37
    simprrl
    oveq1d
    @68
    @46
    @75
    cc0
    @9
    cfz
    co
    #
    wcel
    #
    @89
    @75
    wceq
    @66
    @45
    @46
    @38
    simprlr
    #
    @68
    cc0
    @9
    cfzo
    co
    #
    @110
    @75
    cc0
    @9
    fzossfz
    @68
    @107
    @75
    @113
    wcel
    @68
    @9
    @36
    cn
    @66
    @47
    @18
    @37
    simprrr
    #
    @61
    @101
    @60
    @67
    @102
    ad2antrr
    #
    eqeltrd
    #
    @9
    fzo0end
    syl
    sseldi
    #
    cX
    @8
    @75
    swrd0len
    syl2anc
    #
    @68
    @45
    @69
    cc0
    @17
    cfz
    co
    #
    wcel
    #
    @90
    @69
    wceq
    @66
    @45
    @46
    @38
    simprll
    #
    @68
    @120
    @111
    @117
    @38
    @120
    @111
    wb
    #
    @66
    @47
    @18
    @122
    @37
    @122
    @17
    @9
    @17
    @9
    wceq
    @69
    @75
    @119
    @110
    @17
    @9
    c1
    cmin
    oveq1
    @17
    @9
    cc0
    cfz
    oveq2
    eleq12d
    eqcoms
    adantr
    ad2antll
    mpbird
    cY
    @16
    @69
    swrd0len
    syl2anc
    3eqtr4d
    #
    @68
    @89
    @75
    @36
    c1
    cmin
    co
    #
    @30
    @118
    @68
    @9
    @36
    c1
    cmin
    @114
    oveq1d
    @68
    @30
    cc
    wcel
    #
    c1
    cc
    wcel
    @124
    @30
    wceq
    @61
    @125
    @60
    @67
    @30
    nn0cn
    ad2antrr
    ax-1cn
    @30
    c1
    pncan
    sylancl
    3eqtrd
    jca
    @47
    @59
    @109
    @88
    wi
    #
    vu
    @70
    @2
    @94
    @47
    @53
    @70
    wceq
    #
    wa
    #
    @58
    @126
    vy
    @76
    @0
    @47
    @84
    @127
    @103
    adantr
    @128
    @51
    @76
    wceq
    #
    wa
    #
    @57
    @109
    wch
    @88
    @130
    @55
    @91
    @56
    @108
    @128
    @129
    @55
    @91
    wb
    #
    @127
    @129
    @131
    wi
    @47
    @129
    @127
    @131
    @129
    @127
    @52
    @89
    @54
    @90
    @51
    @76
    chash
    fveq2
    #
    @53
    @70
    chash
    fveq2
    #
    eqeqan12d
    expcom
    adantl
    imp
    @129
    @56
    @108
    wb
    @128
    @129
    @52
    @89
    @30
    @132
    eqeq1d
    adantl
    anbi12d
    @130
    wch
    wph
    vw
    @53
    wsbc
    #
    vx
    @51
    wsbc
    #
    @134
    vx
    @76
    wsbc
    #
    @88
    wch
    @135
    wb
    @130
    @135
    wch
    wph
    wch
    vx
    vw
    @51
    @53
    vy
    vex
    #
    vu
    vex
    #
    wrd2ind.2
    sbc2ie
    bicomi
    a1i
    @130
    @134
    vx
    @51
    @76
    @128
    @129
    simpr
    sbceq1d
    @128
    @136
    @88
    wb
    #
    @129
    @127
    @139
    @47
    @127
    @134
    @87
    vx
    @76
    wph
    vw
    @53
    @70
    dfsbcq
    sbcbidv
    adantl
    adantr
    3bitrd
    imbi12d
    rspcdv
    rspcimdv
    syl3c
    @123
    jca
    wph
    vx
    @51
    wsbc
    #
    vw
    @53
    wsbc
    #
    @55
    wa
    #
    wph
    vx
    @51
    vz
    cv
    #
    cs1
    #
    cconcat
    co
    #
    wsbc
    #
    vw
    @53
    vs
    cv
    #
    cs1
    #
    cconcat
    co
    #
    wsbc
    #
    wi
    @87
    vx
    @51
    wsbc
    #
    @52
    @90
    wceq
    #
    wa
    #
    @146
    vw
    @70
    @148
    cconcat
    co
    #
    wsbc
    #
    wi
    #
    @153
    @74
    vx
    @145
    wsbc
    #
    wi
    #
    @92
    @80
    wi
    @92
    @74
    vx
    @76
    @144
    cconcat
    co
    #
    wsbc
    #
    wi
    vu
    vs
    vy
    vz
    @70
    @71
    @76
    @77
    @2
    cY
    @0
    cX
    @127
    @142
    @153
    @150
    @155
    @127
    @141
    @151
    @55
    @152
    @127
    @141
    @140
    vw
    @70
    wsbc
    @151
    @140
    vw
    @53
    @70
    dfsbcq
    wph
    vw
    vx
    @70
    @51
    sbccom
    syl6bb
    @127
    @54
    @90
    @52
    @133
    eqeq2d
    anbi12d
    @127
    @146
    vw
    @149
    @154
    @53
    @70
    @148
    cconcat
    oveq1
    sbceq1d
    imbi12d
    @147
    @71
    wceq
    #
    @156
    @153
    @146
    vw
    @73
    wsbc
    #
    wi
    @158
    @161
    @155
    @162
    @153
    @161
    @146
    vw
    @154
    @73
    @161
    @148
    @72
    @70
    cconcat
    @147
    @71
    s1eq
    oveq2d
    sbceq1d
    imbi2d
    @161
    @162
    @157
    @153
    @162
    @157
    wb
    @161
    wph
    vw
    vx
    @73
    @145
    sbccom
    a1i
    imbi2d
    bitrd
    @129
    @153
    @92
    @157
    @160
    @129
    @151
    @88
    @152
    @91
    @87
    vx
    @51
    @76
    dfsbcq
    @129
    @52
    @89
    @90
    @132
    eqeq1d
    anbi12d
    @129
    @74
    vx
    @145
    @159
    @51
    @76
    @144
    cconcat
    oveq1
    sbceq1d
    imbi12d
    @143
    @77
    wceq
    #
    @160
    @80
    @92
    @163
    @74
    vx
    @159
    @79
    @163
    @144
    @78
    @76
    cconcat
    @143
    @77
    s1eq
    oveq2d
    sbceq1d
    imbi2d
    @53
    @2
    wcel
    @147
    cY
    wcel
    wa
    #
    @51
    @0
    wcel
    @143
    cX
    wcel
    wa
    #
    wa
    #
    @141
    @55
    @150
    @166
    @55
    @141
    @150
    @166
    @55
    @141
    @150
    wi
    @166
    @55
    wa
    #
    wch
    wth
    @141
    @150
    @167
    @165
    @164
    @55
    wch
    wth
    wi
    @164
    @165
    @55
    simplr
    @164
    @165
    @55
    simpll
    @166
    @55
    simpr
    wrd2ind.7
    syl3anc
    wph
    wch
    vw
    vx
    @53
    @51
    @138
    @137
    @63
    @62
    wph
    wch
    wb
    wrd2ind.2
    ancoms
    sbc2ie
    wph
    wth
    vw
    vx
    @149
    @145
    @53
    @148
    cconcat
    ovex
    @51
    @144
    cconcat
    ovex
    @8
    @145
    wceq
    @16
    @149
    wceq
    wph
    wth
    wb
    wrd2ind.3
    ancoms
    sbc2ie
    3imtr4g
    ex
    com23
    impd
    vtocl4ga
    sylc
    @68
    @16
    @73
    wceq
    #
    @8
    @79
    wceq
    #
    wph
    @80
    wb
    @68
    @45
    @95
    @168
    @121
    @68
    @98
    @95
    @68
    @17
    @36
    cn
    @38
    @17
    @36
    wceq
    @66
    @47
    @9
    @17
    @36
    eqtr2
    ad2antll
    @115
    eqeltrd
    @68
    @16
    cfn
    wcel
    #
    @98
    @95
    wb
    @47
    @170
    @66
    @38
    @45
    @170
    @46
    cY
    @16
    wrdfin
    adantr
    ad2antrl
    @16
    hashnncl
    syl
    mpbid
    @45
    @95
    wa
    @73
    @16
    cY
    @16
    swrdccatwrd
    eqcomd
    syl2anc
    @68
    @46
    @104
    @169
    @112
    @68
    @107
    @104
    @116
    @68
    @8
    cfn
    wcel
    #
    @107
    @104
    wb
    @47
    @171
    @66
    @38
    @46
    @171
    @45
    cX
    @8
    wrdfin
    adantl
    ad2antrl
    @8
    hashnncl
    syl
    mpbid
    @46
    @104
    wa
    @79
    @8
    cX
    @8
    swrdccatwrd
    eqcomd
    syl2anc
    @168
    wph
    @74
    @169
    @80
    wph
    vw
    @73
    sbceq1a
    @74
    vx
    @79
    sbceq1a
    sylan9bb
    syl2anc
    mpbird
    expr
    ralrimivva
    ex
    syl5bi
    nn0ind
    syl
    3ad2ant1
    @3
    @1
    @22
    @14
    wi
    @6
    @21
    @14
    vw
    cB
    @2
    @16
    cB
    wceq
    #
    @20
    @13
    vx
    @0
    @172
    @19
    @12
    wph
    wrh
    @172
    @18
    @10
    @11
    @172
    @17
    @5
    @9
    @16
    cB
    chash
    fveq2
    eqeq2d
    anbi1d
    wrd2ind.5
    imbi12d
    ralbidv
    rspcv
    3ad2ant2
    mpd
    @7
    @4
    eqidd
    @1
    @6
    @14
    @15
    wta
    wi
    wi
    #
    @3
    @1
    @6
    @173
    @1
    @6
    @15
    @14
    wta
    @1
    @6
    @15
    @14
    wta
    wi
    @1
    @14
    @6
    @15
    wa
    #
    wta
    @13
    @174
    wta
    wi
    vx
    cA
    @0
    @8
    cA
    wceq
    #
    @12
    @174
    wrh
    wta
    @175
    @10
    @6
    @11
    @15
    @175
    @9
    @4
    @5
    @8
    cA
    chash
    fveq2
    #
    eqeq1d
    @175
    @9
    @4
    @4
    @176
    eqeq1d
    anbi12d
    wrd2ind.4
    imbi12d
    rspcv
    com23
    expd
    com34
    imp
    3adant2
    mp2d
end
