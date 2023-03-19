include "con0.mm"
include "c2o.mm"
include "cdif.mm"
include "wcel.mm"
include "c1o.mm"
include "wa.mm"
include "coe.mm"
include "co.mm"
include "comu.mm"
include "coa.mm"
include "wceq.mm"
include "w3a.mm"
include "wb.mm"
include "wss.mm"
include "csuc.mm"
include "eldifi.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "oecl.mm"
include "syl2anc.mm"
include "om1.mm"
include "syl.mm"
include "c0.mm"
include "csn.mm"
include "df1o2.mm"
include "wne.mm"
include "dif1o.mm"
include "simprbi.mm"
include "ad2antll.mm"
include "onelon.mm"
include "on0eln0.mm"
include "mpbird.mm"
include "snssd.mm"
include "syl5eqss.mm"
include "wi.mm"
include "1on.mm"
include "a1i.mm"
include "omwordi.mm"
include "syl3anc.mm"
include "mpd.mm"
include "eqsstr3d.mm"
include "omcl.mm"
include "simplrl.mm"
include "oaword1.mm"
include "simplrr.mm"
include "sseqtrd.mm"
include "sstrd.mm"
include "oeeulem.mm"
include "simp3d.mm"
include "simp1d.mm"
include "suceloni.mm"
include "ontr2.mm"
include "mp2and.mm"
include "simplll.mm"
include "oeord.mm"
include "onsssuc.mm"
include "simp2d.mm"
include "word.mm"
include "eloni.mm"
include "ordsucss.mm"
include "sylc.mm"
include "dif20el.mm"
include "oen0.mm"
include "syl21anc.mm"
include "omword.mm"
include "syl31anc.mm"
include "mpbid.mm"
include "oaord.mm"
include "eqeltrrd.mm"
include "odi.mm"
include "oa1suc.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "oesuc.mm"
include "ad2antrl.mm"
include "eqssd.mm"
include "jca.mm"
include "eqeltrd.mm"
include "simprr.mm"
include "suceq.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "omord2.mm"
include "wn.mm"
include "eqsstrd.mm"
include "adantl.mm"
include "ontri1.mm"
include "om0.mm"
include "oveq1d.mm"
include "oa0r.mm"
include "eqtrd.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "sylibd.mm"
include "necon3bd.mm"
include "sylanbrc.mm"
include "impbida.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "anass.mm"
include "syl6bb.mm"
include "3anass.mm"
include "eleq2d.mm"
include "eqeq1d.mm"
include "3anbi23d.mm"
include "syl5bbr.mm"
include "ne0i.mm"
include "cv.mm"
include "cop.mm"
include "wrex.mm"
include "weu.mm"
include "omeu.mm"
include "cio.mm"
include "weq.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "opeq2.mm"
include "cbvrex2v.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "syl5bb.mm"
include "cbviotav.mm"
include "eqtri.mm"
include "opiota.mm"
include "sylan9bbr.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "3an4anass.mm"
include "3bitr4g.mm"

theorem oeeui
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vd: setvar d
  let ve: setvar e
  assume oeeu.1: |- X = U. |^| { x e. On | B e. ( A ^o x ) }
  assume oeeu.2: |- P = ( iota w E. y e. On E. z e. ( A ^o X ) ( w = <. y , z >. /\ ( ( ( A ^o X ) .o y ) +o z ) = B ) )
  assume oeeu.3: |- Y = ( 1st ` P )
  assume oeeu.4: |- Z = ( 2nd ` P )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint a d
  disjoint a e
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint d e
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint e w
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint A e
  disjoint B a
  disjoint B d
  disjoint B e
  disjoint D a
  disjoint D d
  disjoint D e
  disjoint E a
  disjoint E d
  disjoint E e
  disjoint X a
  disjoint X d
  disjoint X e
  assert |- ( ( A e. ( On \ 2o ) /\ B e. ( On \ 1o ) ) -> ( ( ( C e. On /\ D e. ( A \ 1o ) /\ E e. ( A ^o C ) ) /\ ( ( ( A ^o C ) .o D ) +o E ) = B ) <-> ( C = X /\ D = Y /\ E = Z ) ) )

  proof
    cA
    con0
    c2o
    cdif
    wcel
    #
    cB
    con0
    c1o
    cdif
    wcel
    #
    wa
    #
    cC
    con0
    wcel
    #
    cD
    cA
    c1o
    cdif
    wcel
    #
    wa
    #
    cE
    cA
    cC
    coe
    co
    #
    wcel
    #
    @6
    cD
    comu
    co
    #
    cE
    coa
    co
    #
    cB
    wceq
    #
    wa
    #
    wa
    #
    cC
    cX
    wceq
    #
    cD
    cY
    wceq
    #
    cE
    cZ
    wceq
    #
    wa
    #
    wa
    #
    @3
    @4
    @7
    w3a
    @10
    wa
    @13
    @14
    @15
    w3a
    @2
    @12
    @13
    cD
    con0
    wcel
    #
    @11
    wa
    #
    wa
    #
    @17
    @2
    @12
    @13
    @18
    wa
    #
    @11
    wa
    @20
    @2
    @11
    @5
    @21
    @2
    @11
    @5
    @21
    wb
    @2
    @11
    wa
    #
    @5
    @21
    @22
    @5
    wa
    #
    @13
    @18
    @23
    cC
    cX
    @23
    cC
    cX
    wss
    #
    cC
    cX
    csuc
    #
    wcel
    #
    @23
    @26
    @6
    cA
    @25
    coe
    co
    #
    wcel
    #
    @23
    @6
    cB
    wss
    #
    cB
    @27
    wcel
    #
    @28
    @23
    @6
    @8
    cB
    @23
    @6
    @6
    c1o
    comu
    co
    #
    @8
    @23
    @6
    con0
    wcel
    #
    @31
    @6
    wceq
    @23
    cA
    con0
    wcel
    #
    @3
    @32
    @2
    @33
    @11
    @5
    @0
    @33
    @1
    cA
    con0
    c2o
    eldifi
    adantr
    #
    ad2antrr
    #
    @22
    @3
    @4
    simprl
    #
    cA
    cC
    oecl
    #
    syl2anc
    #
    @6
    om1
    syl
    #
    @23
    c1o
    cD
    wss
    #
    @31
    @8
    wss
    #
    @23
    c1o
    c0
    csn
    cD
    df1o2
    @23
    c0
    cD
    @23
    c0
    cD
    wcel
    #
    cD
    c0
    wne
    #
    @4
    @43
    @22
    @3
    @4
    cD
    cA
    wcel
    #
    @43
    cD
    cA
    dif1o
    #
    simprbi
    ad2antll
    @23
    @18
    @42
    @43
    wb
    @23
    @33
    @44
    @18
    @35
    @4
    @44
    @22
    @3
    cD
    cA
    c1o
    eldifi
    ad2antll
    #
    cA
    cD
    onelon
    syl2anc
    #
    cD
    on0eln0
    syl
    mpbird
    snssd
    syl5eqss
    @23
    c1o
    con0
    wcel
    #
    @18
    @32
    @40
    @41
    wi
    @48
    @23
    1on
    a1i
    #
    @47
    @38
    c1o
    cD
    @6
    omwordi
    syl3anc
    mpd
    eqsstr3d
    @23
    @8
    @9
    cB
    @23
    @8
    con0
    wcel
    #
    cE
    con0
    wcel
    #
    @8
    @9
    wss
    #
    @23
    @32
    @18
    @50
    @38
    @47
    @6
    cD
    omcl
    #
    syl2anc
    #
    @23
    @32
    @7
    @51
    @38
    @2
    @7
    @10
    @5
    simplrl
    #
    @6
    cE
    onelon
    #
    syl2anc
    #
    @8
    cE
    oaword1
    #
    syl2anc
    @2
    @7
    @10
    @5
    simplrr
    #
    sseqtrd
    sstrd
    @2
    @30
    @11
    @5
    @2
    cX
    con0
    wcel
    #
    cA
    cX
    coe
    co
    #
    cB
    wss
    #
    @30
    vx
    cA
    cB
    cX
    oeeu.1
    oeeulem
    #
    simp3d
    #
    ad2antrr
    @23
    @32
    @27
    con0
    wcel
    #
    @29
    @30
    wa
    @28
    wi
    @38
    @23
    @33
    @25
    con0
    wcel
    #
    @65
    @35
    @23
    @60
    @66
    @2
    @60
    @11
    @5
    @2
    @60
    @62
    @30
    @63
    simp1d
    #
    ad2antrr
    #
    cX
    suceloni
    syl
    #
    cA
    @25
    oecl
    syl2anc
    @6
    cB
    @27
    ontr2
    syl2anc
    mp2and
    @23
    @3
    @66
    @0
    @26
    @28
    wb
    @36
    @69
    @0
    @1
    @11
    @5
    simplll
    #
    cC
    @25
    cA
    oeord
    syl3anc
    mpbird
    @23
    @3
    @60
    @24
    @26
    wb
    @36
    @68
    cC
    cX
    onsssuc
    syl2anc
    mpbird
    @23
    cX
    cC
    wss
    #
    cX
    cC
    csuc
    #
    wcel
    #
    @23
    @73
    @61
    cA
    @72
    coe
    co
    #
    wcel
    #
    @23
    @62
    cB
    @74
    wcel
    #
    @75
    @2
    @62
    @11
    @5
    @2
    @60
    @62
    @30
    @63
    simp2d
    #
    ad2antrr
    @23
    cB
    @6
    cA
    comu
    co
    #
    @74
    @23
    @6
    cD
    csuc
    #
    comu
    co
    #
    @78
    cB
    @23
    @79
    cA
    wss
    #
    @80
    @78
    wss
    #
    @23
    cA
    word
    #
    @44
    @81
    @23
    @33
    @83
    @35
    cA
    eloni
    syl
    @46
    cD
    cA
    ordsucss
    sylc
    @23
    @79
    con0
    wcel
    #
    @33
    @32
    c0
    @6
    wcel
    #
    @81
    @82
    wb
    @23
    @18
    @84
    @47
    cD
    suceloni
    syl
    @35
    @38
    @23
    @33
    @3
    c0
    cA
    wcel
    #
    @85
    @35
    @36
    @23
    @0
    @86
    @70
    cA
    dif20el
    #
    syl
    cA
    cC
    oen0
    #
    syl21anc
    @79
    cA
    @6
    omword
    syl31anc
    mpbid
    @23
    cB
    @8
    @6
    coa
    co
    #
    @80
    @23
    @9
    cB
    @89
    @59
    @23
    @7
    @9
    @89
    wcel
    #
    @55
    @23
    @51
    @32
    @50
    @7
    @90
    wb
    @57
    @38
    @54
    cE
    @6
    @8
    oaord
    syl3anc
    mpbid
    eqeltrrd
    @23
    @6
    cD
    c1o
    coa
    co
    #
    comu
    co
    #
    @8
    @31
    coa
    co
    #
    @80
    @89
    @23
    @32
    @18
    @48
    @92
    @93
    wceq
    @38
    @47
    @49
    @6
    cD
    c1o
    odi
    syl3anc
    @23
    @91
    @79
    @6
    comu
    @23
    @18
    @91
    @79
    wceq
    @47
    cD
    oa1suc
    syl
    oveq2d
    @23
    @31
    @6
    @8
    coa
    @39
    oveq2d
    3eqtr3d
    eleqtrrd
    sseldd
    @23
    @33
    @3
    @74
    @78
    wceq
    #
    @35
    @36
    cA
    cC
    oesuc
    #
    syl2anc
    eleqtrrd
    @23
    @61
    con0
    wcel
    #
    @74
    con0
    wcel
    #
    @62
    @76
    wa
    @75
    wi
    @23
    @33
    @60
    @96
    @35
    @68
    cA
    cX
    oecl
    #
    syl2anc
    @23
    @33
    @72
    con0
    wcel
    #
    @97
    @35
    @3
    @99
    @22
    @4
    cC
    suceloni
    ad2antrl
    #
    cA
    @72
    oecl
    syl2anc
    @61
    cB
    @74
    ontr2
    syl2anc
    mp2and
    @23
    @60
    @99
    @0
    @73
    @75
    wb
    @68
    @100
    @70
    cX
    @72
    cA
    oeord
    syl3anc
    mpbird
    @23
    @60
    @3
    @71
    @73
    wb
    @68
    @36
    cX
    cC
    onsssuc
    syl2anc
    mpbird
    eqssd
    @47
    jca
    @22
    @21
    wa
    #
    @3
    @4
    @101
    cC
    cX
    con0
    @22
    @13
    @18
    simprl
    #
    @2
    @60
    @11
    @21
    @67
    ad2antrr
    eqeltrd
    #
    @101
    @44
    @43
    @4
    @101
    @44
    @8
    @78
    wcel
    #
    @101
    @8
    cB
    wss
    #
    cB
    @78
    wcel
    #
    @104
    @101
    @8
    @9
    cB
    @101
    @50
    @51
    @52
    @101
    @32
    @18
    @50
    @101
    @33
    @3
    @32
    @2
    @33
    @11
    @21
    @34
    ad2antrr
    #
    @103
    @37
    syl2anc
    #
    @22
    @13
    @18
    simprr
    #
    @53
    syl2anc
    #
    @101
    @32
    @7
    @51
    @108
    @2
    @7
    @10
    @21
    simplrl
    #
    @56
    syl2anc
    #
    @58
    syl2anc
    @2
    @7
    @10
    @21
    simplrr
    #
    sseqtrd
    @101
    cB
    @27
    @78
    @2
    @30
    @11
    @21
    @64
    ad2antrr
    @101
    @74
    @27
    @78
    @101
    @72
    @25
    cA
    coe
    @13
    @72
    @25
    wceq
    @22
    @18
    cC
    cX
    suceq
    ad2antrl
    oveq2d
    @101
    @33
    @3
    @94
    @107
    @103
    @95
    syl2anc
    eqtr3d
    eleqtrd
    @101
    @50
    @78
    con0
    wcel
    #
    @105
    @106
    wa
    @104
    wi
    @110
    @101
    @32
    @33
    @114
    @108
    @107
    @6
    cA
    omcl
    syl2anc
    @8
    cB
    @78
    ontr2
    syl2anc
    mp2and
    @101
    @18
    @33
    @32
    @85
    @44
    @104
    wb
    @109
    @107
    @108
    @101
    @33
    @3
    @86
    @85
    @107
    @103
    @2
    @86
    @11
    @21
    @0
    @86
    @1
    @87
    adantr
    #
    ad2antrr
    @88
    syl21anc
    cD
    cA
    @6
    omord2
    syl31anc
    mpbird
    @101
    cB
    @6
    wcel
    #
    wn
    #
    @43
    @101
    @29
    @117
    @101
    @6
    @61
    cB
    @101
    cC
    cX
    cA
    coe
    @102
    oveq2d
    @2
    @62
    @11
    @21
    @77
    ad2antrr
    eqsstrd
    @101
    @32
    cB
    con0
    wcel
    #
    @29
    @117
    wb
    @108
    @2
    @118
    @11
    @21
    @1
    @118
    @0
    cB
    con0
    c1o
    eldifi
    adantl
    #
    ad2antrr
    @6
    cB
    ontri1
    syl2anc
    mpbid
    @101
    @116
    cD
    c0
    @101
    cD
    c0
    wceq
    #
    @9
    @6
    wcel
    #
    @116
    @101
    @121
    @120
    @6
    c0
    comu
    co
    #
    cE
    coa
    co
    #
    @6
    wcel
    @101
    @123
    cE
    @6
    @101
    @123
    c0
    cE
    coa
    co
    #
    cE
    @101
    @122
    c0
    cE
    coa
    @101
    @32
    @122
    c0
    wceq
    @108
    @6
    om0
    syl
    oveq1d
    @101
    @51
    @124
    cE
    wceq
    @112
    cE
    oa0r
    syl
    eqtrd
    @111
    eqeltrd
    @120
    @9
    @123
    @6
    @120
    @8
    @122
    cE
    coa
    cD
    c0
    @6
    comu
    oveq2
    oveq1d
    eleq1d
    syl5ibrcom
    @101
    @9
    cB
    @6
    @113
    eleq1d
    sylibd
    necon3bd
    mpd
    @45
    sylanbrc
    jca
    impbida
    ex
    pm5.32rd
    @13
    @18
    @11
    anass
    syl6bb
    @2
    @13
    @19
    @16
    @13
    @19
    @18
    cE
    @61
    wcel
    #
    @61
    cD
    comu
    co
    #
    cE
    coa
    co
    #
    cB
    wceq
    #
    w3a
    #
    @2
    @16
    @19
    @18
    @7
    @10
    w3a
    @13
    @129
    @18
    @7
    @10
    3anass
    @13
    @7
    @125
    @10
    @128
    @18
    @13
    @6
    @61
    cE
    cC
    cX
    cA
    coe
    oveq2
    #
    eleq2d
    @13
    @9
    @127
    cB
    @13
    @8
    @126
    cE
    coa
    @13
    @6
    @61
    cD
    comu
    @130
    oveq1d
    oveq1d
    eqeq1d
    3anbi23d
    syl5bbr
    @2
    @96
    @118
    @61
    c0
    wne
    #
    @129
    @16
    wb
    #
    @2
    @33
    @60
    @96
    @34
    @67
    @98
    syl2anc
    @119
    @2
    c0
    @61
    wcel
    #
    @131
    @2
    @33
    @60
    @86
    @133
    @34
    @67
    @115
    cA
    cX
    oen0
    syl21anc
    @61
    c0
    ne0i
    syl
    @96
    @118
    @131
    w3a
    va
    cv
    #
    vd
    cv
    #
    ve
    cv
    #
    cop
    #
    wceq
    #
    @61
    @135
    comu
    co
    #
    @136
    coa
    co
    #
    cB
    wceq
    #
    wa
    #
    ve
    @61
    wrex
    vd
    con0
    wrex
    #
    va
    weu
    @132
    vd
    ve
    va
    @61
    cB
    omeu
    @141
    @126
    @136
    coa
    co
    #
    cB
    wceq
    @128
    vd
    ve
    va
    con0
    @61
    cD
    cE
    cP
    cY
    cZ
    cP
    vw
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    @61
    @146
    comu
    co
    #
    @147
    coa
    co
    #
    cB
    wceq
    #
    wa
    #
    vz
    @61
    wrex
    vy
    con0
    wrex
    #
    vw
    cio
    @143
    va
    cio
    oeeu.2
    @154
    @143
    vw
    va
    @154
    @145
    @137
    wceq
    #
    @141
    wa
    #
    ve
    @61
    wrex
    vd
    con0
    wrex
    vw
    va
    weq
    #
    @143
    @153
    @156
    @145
    @135
    @147
    cop
    #
    wceq
    #
    @139
    @147
    coa
    co
    #
    cB
    wceq
    #
    wa
    vy
    vz
    vd
    ve
    con0
    @61
    vy
    vd
    weq
    #
    @149
    @159
    @152
    @161
    @162
    @148
    @158
    @145
    @146
    @135
    @147
    opeq1
    eqeq2d
    @162
    @151
    @160
    cB
    @162
    @150
    @139
    @147
    coa
    @146
    @135
    @61
    comu
    oveq2
    oveq1d
    eqeq1d
    anbi12d
    vz
    ve
    weq
    #
    @159
    @155
    @161
    @141
    @163
    @158
    @137
    @145
    @147
    @136
    @135
    opeq2
    eqeq2d
    @163
    @160
    @140
    cB
    @147
    @136
    @139
    coa
    oveq2
    eqeq1d
    anbi12d
    cbvrex2v
    @157
    @156
    @142
    vd
    ve
    con0
    @61
    @157
    @155
    @138
    @141
    @145
    @134
    @137
    eqeq1
    anbi1d
    2rexbidv
    syl5bb
    cbviotav
    eqtri
    oeeu.3
    oeeu.4
    @135
    cD
    wceq
    #
    @140
    @144
    cB
    @164
    @139
    @126
    @136
    coa
    @135
    cD
    @61
    comu
    oveq2
    oveq1d
    eqeq1d
    @136
    cE
    wceq
    @144
    @127
    cB
    @136
    cE
    @126
    coa
    oveq2
    eqeq1d
    opiota
    syl
    syl3anc
    sylan9bbr
    pm5.32da
    bitrd
    @3
    @4
    @7
    @10
    3an4anass
    @13
    @14
    @15
    3anass
    3bitr4g
end
