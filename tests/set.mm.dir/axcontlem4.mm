include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wo.mm"
include "simplr1.mm"
include "wi.mm"
include "wex.mm"
include "n0.mm"
include "idd.mm"
include "ssel.mm"
include "com12.mm"
include "wceq.mm"
include "opeq2.mm"
include "breq2d.mm"
include "rspcv.mm"
include "ralimdv.mm"
include "3anim123d.mm"
include "anim2d.mm"
include "adantr.mm"
include "simplr2.mm"
include "sseldd.mm"
include "simpr3.mm"
include "simp2.mm"
include "breq1.mm"
include "rspccva.mm"
include "syl2an.mm"
include "jca.mm"
include "sselda.mm"
include "sylan.mm"
include "jca32.mm"
include "an4.mm"
include "sylib.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cfz.mm"
include "cc0.mm"
include "cicc.mm"
include "wrex.mm"
include "simpl2r.mm"
include "simpl.mm"
include "ralimi.mm"
include "eqcom.mm"
include "oveq2.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "ralbidv.mm"
include "biimpac.mm"
include "wb.mm"
include "simpl2l.mm"
include "simpl3l.mm"
include "eqeefv.mm"
include "syl2anc.mm"
include "cc.mm"
include "fveecn.mm"
include "simp1r.mm"
include "ad2antrr.mm"
include "sylancom.mm"
include "mulid2.mm"
include "mul02.mm"
include "oveqan12d.mm"
include "addid1.mm"
include "eqtrd.mm"
include "ralbidva.mm"
include "bitr4d.mm"
include "syl5ibr.mm"
include "expdimp.mm"
include "sylan2.mm"
include "necon3d.mm"
include "mpd.mm"
include "simp1l.mm"
include "simp2l.mm"
include "3jca.mm"
include "cle.mm"
include "cr.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "syl.mm"
include "simp2r.mm"
include "letrid.mm"
include "cdiv.mm"
include "simpr.mm"
include "clt.mm"
include "simp2bi.mm"
include "0red.mm"
include "simp3.mm"
include "ne0gt0d.mm"
include "ltletrd.mm"
include "divelunit.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "simp12.mm"
include "simp13.mm"
include "recnd.mm"
include "simpll3.mm"
include "simplr.mm"
include "gt0ne0d.mm"
include "divcl.mm"
include "adantl.mm"
include "ax-1cn.mm"
include "simpr2.mm"
include "subcl.mm"
include "sylancr.mm"
include "simpll.mm"
include "mulcld.mm"
include "adddid.mm"
include "oveq2d.mm"
include "addassd.mm"
include "adddird.mm"
include "subdi.mm"
include "mp3an2.mm"
include "mulid1d.mm"
include "divcan1.mm"
include "simp1.mm"
include "npncan.mm"
include "mp3an1.mm"
include "mulassd.mm"
include "3eqtr3rd.mm"
include "eqtr3d.mm"
include "3eqtr2rd.mm"
include "syl23anc.mm"
include "ralrimiva.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "biimpar.mm"
include "simp112.mm"
include "simp113.mm"
include "simp12r.mm"
include "simp12l.mm"
include "eqtr2d.mm"
include "3eqtrrd.mm"
include "3expa.mm"
include "orim12d.mm"
include "r19.43.mm"
include "syl6ibr.mm"
include "id.mm"
include "eqeqan12d.mm"
include "ralbi.mm"
include "eqeqan12rd.mm"
include "orbi12d.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "3expia.mm"
include "com23.mm"
include "imp.mm"
include "rexlimdvva.mm"
include "simp3l.mm"
include "brbtwn.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "anbi12d.mm"
include "r19.26.mm"
include "2rexbii.mm"
include "reeanv.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "3imtr4d.mm"
include "impd.mm"
include "sylanl2.mm"
include "3adantr2.mm"
include "3exp2.mm"
include "syl6.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "com4l.mm"
include "3impd.mm"
include "imp32.mm"
include "crab.mm"
include "sseq2i.mm"
include "ssrab.mm"
include "sylanbrc.mm"

theorem axcontlem4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let cN: class N
  let cZ: class Z
  let vp: setvar p
  let vb: setvar b
  let vi: setvar i
  let vr: setvar r
  let vt: setvar t
  let vs: setvar s
  assume axcontlem4.1: |- D = { p e. ( EE ` N ) | ( U Btwn <. Z , p >. \/ p Btwn <. Z , U >. ) }

  disjoint A p
  disjoint A x
  disjoint p x
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint p y
  disjoint x y
  disjoint N p
  disjoint N x
  disjoint N y
  disjoint U p
  disjoint U x
  disjoint U y
  disjoint Z p
  disjoint Z x
  disjoint Z y
  disjoint A b
  disjoint A i
  disjoint A r
  disjoint A t
  disjoint b i
  disjoint b r
  disjoint b t
  disjoint b p
  disjoint b x
  disjoint i r
  disjoint i t
  disjoint i p
  disjoint i x
  disjoint r t
  disjoint p r
  disjoint r x
  disjoint p t
  disjoint t x
  disjoint B b
  disjoint B i
  disjoint B r
  disjoint B t
  disjoint b y
  disjoint i y
  disjoint r y
  disjoint t y
  disjoint N b
  disjoint N i
  disjoint N r
  disjoint N s
  disjoint N t
  disjoint b s
  disjoint i s
  disjoint r s
  disjoint s t
  disjoint p s
  disjoint s x
  disjoint s y
  disjoint U b
  disjoint U i
  disjoint U r
  disjoint U s
  disjoint U t
  disjoint Z b
  disjoint Z i
  disjoint Z r
  disjoint Z s
  disjoint Z t
  assert |- ( ( ( N e. NN /\ ( A C_ ( EE ` N ) /\ B C_ ( EE ` N ) /\ A. x e. A A. y e. B x Btwn <. Z , y >. ) ) /\ ( ( Z e. ( EE ` N ) /\ U e. A /\ B =/= (/) ) /\ Z =/= U ) ) -> A C_ D )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wss
    #
    cB
    @1
    wss
    #
    vx
    cv
    #
    cZ
    vy
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    w3a
    #
    wa
    #
    cZ
    @1
    wcel
    #
    cU
    cA
    wcel
    #
    cB
    c0
    wne
    #
    w3a
    #
    cZ
    cU
    wne
    #
    wa
    #
    wa
    @2
    cU
    cZ
    vp
    cv
    #
    cop
    cbtwn
    wbr
    #
    @18
    cZ
    cU
    cop
    cbtwn
    wbr
    #
    wo
    #
    vp
    cA
    wral
    #
    cA
    cD
    wss
    #
    @2
    @3
    @9
    @0
    @17
    simplr1
    @11
    @15
    @16
    @22
    @11
    @12
    @13
    @14
    @16
    @22
    wi
    #
    @14
    @11
    @12
    @13
    @24
    @14
    vb
    cv
    #
    cB
    wcel
    #
    vb
    wex
    @11
    @12
    @13
    @24
    wi
    wi
    #
    wi
    #
    vb
    cB
    n0
    @26
    @28
    vb
    @26
    @11
    @0
    @2
    @25
    @1
    wcel
    #
    @4
    cZ
    @25
    cop
    #
    cbtwn
    wbr
    #
    vx
    cA
    wral
    #
    w3a
    #
    wa
    #
    @27
    @26
    @10
    @33
    @0
    @26
    @2
    @2
    @3
    @29
    @9
    @32
    @26
    @2
    idd
    @3
    @26
    @29
    cB
    @1
    @25
    ssel
    com12
    @26
    @8
    @31
    vx
    cA
    @7
    @31
    vy
    @25
    cB
    @5
    @25
    wceq
    @6
    @30
    @4
    cbtwn
    @5
    @25
    cZ
    opeq2
    breq2d
    rspcv
    ralimdv
    3anim123d
    anim2d
    @34
    @12
    @13
    @16
    @22
    @34
    @12
    @13
    @16
    w3a
    #
    wa
    #
    @21
    vp
    cA
    @36
    @18
    cA
    wcel
    #
    wa
    #
    cU
    @1
    wcel
    #
    @18
    @1
    wcel
    #
    wa
    #
    cU
    @30
    cbtwn
    wbr
    #
    @18
    @30
    cbtwn
    wbr
    #
    wa
    #
    wa
    #
    @21
    @38
    @39
    @42
    wa
    #
    @40
    @43
    wa
    wa
    @45
    @38
    @46
    @40
    @43
    @38
    @39
    @42
    @38
    cA
    @1
    cU
    @36
    @2
    @37
    @2
    @29
    @32
    @0
    @35
    simplr1
    #
    adantr
    @12
    @13
    @16
    @34
    @37
    simplr2
    sseldd
    @36
    @42
    @37
    @34
    @32
    @13
    @42
    @35
    @0
    @2
    @29
    @32
    simpr3
    #
    @12
    @13
    @16
    simp2
    @31
    @42
    vx
    cU
    cA
    @4
    cU
    @30
    cbtwn
    breq1
    rspccva
    syl2an
    adantr
    jca
    @36
    cA
    @1
    @18
    @47
    sselda
    @36
    @32
    @37
    @43
    @34
    @32
    @35
    @48
    adantr
    @31
    @43
    vx
    @18
    cA
    @4
    @18
    @30
    cbtwn
    breq1
    rspccva
    sylan
    jca32
    @39
    @42
    @40
    @43
    an4
    sylib
    @36
    @45
    @21
    wi
    #
    @37
    @34
    @12
    @16
    @49
    @13
    @33
    @0
    @29
    @12
    @16
    wa
    #
    @49
    @2
    @29
    @32
    simp2
    @0
    @29
    wa
    #
    @50
    wa
    @41
    @44
    @21
    @51
    @50
    @41
    @44
    @21
    wi
    @51
    @50
    @41
    w3a
    #
    vi
    cv
    #
    cU
    cfv
    #
    c1
    vt
    cv
    #
    cmin
    co
    #
    @53
    cZ
    cfv
    #
    cmul
    co
    #
    @55
    @53
    @25
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @53
    @18
    cfv
    #
    c1
    vs
    cv
    #
    cmin
    co
    #
    @57
    cmul
    co
    #
    @64
    @59
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    wa
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    vs
    cc0
    c1
    cicc
    co
    #
    wrex
    vt
    @73
    wrex
    #
    @54
    c1
    vr
    cv
    #
    cmin
    co
    #
    @57
    cmul
    co
    #
    @75
    @63
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @71
    wral
    #
    @63
    @77
    @75
    @54
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @71
    wral
    #
    wo
    #
    vr
    @73
    wrex
    #
    @44
    @21
    @52
    @72
    @87
    vt
    vs
    @73
    @73
    @52
    @55
    @73
    wcel
    #
    @64
    @73
    wcel
    #
    wa
    #
    wa
    #
    @72
    @87
    @91
    @72
    wa
    #
    @55
    cc0
    wne
    #
    @87
    @92
    @16
    @93
    @91
    @16
    @72
    @12
    @16
    @51
    @41
    @90
    simpl2r
    adantr
    @92
    @55
    cc0
    cZ
    cU
    @72
    @91
    @62
    vi
    @71
    wral
    #
    @55
    cc0
    wceq
    #
    cZ
    cU
    wceq
    #
    wi
    @70
    @62
    vi
    @71
    @62
    @69
    simpl
    ralimi
    @91
    @94
    @95
    @96
    @94
    @95
    wa
    @96
    @91
    c1
    @57
    cmul
    co
    #
    cc0
    @59
    cmul
    co
    #
    caddc
    co
    #
    @54
    wceq
    #
    vi
    @71
    wral
    #
    @95
    @94
    @101
    @95
    @62
    @100
    vi
    @71
    @62
    @61
    @54
    wceq
    @95
    @100
    @54
    @61
    eqcom
    @95
    @61
    @99
    @54
    @95
    @58
    @97
    @60
    @98
    caddc
    @95
    @56
    c1
    @57
    cmul
    @95
    @56
    c1
    cc0
    cmin
    co
    c1
    @55
    cc0
    c1
    cmin
    oveq2
    1m0e1
    syl6eq
    oveq1d
    @55
    cc0
    @59
    cmul
    oveq1
    oveq12d
    eqeq1d
    syl5bb
    ralbidv
    biimpac
    @91
    @96
    @57
    @54
    wceq
    #
    vi
    @71
    wral
    #
    @101
    @91
    @12
    @39
    @96
    @103
    wb
    @12
    @16
    @51
    @41
    @90
    simpl2l
    #
    @39
    @40
    @51
    @50
    @90
    simpl3l
    cZ
    cU
    vi
    cN
    eqeefv
    syl2anc
    @91
    @100
    @102
    vi
    @71
    @91
    @53
    @71
    wcel
    #
    wa
    #
    @99
    @57
    @54
    @106
    @57
    cc
    wcel
    #
    @59
    cc
    wcel
    #
    @99
    @57
    wceq
    @91
    @12
    @105
    @107
    @104
    cZ
    @53
    cN
    fveecn
    #
    sylan
    @91
    @105
    @29
    @108
    @52
    @29
    @90
    @105
    @0
    @29
    @50
    @41
    simp1r
    #
    ad2antrr
    @25
    @53
    cN
    fveecn
    #
    sylancom
    @107
    @108
    wa
    #
    @99
    @57
    cc0
    caddc
    co
    #
    @57
    @107
    @108
    @97
    @57
    @98
    cc0
    caddc
    @57
    mulid2
    @59
    mul02
    oveqan12d
    @107
    @113
    @57
    wceq
    @108
    @57
    addid1
    adantr
    eqtrd
    syl2anc
    eqeq1d
    ralbidva
    bitr4d
    syl5ibr
    expdimp
    sylan2
    necon3d
    mpd
    @91
    @72
    @93
    @87
    wi
    #
    @52
    @0
    @12
    @29
    w3a
    #
    @90
    @72
    @114
    wi
    @52
    @0
    @12
    @29
    @0
    @29
    @50
    @41
    simp1l
    @51
    @12
    @16
    @41
    simp2l
    #
    @110
    3jca
    @115
    @90
    wa
    @93
    @72
    @87
    @115
    @90
    @93
    @72
    @87
    wi
    @115
    @90
    @93
    w3a
    #
    @87
    @72
    @61
    @77
    @75
    @68
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @71
    wral
    #
    @68
    @77
    @75
    @61
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @71
    wral
    #
    wo
    #
    vr
    @73
    wrex
    #
    @117
    @55
    @64
    cle
    wbr
    #
    @64
    @55
    cle
    wbr
    #
    wo
    #
    @127
    @117
    @55
    @64
    @117
    @88
    @55
    cr
    wcel
    #
    @115
    @88
    @89
    @93
    simp2l
    #
    @88
    @131
    cc0
    @55
    cle
    wbr
    #
    @55
    c1
    cle
    wbr
    #
    cc0
    c1
    @55
    0re
    1re
    elicc2i
    #
    simp1bi
    #
    syl
    #
    @117
    @89
    @64
    cr
    wcel
    #
    @115
    @88
    @89
    @93
    simp2r
    #
    @89
    @138
    cc0
    @64
    cle
    wbr
    #
    @64
    c1
    cle
    wbr
    #
    cc0
    c1
    @64
    0re
    1re
    elicc2i
    #
    simp1bi
    #
    syl
    #
    letrid
    @117
    @130
    @121
    vr
    @73
    wrex
    #
    @125
    vr
    @73
    wrex
    #
    wo
    @127
    @117
    @128
    @145
    @129
    @146
    @117
    @128
    @145
    @117
    @128
    wa
    #
    @55
    @64
    cdiv
    co
    #
    @73
    wcel
    #
    @61
    c1
    @148
    cmin
    co
    #
    @57
    cmul
    co
    #
    @148
    @68
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @71
    wral
    #
    @145
    @147
    @149
    @128
    @117
    @128
    simpr
    #
    @147
    @131
    @133
    @138
    cc0
    @64
    clt
    wbr
    @149
    @128
    wb
    @117
    @131
    @128
    @137
    adantr
    #
    @117
    @133
    @128
    @117
    @88
    @133
    @132
    @88
    @131
    @133
    @134
    @135
    simp2bi
    syl
    #
    adantr
    @117
    @138
    @128
    @144
    adantr
    #
    @147
    cc0
    @55
    @64
    @147
    0red
    @157
    @159
    @117
    cc0
    @55
    clt
    wbr
    #
    @128
    @117
    @55
    @137
    @158
    @115
    @90
    @93
    simp3
    ne0gt0d
    #
    adantr
    @156
    ltletrd
    @55
    @64
    divelunit
    syl22anc
    mpbird
    @147
    @154
    vi
    @71
    @147
    @105
    wa
    #
    @107
    @108
    @55
    cc
    wcel
    #
    @64
    cc
    wcel
    #
    @64
    cc0
    wne
    #
    @154
    @147
    @105
    @12
    @107
    @117
    @12
    @128
    @105
    @0
    @12
    @29
    @90
    @93
    simp12
    ad2antrr
    @109
    sylancom
    @147
    @105
    @29
    @108
    @117
    @29
    @128
    @105
    @0
    @12
    @29
    @90
    @93
    simp13
    ad2antrr
    @111
    sylancom
    @117
    @163
    @128
    @105
    @117
    @88
    @163
    @132
    @88
    @55
    @136
    recnd
    #
    syl
    ad2antrr
    @117
    @164
    @128
    @105
    @117
    @89
    @164
    @139
    @89
    @64
    @143
    recnd
    #
    syl
    ad2antrr
    @162
    @64
    @162
    cc0
    @55
    @64
    @162
    0red
    @117
    @131
    @128
    @105
    @137
    ad2antrr
    #
    @117
    @138
    @128
    @105
    @144
    ad2antrr
    @162
    @55
    @168
    @117
    @133
    @128
    @105
    @158
    ad2antrr
    @115
    @90
    @93
    @128
    @105
    simpll3
    ne0gt0d
    @117
    @128
    @105
    simplr
    ltletrd
    gt0ne0d
    @112
    @163
    @164
    @165
    w3a
    #
    wa
    #
    @153
    @151
    @148
    @66
    cmul
    co
    #
    @148
    @67
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    @151
    @171
    caddc
    co
    #
    @172
    caddc
    co
    @61
    @170
    @152
    @173
    @151
    caddc
    @170
    @148
    @66
    @67
    @169
    @148
    cc
    wcel
    #
    @112
    @55
    @64
    divcl
    #
    adantl
    #
    @170
    @65
    @57
    @170
    c1
    cc
    wcel
    #
    @164
    @65
    cc
    wcel
    ax-1cn
    @112
    @163
    @164
    @165
    simpr2
    #
    c1
    @64
    subcl
    sylancr
    #
    @107
    @108
    @169
    simpll
    #
    mulcld
    #
    @170
    @64
    @59
    @179
    @107
    @108
    @169
    simplr
    #
    mulcld
    #
    adddid
    oveq2d
    @170
    @151
    @171
    @172
    @170
    @150
    @57
    @170
    @178
    @175
    @150
    cc
    wcel
    ax-1cn
    @177
    c1
    @148
    subcl
    sylancr
    #
    @181
    mulcld
    @170
    @148
    @66
    @177
    @182
    mulcld
    @170
    @148
    @67
    @177
    @184
    mulcld
    addassd
    @170
    @174
    @58
    @172
    @60
    caddc
    @170
    @150
    @148
    @65
    cmul
    co
    #
    caddc
    co
    #
    @57
    cmul
    co
    @151
    @186
    @57
    cmul
    co
    #
    caddc
    co
    @58
    @174
    @170
    @150
    @186
    @57
    @185
    @170
    @148
    @65
    @177
    @180
    mulcld
    @181
    adddird
    @170
    @187
    @56
    @57
    cmul
    @169
    @187
    @56
    wceq
    @112
    @169
    @187
    @150
    @148
    @55
    cmin
    co
    #
    caddc
    co
    #
    @56
    @169
    @186
    @189
    @150
    caddc
    @169
    @186
    @148
    c1
    cmul
    co
    #
    @148
    @64
    cmul
    co
    #
    cmin
    co
    #
    @189
    @169
    @175
    @164
    @186
    @193
    wceq
    #
    @176
    @163
    @164
    @165
    simp2
    @175
    @178
    @164
    @194
    ax-1cn
    @148
    c1
    @64
    subdi
    mp3an2
    syl2anc
    @169
    @191
    @148
    @192
    @55
    cmin
    @169
    @148
    @176
    mulid1d
    @55
    @64
    divcan1
    #
    oveq12d
    eqtrd
    oveq2d
    @169
    @175
    @163
    @190
    @56
    wceq
    #
    @176
    @163
    @164
    @165
    simp1
    @178
    @175
    @163
    @196
    ax-1cn
    c1
    @148
    @55
    npncan
    mp3an1
    syl2anc
    eqtrd
    adantl
    oveq1d
    @170
    @188
    @171
    @151
    caddc
    @170
    @148
    @65
    @57
    @177
    @180
    @181
    mulassd
    oveq2d
    3eqtr3rd
    @170
    @192
    @59
    cmul
    co
    @172
    @60
    @170
    @148
    @64
    @59
    @177
    @179
    @183
    mulassd
    @170
    @192
    @55
    @59
    cmul
    @169
    @192
    @55
    wceq
    @112
    @195
    adantl
    oveq1d
    eqtr3d
    oveq12d
    3eqtr2rd
    syl23anc
    ralrimiva
    @121
    @155
    vr
    @148
    @73
    @75
    @148
    wceq
    #
    @120
    @154
    vi
    @71
    @197
    @119
    @153
    @61
    @197
    @77
    @151
    @118
    @152
    caddc
    @197
    @76
    @150
    @57
    cmul
    @75
    @148
    c1
    cmin
    oveq2
    oveq1d
    @75
    @148
    @68
    cmul
    oveq1
    oveq12d
    eqeq2d
    ralbidv
    rspcev
    syl2anc
    ex
    @117
    @129
    @146
    @117
    @129
    wa
    #
    @64
    @55
    cdiv
    co
    #
    @73
    wcel
    #
    @68
    c1
    @199
    cmin
    co
    #
    @57
    cmul
    co
    #
    @199
    @61
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @71
    wral
    #
    @146
    @117
    @200
    @129
    @117
    @138
    @140
    @131
    @160
    @200
    @129
    wb
    @144
    @117
    @89
    @140
    @139
    @89
    @138
    @140
    @141
    @142
    simp2bi
    syl
    @137
    @161
    @64
    @55
    divelunit
    syl22anc
    biimpar
    @198
    @205
    vi
    @71
    @117
    @129
    @105
    @205
    @117
    @129
    @105
    w3a
    #
    @107
    @108
    @164
    @163
    @93
    @205
    @207
    @12
    @105
    @107
    @0
    @12
    @29
    @90
    @93
    @129
    @105
    simp112
    @117
    @129
    @105
    simp3
    #
    @109
    syl2anc
    @207
    @29
    @105
    @108
    @0
    @12
    @29
    @90
    @93
    @129
    @105
    simp113
    @208
    @111
    syl2anc
    @207
    @89
    @164
    @88
    @89
    @115
    @93
    @129
    @105
    simp12r
    @167
    syl
    @207
    @88
    @163
    @88
    @89
    @115
    @93
    @129
    @105
    simp12l
    @166
    syl
    @115
    @90
    @93
    @129
    @105
    simp13
    @112
    @164
    @163
    @93
    w3a
    #
    wa
    #
    @204
    @202
    @199
    @58
    cmul
    co
    #
    @199
    @60
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    @202
    @211
    caddc
    co
    #
    @212
    caddc
    co
    @68
    @210
    @203
    @213
    @202
    caddc
    @210
    @199
    @58
    @60
    @209
    @199
    cc
    wcel
    #
    @112
    @64
    @55
    divcl
    #
    adantl
    #
    @210
    @56
    @57
    @210
    @178
    @163
    @56
    cc
    wcel
    ax-1cn
    @112
    @164
    @163
    @93
    simpr2
    #
    c1
    @55
    subcl
    sylancr
    #
    @107
    @108
    @209
    simpll
    #
    mulcld
    #
    @210
    @55
    @59
    @218
    @107
    @108
    @209
    simplr
    #
    mulcld
    #
    adddid
    oveq2d
    @210
    @202
    @211
    @212
    @210
    @201
    @57
    @210
    @178
    @215
    @201
    cc
    wcel
    ax-1cn
    @217
    c1
    @199
    subcl
    sylancr
    #
    @220
    mulcld
    @210
    @199
    @58
    @217
    @221
    mulcld
    @210
    @199
    @60
    @217
    @223
    mulcld
    addassd
    @210
    @214
    @66
    @212
    @67
    caddc
    @210
    @66
    @201
    @199
    @56
    cmul
    co
    #
    caddc
    co
    #
    @57
    cmul
    co
    #
    @202
    @225
    @57
    cmul
    co
    #
    caddc
    co
    @214
    @209
    @66
    @227
    wceq
    @112
    @209
    @65
    @226
    @57
    cmul
    @209
    @226
    @201
    @199
    @64
    cmin
    co
    #
    caddc
    co
    #
    @65
    @209
    @225
    @229
    @201
    caddc
    @209
    @225
    @199
    c1
    cmul
    co
    #
    @199
    @55
    cmul
    co
    #
    cmin
    co
    #
    @229
    @209
    @215
    @163
    @225
    @233
    wceq
    #
    @216
    @164
    @163
    @93
    simp2
    @215
    @178
    @163
    @234
    ax-1cn
    @199
    c1
    @55
    subdi
    mp3an2
    syl2anc
    @209
    @231
    @199
    @232
    @64
    cmin
    @209
    @199
    @216
    mulid1d
    @64
    @55
    divcan1
    #
    oveq12d
    eqtrd
    oveq2d
    @209
    @215
    @164
    @230
    @65
    wceq
    #
    @216
    @164
    @163
    @93
    simp1
    @178
    @215
    @164
    @236
    ax-1cn
    c1
    @199
    @64
    npncan
    mp3an1
    syl2anc
    eqtr2d
    oveq1d
    adantl
    @210
    @201
    @225
    @57
    @224
    @210
    @199
    @56
    @217
    @219
    mulcld
    @220
    adddird
    @210
    @228
    @211
    @202
    caddc
    @210
    @199
    @56
    @57
    @217
    @219
    @220
    mulassd
    oveq2d
    3eqtrrd
    @210
    @232
    @59
    cmul
    co
    #
    @212
    @67
    @210
    @199
    @55
    @59
    @217
    @218
    @222
    mulassd
    @209
    @237
    @67
    wceq
    @112
    @209
    @232
    @64
    @59
    cmul
    @235
    oveq1d
    adantl
    eqtr3d
    oveq12d
    3eqtr2rd
    syl23anc
    3expa
    ralrimiva
    @125
    @206
    vr
    @199
    @73
    @75
    @199
    wceq
    #
    @124
    @205
    vi
    @71
    @238
    @123
    @204
    @68
    @238
    @77
    @202
    @122
    @203
    caddc
    @238
    @76
    @201
    @57
    cmul
    @75
    @199
    c1
    cmin
    oveq2
    oveq1d
    @75
    @199
    @61
    cmul
    oveq1
    oveq12d
    eqeq2d
    ralbidv
    rspcev
    syl2anc
    ex
    orim12d
    @121
    @125
    vr
    @73
    r19.43
    syl6ibr
    mpd
    @72
    @86
    @126
    vr
    @73
    @72
    @81
    @121
    @85
    @125
    @72
    @80
    @120
    wb
    #
    vi
    @71
    wral
    @81
    @121
    wb
    @70
    @239
    vi
    @71
    @62
    @69
    @54
    @61
    @79
    @119
    @62
    id
    @69
    @78
    @118
    @77
    caddc
    @63
    @68
    @75
    cmul
    oveq2
    oveq2d
    eqeqan12d
    ralimi
    @80
    @120
    vi
    @71
    ralbi
    syl
    @72
    @84
    @124
    wb
    #
    vi
    @71
    wral
    @85
    @125
    wb
    @70
    @240
    vi
    @71
    @69
    @62
    @63
    @68
    @83
    @123
    @69
    id
    @62
    @82
    @122
    @77
    caddc
    @54
    @61
    @75
    cmul
    oveq2
    oveq2d
    eqeqan12rd
    ralimi
    @84
    @124
    vi
    @71
    ralbi
    syl
    orbi12d
    rexbidv
    syl5ibrcom
    3expia
    com23
    sylan
    imp
    mpd
    ex
    rexlimdvva
    @52
    @44
    @94
    vt
    @73
    wrex
    #
    @69
    vi
    @71
    wral
    #
    vs
    @73
    wrex
    #
    wa
    #
    @74
    @52
    @42
    @241
    @43
    @243
    @52
    @39
    @12
    @29
    @42
    @241
    wb
    @51
    @50
    @39
    @40
    simp3l
    #
    @116
    @110
    vt
    cU
    cZ
    @25
    vi
    cN
    brbtwn
    syl3anc
    @52
    @40
    @12
    @29
    @43
    @243
    wb
    @51
    @50
    @39
    @40
    simp3r
    #
    @116
    @110
    vs
    @18
    cZ
    @25
    vi
    cN
    brbtwn
    syl3anc
    anbi12d
    @74
    @94
    @242
    wa
    #
    vs
    @73
    wrex
    vt
    @73
    wrex
    @244
    @72
    @247
    vt
    vs
    @73
    @73
    @62
    @69
    vi
    @71
    r19.26
    2rexbii
    @94
    @242
    vt
    vs
    @73
    @73
    reeanv
    bitri
    syl6bbr
    @52
    @21
    @81
    vr
    @73
    wrex
    #
    @85
    vr
    @73
    wrex
    #
    wo
    @87
    @52
    @19
    @248
    @20
    @249
    @52
    @39
    @12
    @40
    @19
    @248
    wb
    @245
    @116
    @246
    vr
    cU
    cZ
    @18
    vi
    cN
    brbtwn
    syl3anc
    @52
    @40
    @12
    @39
    @20
    @249
    wb
    @246
    @116
    @245
    vr
    @18
    cZ
    cU
    vi
    cN
    brbtwn
    syl3anc
    orbi12d
    @81
    @85
    vr
    @73
    r19.43
    syl6bbr
    3imtr4d
    3expia
    impd
    sylanl2
    3adantr2
    adantr
    mpd
    ralrimiva
    3exp2
    syl6
    exlimiv
    sylbi
    com4l
    3impd
    imp32
    @23
    cA
    @21
    vp
    @1
    crab
    #
    wss
    @2
    @22
    wa
    cD
    @250
    cA
    axcontlem4.1
    sseq2i
    @21
    vp
    @1
    cA
    ssrab
    bitri
    sylanbrc
end
