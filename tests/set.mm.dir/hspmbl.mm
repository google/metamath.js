include "cfv.mm"
include "co.mm"
include "covoln.mm"
include "ccaragen.mm"
include "cvoln.mm"
include "cdm.mm"
include "cuni.mm"
include "ovnome.mm"
include "eqid.mm"
include "cpw.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cmnf.mm"
include "cioo.mm"
include "cr.mm"
include "cif.mm"
include "cixp.mm"
include "cmap.mm"
include "wss.mm"
include "ciun.mm"
include "ovex.mm"
include "reex.mm"
include "ifex.mm"
include "ixpssmap.mm"
include "cvv.mm"
include "wral.mm"
include "iftrue.mm"
include "ioossre.mm"
include "a1i.mm"
include "eqsstrd.mm"
include "wn.mm"
include "iffalse.mm"
include "ssid.mm"
include "pm2.61i.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"
include "mapss.mm"
include "mp2an.mm"
include "sstri.mm"
include "wb.mm"
include "ixpexg.mm"
include "ax-mp.mm"
include "elpwg.mm"
include "cfn.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "equid.mm"
include "equequ1.mm"
include "ifbid.mm"
include "cbvixpv.mm"
include "mpt2eq123i.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "hspval.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "ovnf.mm"
include "fdm.mm"
include "syl.mm"
include "unieqd.mm"
include "unipw.mm"
include "eqtrd.mm"
include "pweqd.mm"
include "eleq12d.mm"
include "mpbird.mm"
include "wa.mm"
include "cin.mm"
include "cdif.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "simpl.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "cxr.mm"
include "adantr.mm"
include "inss1.mm"
include "elpwi.mm"
include "sstrd.mm"
include "adantl.mm"
include "ovnxrcl.mm"
include "ssdifssd.mm"
include "xaddcld.mm"
include "pnfge.mm"
include "id.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "wne.mm"
include "ovncl.mm"
include "neqne.mm"
include "ge0xrre.mm"
include "syl2anc.mm"
include "cn.mm"
include "c1st.mm"
include "cico.mm"
include "ccom.mm"
include "cxp.mm"
include "crab.mm"
include "crp.mm"
include "cvol.mm"
include "cprod.mm"
include "csumge0.mm"
include "c2nd.mm"
include "ad2antrr.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "cbvmptv.mm"
include "coeq2d.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "prodeq2dv.mm"
include "fveq2.mm"
include "fveq1.mm"
include "ixpeq2dv.mm"
include "iuneq2dv.mm"
include "sseq2d.mm"
include "cbvrabv.mm"
include "cbviunv.mm"
include "fveq12d.mm"
include "eleq2d.mm"
include "cbvprodv.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "rabbidva2.mm"
include "mpteq2dv.mm"
include "eqidd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "hspmbllem3.mm"
include "pm2.61dan.mm"
include "caragenel2d.mm"
include "dmvon.mm"

theorem hspmbl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  let cH: class H
  let cK: class K
  let cX: class X
  let cY: class Y
  let vl: setvar l
  let va: setvar a
  let vj: setvar j
  let vp: setvar p
  let vt: setvar t
  let vb: setvar b
  let vh: setvar h
  let vc: setvar c
  let vr: setvar r
  let vs: setvar s
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  assume hspmbl.1: |- H = ( x e. Fin |-> ( l e. x , y e. RR |-> X_ k e. x if ( k = l , ( -oo (,) y ) , RR ) ) )
  assume hspmbl.x: |- ( ph -> X e. Fin )
  assume hspmbl.i: |- ( ph -> K e. X )
  assume hspmbl.y: |- ( ph -> Y e. RR )

  disjoint K l
  disjoint K x
  disjoint K y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint X l
  disjoint X x
  disjoint X y
  disjoint Y l
  disjoint Y x
  disjoint Y y
  disjoint l ph
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint ph x
  disjoint ph y
  disjoint k x
  disjoint H a
  disjoint H j
  disjoint H p
  disjoint H t
  disjoint a j
  disjoint a p
  disjoint a t
  disjoint j p
  disjoint j t
  disjoint p t
  disjoint K a
  disjoint K b
  disjoint K h
  disjoint K j
  disjoint K p
  disjoint K t
  disjoint a b
  disjoint a h
  disjoint a l
  disjoint a x
  disjoint a y
  disjoint b h
  disjoint b j
  disjoint b l
  disjoint b p
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint h j
  disjoint h l
  disjoint h p
  disjoint h t
  disjoint h x
  disjoint h y
  disjoint j l
  disjoint j x
  disjoint j y
  disjoint l p
  disjoint l t
  disjoint p x
  disjoint p y
  disjoint t x
  disjoint t y
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X h
  disjoint X j
  disjoint X p
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint a c
  disjoint a r
  disjoint a s
  disjoint b c
  disjoint b r
  disjoint b s
  disjoint c h
  disjoint c j
  disjoint c l
  disjoint c p
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint h r
  disjoint h s
  disjoint j r
  disjoint j s
  disjoint l r
  disjoint l s
  disjoint p r
  disjoint p s
  disjoint r s
  disjoint r t
  disjoint s t
  disjoint X i
  disjoint b i
  disjoint c i
  disjoint h i
  disjoint i j
  disjoint i l
  disjoint i p
  disjoint i r
  disjoint i s
  disjoint i t
  disjoint X m
  disjoint a m
  disjoint b m
  disjoint h m
  disjoint j m
  disjoint l m
  disjoint m p
  disjoint m r
  disjoint m t
  disjoint X n
  disjoint b n
  disjoint h n
  disjoint i m
  disjoint i n
  disjoint j n
  disjoint l n
  disjoint m n
  disjoint n p
  disjoint n r
  disjoint c x
  disjoint c y
  disjoint s x
  disjoint s y
  disjoint Y a
  disjoint Y b
  disjoint Y h
  disjoint Y j
  disjoint Y p
  disjoint Y t
  disjoint a ph
  disjoint b ph
  disjoint h ph
  disjoint j ph
  disjoint p ph
  disjoint ph r
  disjoint ph t
  disjoint i x
  disjoint i y
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint k p
  assert |- ( ph -> ( K ( H ` X ) Y ) e. dom ( voln ` X ) )

  proof
    wph
    cK
    cY
    cX
    cH
    cfv
    co
    #
    cX
    covoln
    cfv
    #
    ccaragen
    cfv
    #
    cX
    cvoln
    cfv
    cdm
    #
    wph
    @2
    @0
    @1
    @1
    cdm
    #
    cuni
    #
    va
    wph
    cX
    hspmbl.x
    ovnome
    @5
    eqid
    @2
    eqid
    wph
    @0
    @5
    cpw
    #
    wcel
    vp
    cX
    vp
    cv
    #
    cK
    wceq
    #
    cmnf
    cY
    cioo
    co
    #
    cr
    cif
    #
    cixp
    #
    cr
    cX
    cmap
    co
    #
    cpw
    #
    wcel
    #
    @14
    wph
    @14
    @11
    @12
    wss
    #
    @11
    vp
    cX
    @10
    ciun
    #
    cX
    cmap
    co
    #
    @12
    vp
    cX
    @10
    @8
    @9
    cr
    cmnf
    cY
    cioo
    ovex
    reex
    ifex
    #
    ixpssmap
    cr
    cvv
    wcel
    @16
    cr
    wss
    #
    @17
    @12
    wss
    reex
    @19
    @10
    cr
    wss
    #
    vp
    cX
    wral
    @20
    vp
    cX
    @8
    @20
    @8
    @10
    @9
    cr
    @8
    @9
    cr
    iftrue
    @9
    cr
    wss
    @8
    cmnf
    cY
    ioossre
    a1i
    eqsstrd
    @8
    wn
    #
    @10
    cr
    cr
    @8
    @9
    cr
    iffalse
    cr
    cr
    wss
    @21
    cr
    ssid
    a1i
    eqsstrd
    pm2.61i
    rgenw
    vp
    cX
    @10
    cr
    iunss
    mpbir
    @16
    cr
    cX
    cvv
    mapss
    mp2an
    sstri
    @11
    cvv
    wcel
    #
    @14
    @15
    wb
    @10
    cvv
    wcel
    #
    vp
    cX
    wral
    @22
    @23
    vp
    cX
    @18
    rgenw
    vp
    cX
    @10
    cvv
    ixpexg
    ax-mp
    @11
    @12
    cvv
    elpwg
    ax-mp
    mpbir
    a1i
    wph
    @0
    @11
    @6
    @13
    wph
    vx
    vy
    vl
    vp
    cH
    cK
    cX
    cY
    cH
    vx
    cfn
    vl
    vy
    vx
    cv
    #
    cr
    vk
    @24
    vk
    cv
    #
    vl
    cv
    #
    wceq
    #
    cmnf
    vy
    cv
    cioo
    co
    #
    cr
    cif
    #
    cixp
    #
    cmpt2
    #
    cmpt
    vx
    cfn
    vl
    vy
    @24
    cr
    vp
    @24
    @7
    @26
    wceq
    #
    @28
    cr
    cif
    #
    cixp
    #
    cmpt2
    #
    cmpt
    hspmbl.1
    vx
    cfn
    @31
    @35
    vl
    vy
    @24
    cr
    @30
    @24
    cr
    @34
    vx
    equid
    cr
    eqid
    vk
    vp
    @24
    @29
    @33
    @25
    @7
    wceq
    @27
    @32
    @28
    cr
    vk
    vp
    vl
    equequ1
    ifbid
    cbvixpv
    mpt2eq123i
    mpteq2i
    eqtri
    #
    hspmbl.x
    hspmbl.i
    hspmbl.y
    hspval
    wph
    @5
    @12
    wph
    @5
    @13
    cuni
    #
    @12
    wph
    @4
    @13
    wph
    @13
    cc0
    cpnf
    cicc
    co
    #
    @1
    wf
    @4
    @13
    wceq
    wph
    cX
    hspmbl.x
    ovnf
    @13
    @38
    @1
    fdm
    syl
    unieqd
    @37
    @12
    wceq
    wph
    @12
    unipw
    a1i
    eqtrd
    pweqd
    #
    eleq12d
    mpbird
    wph
    va
    cv
    #
    @6
    wcel
    #
    wa
    #
    wph
    @40
    @13
    wcel
    #
    @40
    @0
    cin
    #
    @1
    cfv
    #
    @40
    @0
    cdif
    #
    @1
    cfv
    #
    cxad
    co
    #
    @40
    @1
    cfv
    #
    cle
    wbr
    #
    wph
    @41
    simpl
    #
    @42
    @40
    @6
    @13
    wph
    @41
    simpr
    @42
    wph
    @6
    @13
    wceq
    @51
    @39
    syl
    eleqtrd
    wph
    @43
    wa
    #
    @49
    cpnf
    wceq
    #
    @50
    @52
    @53
    wa
    @48
    cpnf
    @49
    cle
    @52
    @48
    cpnf
    cle
    wbr
    #
    @53
    @52
    @48
    cxr
    wcel
    @54
    @52
    @45
    @47
    @52
    @44
    cX
    wph
    cX
    cfn
    wcel
    #
    @43
    hspmbl.x
    adantr
    #
    @43
    @44
    @12
    wss
    wph
    @43
    @44
    @40
    @12
    @44
    @40
    wss
    @43
    @40
    @0
    inss1
    a1i
    @40
    @12
    elpwi
    #
    sstrd
    adantl
    ovnxrcl
    @52
    @46
    cX
    @56
    @52
    @40
    @12
    @0
    @43
    @40
    @12
    wss
    #
    wph
    @57
    adantl
    #
    ssdifssd
    ovnxrcl
    xaddcld
    @48
    pnfge
    syl
    adantr
    @53
    cpnf
    @49
    wceq
    @52
    @53
    @49
    cpnf
    @53
    id
    eqcomd
    adantl
    breqtrd
    @52
    @53
    wn
    #
    wa
    #
    @52
    @49
    cr
    wcel
    #
    @50
    @52
    @60
    simpl
    @61
    @49
    @38
    wcel
    #
    @49
    cpnf
    wne
    #
    @62
    @52
    @63
    @60
    @52
    @40
    cX
    @56
    @59
    ovncl
    adantr
    @60
    @64
    @52
    @49
    cpnf
    neqne
    adantl
    @49
    ge0xrre
    syl2anc
    @52
    @62
    wa
    vx
    vy
    @40
    vj
    cn
    vm
    cX
    vm
    cv
    #
    vj
    cv
    #
    vt
    cv
    #
    cfv
    #
    cfv
    #
    c1st
    cfv
    #
    cmpt
    #
    cmpt
    va
    @13
    @40
    vj
    cn
    vp
    cX
    @7
    cico
    @66
    @26
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    vl
    cr
    cr
    cxp
    cX
    cmap
    co
    #
    cn
    cmap
    co
    #
    crab
    #
    cmpt
    #
    vc
    @13
    vs
    crp
    vm
    cn
    @65
    @67
    cfv
    #
    vi
    @78
    cX
    @65
    cico
    vi
    cv
    #
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vm
    cprod
    #
    cmpt
    #
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    vc
    cv
    #
    @1
    cfv
    #
    vs
    cv
    #
    cxad
    co
    #
    cle
    wbr
    #
    vt
    @92
    va
    @13
    @40
    vi
    cn
    vn
    cX
    vn
    cv
    #
    cico
    @83
    @65
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    vm
    @79
    crab
    #
    cmpt
    #
    cfv
    #
    crab
    #
    cmpt
    #
    cmpt
    vi
    cn
    vm
    cX
    @65
    @83
    @67
    cfv
    #
    cfv
    #
    c2nd
    cfv
    #
    cmpt
    #
    cmpt
    vh
    vt
    vj
    vp
    cH
    cK
    vi
    @78
    cX
    @7
    @84
    cfv
    #
    cvol
    cfv
    #
    vp
    cprod
    #
    cmpt
    #
    cX
    cY
    vr
    vb
    vl
    @36
    @52
    @55
    @62
    @56
    adantr
    wph
    cK
    cX
    wcel
    @43
    @62
    hspmbl.i
    ad2antrr
    wph
    cY
    cr
    wcel
    @43
    @62
    hspmbl.y
    ad2antrr
    @52
    @62
    simpr
    @52
    @58
    @62
    @59
    adantr
    va
    vb
    @13
    @80
    vb
    cv
    #
    @76
    wss
    #
    vl
    @79
    crab
    @40
    @117
    wceq
    @77
    @118
    vl
    @79
    @40
    @117
    @76
    sseq1
    rabbidv
    cbvmptv
    vi
    vh
    @78
    @115
    cX
    @7
    cico
    vh
    cv
    #
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vp
    cprod
    @83
    @119
    wceq
    #
    cX
    @114
    @122
    vp
    @123
    @7
    cX
    wcel
    #
    wa
    #
    @113
    @121
    cvol
    @125
    @7
    @84
    @120
    @125
    @83
    @119
    cico
    @123
    @124
    simpl
    coeq2d
    fveq1d
    fveq2d
    prodeq2dv
    cbvmptv
    vc
    vb
    @13
    @108
    vr
    crp
    vj
    cn
    @68
    @116
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @117
    @1
    cfv
    #
    vr
    cv
    #
    cxad
    co
    #
    cle
    wbr
    #
    vt
    @117
    @81
    cfv
    #
    crab
    #
    cmpt
    #
    @92
    @117
    wceq
    #
    @108
    vs
    crp
    @128
    @129
    @94
    cxad
    co
    #
    cle
    wbr
    #
    vt
    @133
    crab
    #
    cmpt
    #
    @135
    @136
    vs
    crp
    @107
    @139
    @136
    @96
    @138
    vt
    @106
    @133
    @136
    @67
    @106
    wcel
    @67
    @133
    wcel
    #
    @96
    @138
    @136
    @106
    @133
    @67
    @136
    @92
    @117
    @105
    @81
    @105
    @81
    wceq
    @136
    va
    @13
    @104
    @80
    @104
    @40
    vi
    cn
    vp
    cX
    @7
    cico
    @83
    @119
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    vh
    @79
    crab
    @80
    @103
    @147
    vm
    vh
    @79
    @65
    @119
    wceq
    #
    @102
    @146
    @40
    @148
    vi
    cn
    @101
    @145
    @148
    @101
    @145
    wceq
    @83
    cn
    wcel
    #
    @148
    @101
    vp
    cX
    @7
    @99
    cfv
    #
    cixp
    #
    @145
    @101
    @151
    wceq
    @148
    vn
    vp
    cX
    @100
    @150
    @97
    @7
    @99
    fveq2
    cbvixpv
    a1i
    @148
    vp
    cX
    @150
    @144
    @148
    @7
    @99
    @143
    @148
    @98
    @142
    cico
    @83
    @65
    @119
    fveq1
    coeq2d
    fveq1d
    ixpeq2dv
    eqtrd
    adantr
    iuneq2dv
    sseq2d
    cbvrabv
    @147
    @77
    vh
    vl
    @79
    @119
    @26
    wceq
    #
    @146
    @76
    @40
    @152
    @146
    vi
    cn
    vp
    cX
    @7
    cico
    @83
    @26
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    @76
    @152
    vi
    cn
    @145
    @156
    @152
    @145
    @156
    wceq
    @149
    @152
    vp
    cX
    @144
    @155
    @152
    @7
    @143
    @154
    @152
    @142
    @153
    cico
    @83
    @119
    @26
    fveq1
    coeq2d
    fveq1d
    ixpeq2dv
    adantr
    iuneq2dv
    @157
    @76
    wceq
    @152
    vi
    vj
    cn
    @156
    @75
    @83
    @66
    wceq
    #
    vp
    cX
    @155
    @74
    @158
    @7
    @154
    @73
    @158
    @153
    @72
    cico
    @83
    @66
    @26
    fveq2
    coeq2d
    fveq1d
    ixpeq2dv
    cbviunv
    a1i
    eqtrd
    sseq2d
    cbvrabv
    eqtri
    mpteq2i
    a1i
    @136
    id
    fveq12d
    eleq2d
    @136
    @91
    @128
    @95
    @137
    cle
    @136
    @90
    @127
    csumge0
    @90
    @127
    wceq
    @136
    vm
    vj
    cn
    @89
    @126
    @65
    @66
    wceq
    #
    @82
    @68
    @88
    @116
    @88
    @116
    wceq
    @159
    vi
    @78
    @87
    @115
    cX
    @86
    @114
    vm
    vp
    @65
    @7
    wceq
    #
    @85
    @113
    cvol
    @65
    @7
    @84
    fveq2
    fveq2d
    cbvprodv
    mpteq2i
    a1i
    @65
    @66
    @67
    fveq2
    fveq12d
    cbvmptv
    a1i
    fveq2d
    @136
    @93
    @129
    @94
    cxad
    @92
    @117
    @1
    fveq2
    oveq1d
    breq12d
    anbi12d
    rabbidva2
    mpteq2dv
    @140
    @135
    wceq
    @136
    vs
    vr
    crp
    @139
    @134
    @94
    @130
    wceq
    #
    @138
    @132
    vt
    @133
    @133
    @161
    @141
    @141
    @138
    @132
    @161
    @133
    @133
    @67
    @161
    @133
    eqidd
    eleq2d
    @161
    @137
    @131
    @128
    cle
    @94
    @130
    @129
    cxad
    oveq2
    breq2d
    anbi12d
    rabbidva2
    cbvmptv
    a1i
    eqtrd
    cbvmptv
    vj
    cn
    @71
    vp
    cX
    @7
    @68
    cfv
    #
    c1st
    cfv
    #
    cmpt
    vm
    vp
    cX
    @70
    @163
    @160
    @69
    @162
    c1st
    @65
    @7
    @68
    fveq2
    #
    fveq2d
    cbvmptv
    mpteq2i
    vi
    vj
    cn
    @112
    vp
    cX
    @162
    c2nd
    cfv
    #
    cmpt
    #
    @158
    @112
    vm
    cX
    @69
    c2nd
    cfv
    #
    cmpt
    #
    @166
    @158
    vm
    cX
    @111
    @167
    @158
    @110
    @69
    c2nd
    @158
    @65
    @109
    @68
    @83
    @66
    @67
    fveq2
    fveq1d
    fveq2d
    mpteq2dv
    @168
    @166
    wceq
    @158
    vm
    vp
    cX
    @167
    @165
    @160
    @69
    @162
    c2nd
    @164
    fveq2d
    cbvmptv
    a1i
    eqtrd
    cbvmptv
    hspmbllem3
    syl2anc
    pm2.61dan
    syl2anc
    caragenel2d
    wph
    @3
    @2
    wph
    cX
    hspmbl.x
    dmvon
    eqcomd
    eleqtrd
end
