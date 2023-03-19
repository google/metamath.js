include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "co.mm"
include "cn.mm"
include "cv.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cle.mm"
include "wa.mm"
include "cmin.mm"
include "cico.mm"
include "cvol.mm"
include "cpnf.mm"
include "wceq.mm"
include "cr.mm"
include "csn.mm"
include "wcel.mm"
include "snidg.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "ffvelrnd.mm"
include "resubcld.mm"
include "rexrd.mm"
include "cxr.mm"
include "pnfxr.mm"
include "a1i.mm"
include "ltpnfd.mm"
include "xrltled.mm"
include "ad2antrr.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "wn.mm"
include "simpl.mm"
include "simpr.mm"
include "cvv.mm"
include "nnex.mm"
include "cc0.mm"
include "cicc.mm"
include "wf.mm"
include "cprod.mm"
include "cfn.mm"
include "snfi.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "cmap.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "hoidmvn0val.mm"
include "prodeq1i.mm"
include "cc.mm"
include "volicore.mm"
include "syl2anc.mm"
include "recnd.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "prodsn.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "cif.mm"
include "cmpt2.mm"
include "cbvprodv.mm"
include "ifeq2.mm"
include "ax-mp.mm"
include "mpt2eq3ia.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "hoidmvcl.mm"
include "eqid.mm"
include "fmptd.mm"
include "wss.mm"
include "icossicc.mm"
include "fssd.mm"
include "feq1dd.mm"
include "sge0repnf.mm"
include "mpbird.mm"
include "crab.mm"
include "csup.mm"
include "simplr.mm"
include "ciun.mm"
include "wral.mm"
include "wrex.mm"
include "cop.mm"
include "cixp.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "elsni.mm"
include "rgen.mm"
include "ixpeq2.mm"
include "iuneq2i.mm"
include "sseqtrd.mm"
include "eqidd.mm"
include "opeq2.mm"
include "sneqd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "wb.mm"
include "elixpsn.mm"
include "eqcomi.mm"
include "ixpeq1.mm"
include "eleqtrd.mm"
include "sseldd.mm"
include "eliun.mm"
include "sylib.mm"
include "wi.mm"
include "mpbid.mm"
include "w3a.mm"
include "opex.mm"
include "sneqr.mm"
include "vex.mm"
include "opthg.mm"
include "simprd.mm"
include "3adant2.mm"
include "simp2.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ex.mm"
include "reximdva.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "fveq1d.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "iuneq2dv.mm"
include "cbviunv.mm"
include "eqtr2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "mpteq2ia.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "cbvmptv.mm"
include "fveq2i.mm"
include "oveq1.mm"
include "breq1d.mm"
include "ifbieq1d.mm"
include "breq2.mm"
include "ifbieq2d.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "breq12d.mm"
include "cbvrabv.mm"
include "hoidmv1lelem3.mm"
include "pm2.61dan.mm"
include "prodeq1d.mm"
include "volico.mm"
include "iftrue.mm"
include "iffalse.mm"
include "sge0ge0.mm"
include "eqbrtrd.mm"

theorem hoidmv1le
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cL: class L
  let cV: class V
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vw: setvar w
  let vz: setvar z
  let vy: setvar y
  let vl: setvar l
  let vh: setvar h
  assume hoidmv1le.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoidmv1le.z: |- ( ph -> Z e. V )
  assume hoidmv1le.x: |- X = { Z }
  assume hoidmv1le.a: |- ( ph -> A : X --> RR )
  assume hoidmv1le.b: |- ( ph -> B : X --> RR )
  assume hoidmv1le.c: |- ( ph -> C : NN --> ( RR ^m X ) )
  assume hoidmv1le.d: |- ( ph -> D : NN --> ( RR ^m X ) )
  assume hoidmv1le.s: |- ( ph -> X_ k e. X ( ( A ` k ) [,) ( B ` k ) ) C_ U_ j e. NN X_ k e. X ( ( ( C ` j ) ` k ) [,) ( ( D ` j ) ` k ) ) )

  disjoint A a
  disjoint A b
  disjoint A j
  disjoint A k
  disjoint A x
  disjoint a b
  disjoint a j
  disjoint a k
  disjoint a x
  disjoint b j
  disjoint b k
  disjoint b x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint B a
  disjoint B b
  disjoint B j
  disjoint B k
  disjoint B x
  disjoint C a
  disjoint C b
  disjoint C j
  disjoint C k
  disjoint C x
  disjoint D a
  disjoint D b
  disjoint D j
  disjoint D k
  disjoint D x
  disjoint V k
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint a ph
  disjoint b ph
  disjoint j ph
  disjoint ph x
  disjoint k x
  disjoint A i
  disjoint A w
  disjoint A z
  disjoint i j
  disjoint i w
  disjoint i z
  disjoint j w
  disjoint j z
  disjoint w z
  disjoint A y
  disjoint j y
  disjoint k y
  disjoint x y
  disjoint B i
  disjoint B w
  disjoint B z
  disjoint B y
  disjoint C l
  disjoint a l
  disjoint b l
  disjoint j l
  disjoint k l
  disjoint l x
  disjoint C h
  disjoint C i
  disjoint C w
  disjoint C z
  disjoint h i
  disjoint h w
  disjoint h z
  disjoint C y
  disjoint D l
  disjoint D h
  disjoint D i
  disjoint D w
  disjoint D z
  disjoint D y
  disjoint V y
  disjoint X l
  disjoint X y
  disjoint Z h
  disjoint Z i
  disjoint Z w
  disjoint Z z
  disjoint Z y
  disjoint l ph
  disjoint i ph
  disjoint ph z
  disjoint ph y
  assert |- ( ph -> ( A ( L ` X ) B ) <_ ( sum^ ` ( j e. NN |-> ( ( C ` j ) ( L ` X ) ( D ` j ) ) ) ) )

  proof
    wph
    cZ
    cA
    cfv
    #
    cZ
    cB
    cfv
    #
    clt
    wbr
    #
    cA
    cB
    cX
    cL
    cfv
    #
    co
    #
    vj
    cn
    vj
    cv
    #
    cC
    cfv
    #
    @5
    cD
    cfv
    #
    @3
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    wph
    @2
    wa
    #
    @11
    @1
    @0
    cmin
    co
    #
    vj
    cn
    cZ
    @6
    cfv
    #
    cZ
    @7
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    @12
    @19
    cpnf
    wceq
    #
    @20
    @12
    @21
    wa
    @13
    cpnf
    @19
    cle
    wph
    @13
    cpnf
    cle
    wbr
    @2
    @21
    wph
    @13
    cpnf
    wph
    @13
    wph
    @1
    @0
    wph
    cX
    cr
    cZ
    cB
    hoidmv1le.b
    wph
    cZ
    cZ
    csn
    #
    cX
    wph
    cZ
    cV
    wcel
    #
    cZ
    @22
    wcel
    hoidmv1le.z
    cZ
    cV
    snidg
    syl
    hoidmv1le.x
    syl6eleqr
    #
    ffvelrnd
    #
    wph
    cX
    cr
    cZ
    cA
    hoidmv1le.a
    @24
    ffvelrnd
    #
    resubcld
    #
    rexrd
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    wph
    @13
    @27
    ltpnfd
    xrltled
    ad2antrr
    @21
    cpnf
    @19
    wceq
    @12
    @21
    @19
    cpnf
    @21
    id
    eqcomd
    adantl
    breqtrd
    @12
    @21
    wn
    #
    wa
    #
    @12
    @19
    cr
    wcel
    #
    @20
    @12
    @28
    simpl
    @29
    @30
    @28
    @12
    @28
    simpr
    @29
    @18
    cvv
    cn
    cn
    cvv
    wcel
    #
    @29
    nnex
    a1i
    wph
    cn
    cc0
    cpnf
    cicc
    co
    #
    @18
    wf
    @2
    @28
    wph
    cn
    @32
    @9
    @18
    wph
    vj
    cn
    @8
    @17
    wph
    @5
    cn
    wcel
    #
    wa
    #
    @8
    cX
    vk
    cv
    #
    @6
    cfv
    #
    @35
    @7
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    @22
    @39
    vk
    cprod
    #
    @17
    @34
    vx
    @6
    @7
    vk
    cL
    cX
    va
    vb
    hoidmv1le.l
    wph
    cX
    cfn
    wcel
    @33
    wph
    cX
    @22
    cfn
    cX
    @22
    wceq
    #
    wph
    hoidmv1le.x
    a1i
    #
    @22
    cfn
    wcel
    wph
    cZ
    snfi
    a1i
    eqeltrd
    #
    adantr
    #
    wph
    cX
    c0
    wne
    #
    @33
    wph
    cZ
    cX
    wcel
    #
    @46
    @24
    cX
    cZ
    ne0i
    syl
    #
    adantr
    @34
    @6
    cr
    cX
    cmap
    co
    #
    wcel
    cX
    cr
    @6
    wf
    wph
    cn
    @49
    @5
    cC
    hoidmv1le.c
    ffvelrnda
    @6
    cr
    cX
    elmapi
    syl
    #
    @34
    @7
    @49
    wcel
    cX
    cr
    @7
    wf
    wph
    cn
    @49
    @5
    cD
    hoidmv1le.d
    ffvelrnda
    @7
    cr
    cX
    elmapi
    syl
    #
    hoidmvn0val
    @40
    @41
    wceq
    @34
    cX
    @22
    @39
    vk
    hoidmv1le.x
    prodeq1i
    a1i
    @34
    @23
    @17
    cc
    wcel
    @41
    @17
    wceq
    wph
    @23
    @33
    hoidmv1le.z
    adantr
    @34
    @17
    @34
    @14
    cr
    wcel
    @15
    cr
    wcel
    @17
    cr
    wcel
    @34
    cX
    cr
    cZ
    @6
    @50
    wph
    @47
    @33
    @24
    adantr
    #
    ffvelrnd
    #
    @34
    cX
    cr
    cZ
    @7
    @51
    @52
    ffvelrnd
    #
    @14
    @15
    volicore
    syl2anc
    recnd
    @39
    @17
    vk
    cZ
    cV
    @35
    cZ
    wceq
    #
    @38
    @16
    cvol
    @55
    @36
    @14
    @37
    @15
    cico
    @35
    cZ
    @6
    fveq2
    @35
    cZ
    @7
    fveq2
    oveq12d
    #
    fveq2d
    prodsn
    syl2anc
    3eqtrd
    mpteq2dva
    #
    wph
    cn
    cc0
    cpnf
    cico
    co
    #
    @32
    @9
    wph
    vj
    cn
    @8
    @58
    @9
    @34
    vx
    @6
    @7
    vl
    cL
    cX
    va
    vb
    cL
    vx
    cfn
    va
    vb
    cr
    vx
    cv
    #
    cmap
    co
    #
    @60
    @59
    c0
    wceq
    #
    cc0
    @59
    @35
    va
    cv
    #
    cfv
    #
    @35
    vb
    cv
    #
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cif
    #
    cmpt2
    #
    cmpt
    vx
    cfn
    va
    vb
    @60
    @60
    @61
    cc0
    @59
    vl
    cv
    #
    @62
    cfv
    #
    @71
    @64
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vl
    cprod
    #
    cif
    #
    cmpt2
    #
    cmpt
    hoidmv1le.l
    vx
    cfn
    @70
    @78
    va
    vb
    @60
    @60
    @69
    @77
    @69
    @77
    wceq
    #
    @62
    @60
    wcel
    @64
    @60
    wcel
    wa
    @68
    @76
    wceq
    @79
    @59
    @67
    @75
    vk
    vl
    @35
    @71
    wceq
    #
    @66
    @74
    cvol
    @80
    @63
    @72
    @65
    @73
    cico
    @35
    @71
    @62
    fveq2
    @35
    @71
    @64
    fveq2
    oveq12d
    fveq2d
    cbvprodv
    @61
    @68
    @76
    cc0
    ifeq2
    ax-mp
    a1i
    mpt2eq3ia
    mpteq2i
    eqtri
    @45
    @50
    @51
    hoidmvcl
    @9
    eqid
    fmptd
    @58
    @32
    wss
    wph
    cc0
    cpnf
    icossicc
    a1i
    fssd
    #
    feq1dd
    ad2antrr
    sge0repnf
    mpbird
    @12
    @30
    wa
    #
    @13
    vi
    cn
    vi
    cv
    #
    vj
    cn
    @14
    cmpt
    #
    cfv
    #
    @83
    vj
    cn
    @15
    cmpt
    #
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @19
    cle
    @82
    vz
    @0
    @1
    @84
    @86
    vw
    cv
    #
    @0
    cmin
    co
    #
    vh
    cn
    cZ
    vh
    cv
    #
    cC
    cfv
    #
    cfv
    #
    cZ
    @94
    cD
    cfv
    #
    cfv
    #
    @92
    cle
    wbr
    #
    @98
    @92
    cif
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    vw
    @0
    @1
    cicc
    co
    #
    crab
    #
    cr
    clt
    csup
    #
    @107
    vi
    wph
    @0
    cr
    wcel
    #
    @2
    @30
    @26
    ad2antrr
    wph
    @1
    cr
    wcel
    #
    @2
    @30
    @25
    ad2antrr
    wph
    @2
    @30
    simplr
    wph
    cn
    cr
    @84
    wf
    @2
    @30
    wph
    vj
    cn
    @14
    cr
    @84
    @53
    @84
    eqid
    #
    fmptd
    ad2antrr
    wph
    cn
    cr
    @86
    wf
    @2
    @30
    wph
    vj
    cn
    @15
    cr
    @86
    @54
    @86
    eqid
    #
    fmptd
    ad2antrr
    wph
    @0
    @1
    cico
    co
    #
    vi
    cn
    @88
    ciun
    #
    wss
    @2
    @30
    wph
    @113
    vj
    cn
    @16
    ciun
    #
    @114
    wph
    @59
    @115
    wcel
    #
    vx
    @113
    wral
    @113
    @115
    wss
    wph
    @116
    vx
    @113
    wph
    @59
    @113
    wcel
    #
    wa
    #
    @59
    @16
    wcel
    #
    vj
    cn
    wrex
    #
    @116
    @118
    cZ
    @59
    cop
    #
    csn
    #
    vk
    cX
    @16
    cixp
    #
    wcel
    #
    vj
    cn
    wrex
    #
    @120
    @118
    @122
    vj
    cn
    @123
    ciun
    #
    wcel
    @125
    @118
    vk
    cX
    @35
    cA
    cfv
    #
    @35
    cB
    cfv
    #
    cico
    co
    #
    cixp
    #
    @126
    @122
    wph
    @130
    @126
    wss
    @117
    wph
    @130
    vj
    cn
    vk
    cX
    @38
    cixp
    #
    ciun
    #
    @126
    hoidmv1le.s
    @132
    @126
    wceq
    wph
    vj
    cn
    @131
    @123
    @131
    @123
    wceq
    #
    @33
    @38
    @16
    wceq
    #
    vk
    cX
    wral
    @133
    @134
    vk
    cX
    @35
    cX
    wcel
    #
    @55
    @134
    @135
    @35
    @22
    wcel
    #
    @55
    @135
    @136
    cX
    @22
    @35
    hoidmv1le.x
    eleq2i
    biimpi
    @35
    cZ
    elsni
    syl
    #
    @56
    syl
    rgen
    vk
    cX
    @38
    @16
    ixpeq2
    ax-mp
    a1i
    iuneq2i
    a1i
    sseqtrd
    adantr
    @118
    @122
    vk
    @22
    @113
    cixp
    #
    @130
    @118
    @122
    @138
    wcel
    #
    @122
    cZ
    vy
    cv
    #
    cop
    #
    csn
    #
    wceq
    #
    vy
    @113
    wrex
    #
    @117
    @144
    wph
    @117
    @117
    @122
    @122
    wceq
    #
    @144
    @117
    id
    @117
    @122
    eqidd
    @143
    @145
    vy
    @59
    @113
    @140
    @59
    wceq
    #
    @142
    @122
    @122
    @146
    @141
    @121
    @140
    @59
    cZ
    opeq2
    sneqd
    eqeq2d
    rspcev
    syl2anc
    adantl
    wph
    @139
    @144
    wb
    #
    @117
    wph
    @23
    @147
    hoidmv1le.z
    vk
    vy
    cZ
    @113
    @122
    cV
    elixpsn
    syl
    adantr
    mpbird
    wph
    @138
    @130
    wceq
    #
    @117
    @148
    wph
    @138
    vk
    cX
    @113
    cixp
    #
    @130
    @22
    cX
    wceq
    @138
    @149
    wceq
    cX
    @22
    hoidmv1le.x
    eqcomi
    vk
    @22
    cX
    @113
    ixpeq1
    ax-mp
    @113
    @129
    wceq
    #
    vk
    cX
    wral
    @149
    @130
    wceq
    @150
    vk
    cX
    @135
    @129
    @113
    @135
    @127
    @0
    @128
    @1
    cico
    @135
    @55
    @127
    @0
    wceq
    @137
    @35
    cZ
    cA
    fveq2
    #
    syl
    @135
    @55
    @128
    @1
    wceq
    @137
    @35
    cZ
    cB
    fveq2
    #
    syl
    oveq12d
    eqcomd
    rgen
    vk
    cX
    @113
    @129
    ixpeq2
    ax-mp
    eqtri
    a1i
    adantr
    eleqtrd
    sseldd
    vj
    @122
    cn
    @123
    eliun
    sylib
    @118
    @124
    @119
    vj
    cn
    wph
    @124
    @119
    wi
    @117
    @33
    wph
    @124
    @119
    wph
    @124
    wa
    #
    @143
    vy
    @16
    wrex
    #
    @119
    @153
    @122
    vk
    @22
    @16
    cixp
    #
    wcel
    #
    @154
    @124
    @156
    wph
    @124
    @156
    @123
    @155
    @122
    @42
    @123
    @155
    wceq
    hoidmv1le.x
    vk
    cX
    @22
    @16
    ixpeq1
    ax-mp
    eleq2i
    biimpi
    adantl
    wph
    @156
    @154
    wb
    #
    @124
    wph
    @23
    @157
    hoidmv1le.z
    vk
    vy
    cZ
    @16
    @122
    cV
    elixpsn
    syl
    adantr
    mpbid
    @153
    @143
    @119
    vy
    @16
    wph
    @140
    @16
    wcel
    #
    @143
    @119
    wi
    wi
    @124
    wph
    @158
    @143
    @119
    wph
    @158
    @143
    w3a
    @59
    @140
    @16
    wph
    @143
    @59
    @140
    wceq
    #
    @158
    wph
    @143
    wa
    #
    cZ
    cZ
    wceq
    #
    @159
    @160
    @121
    @141
    wceq
    #
    @161
    @159
    wa
    #
    @143
    @162
    wph
    @121
    @141
    cZ
    @59
    opex
    sneqr
    adantl
    wph
    @162
    @163
    wb
    #
    @143
    wph
    @23
    @59
    cvv
    wcel
    #
    @164
    hoidmv1le.z
    @165
    wph
    vx
    vex
    a1i
    cZ
    @59
    cZ
    @140
    cV
    cvv
    opthg
    syl2anc
    adantr
    mpbid
    simprd
    3adant2
    wph
    @158
    @143
    simp2
    eqeltrd
    3exp
    adantr
    rexlimdv
    mpd
    ex
    ad2antrr
    reximdva
    mpd
    vj
    @59
    cn
    @16
    eliun
    sylibr
    ralrimiva
    vx
    @113
    @115
    dfss3
    sylibr
    wph
    @114
    vi
    cn
    cZ
    @83
    cC
    cfv
    #
    cfv
    #
    cZ
    @83
    cD
    cfv
    #
    cfv
    #
    cico
    co
    #
    ciun
    #
    @115
    wph
    vi
    cn
    @88
    @170
    wph
    @83
    cn
    wcel
    #
    wa
    #
    @85
    @167
    @87
    @169
    cico
    @173
    vj
    @83
    @14
    @167
    cn
    @84
    cvv
    @173
    @84
    eqidd
    @5
    @83
    wceq
    #
    @14
    @167
    wceq
    @173
    @174
    cZ
    @6
    @166
    @5
    @83
    cC
    fveq2
    fveq1d
    #
    adantl
    wph
    @172
    simpr
    #
    @173
    cZ
    @166
    fvexd
    fvmptd
    @173
    vj
    @83
    @15
    @169
    cn
    @86
    cvv
    @173
    @86
    eqidd
    @174
    @15
    @169
    wceq
    @173
    @174
    cZ
    @7
    @168
    @5
    @83
    cD
    fveq2
    fveq1d
    #
    adantl
    @176
    @173
    cZ
    @168
    fvexd
    fvmptd
    oveq12d
    iuneq2dv
    @171
    @115
    wceq
    wph
    @115
    @171
    vj
    vi
    cn
    @16
    @170
    @174
    @14
    @167
    @15
    @169
    cico
    @175
    @177
    oveq12d
    #
    cbviunv
    eqcomi
    a1i
    eqtr2d
    sseqtrd
    ad2antrr
    @82
    @91
    @19
    cr
    @91
    @19
    wceq
    @82
    @90
    @18
    csumge0
    @90
    vi
    cn
    @170
    cvol
    cfv
    #
    cmpt
    @18
    vi
    cn
    @89
    @179
    @172
    @88
    @170
    cvol
    @172
    @85
    @167
    @87
    @169
    cico
    vj
    @83
    @14
    @167
    cn
    @84
    @175
    @111
    cZ
    @166
    fvex
    fvmpt
    #
    vj
    @83
    @15
    @169
    cn
    @86
    @177
    @112
    cZ
    @168
    fvex
    fvmpt
    #
    oveq12d
    fveq2d
    mpteq2ia
    vi
    vj
    cn
    @179
    @17
    @83
    @5
    wceq
    #
    @170
    @16
    cvol
    @174
    @16
    @170
    wceq
    #
    wi
    #
    @182
    @170
    @16
    wceq
    #
    wi
    #
    @178
    @184
    @182
    @183
    wi
    @186
    @174
    @182
    @183
    @5
    @83
    eqcom
    imbi1i
    @183
    @185
    @182
    @16
    @170
    eqcom
    imbi2i
    bitri
    mpbi
    fveq2d
    cbvmptv
    eqtri
    fveq2i
    a1i
    #
    @12
    @30
    simpr
    eqeltrd
    @105
    vz
    cv
    #
    @0
    cmin
    co
    #
    vi
    cn
    @85
    @87
    @188
    cle
    wbr
    #
    @87
    @188
    cif
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    vw
    vz
    @106
    @92
    @188
    wceq
    #
    @93
    @189
    @104
    @195
    cle
    @92
    @188
    @0
    cmin
    oveq1
    @196
    @103
    @194
    csumge0
    @196
    @194
    vh
    cn
    @96
    @98
    @188
    cle
    wbr
    #
    @98
    @188
    cif
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    @103
    @194
    @201
    wceq
    @196
    @194
    vi
    cn
    @167
    @169
    @188
    cle
    wbr
    #
    @169
    @188
    cif
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    @201
    vi
    cn
    @193
    @205
    @172
    @192
    @204
    cvol
    @172
    @85
    @167
    @191
    @203
    cico
    @180
    @172
    @190
    @202
    @87
    @169
    @188
    @172
    @87
    @169
    @188
    cle
    @181
    breq1d
    @181
    ifbieq1d
    oveq12d
    fveq2d
    mpteq2ia
    vi
    vh
    cn
    @205
    @200
    @83
    @94
    wceq
    #
    @204
    @199
    cvol
    @206
    @167
    @96
    @203
    @198
    cico
    @206
    cZ
    @166
    @95
    @83
    @94
    cC
    fveq2
    fveq1d
    @206
    @202
    @197
    @169
    @98
    @188
    @206
    @169
    @98
    @188
    cle
    @206
    cZ
    @168
    @97
    @83
    @94
    cD
    fveq2
    fveq1d
    #
    breq1d
    @207
    ifbieq1d
    oveq12d
    fveq2d
    cbvmptv
    eqtri
    a1i
    @196
    vh
    cn
    @200
    @102
    @196
    @199
    @101
    cvol
    @196
    @198
    @100
    @96
    cico
    @196
    @100
    @198
    @196
    @99
    @197
    @92
    @188
    @98
    @92
    @188
    @98
    cle
    breq2
    @196
    id
    ifbieq2d
    eqcomd
    oveq2d
    fveq2d
    mpteq2dv
    eqtr2d
    fveq2d
    breq12d
    cbvrabv
    @108
    eqid
    hoidmv1lelem3
    @187
    breqtrd
    syl2anc
    pm2.61dan
    @12
    @4
    @13
    @10
    @19
    cle
    @12
    @4
    @113
    cvol
    cfv
    #
    @2
    @13
    cc0
    cif
    #
    @13
    wph
    @4
    @208
    wceq
    @2
    wph
    @4
    cX
    @129
    cvol
    cfv
    #
    vk
    cprod
    #
    @22
    @210
    vk
    cprod
    #
    @208
    wph
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    hoidmv1le.l
    @44
    @48
    hoidmv1le.a
    hoidmv1le.b
    hoidmvn0val
    #
    wph
    cX
    @22
    @210
    vk
    @43
    prodeq1d
    #
    wph
    @23
    @208
    cc
    wcel
    @212
    @208
    wceq
    #
    hoidmv1le.z
    wph
    @208
    wph
    @109
    @110
    @208
    cr
    wcel
    @26
    @25
    @0
    @1
    volicore
    syl2anc
    recnd
    @210
    @208
    vk
    cZ
    cV
    @55
    @129
    @113
    cvol
    @55
    @127
    @0
    @128
    @1
    cico
    @151
    @152
    oveq12d
    fveq2d
    prodsn
    syl2anc
    #
    3eqtrd
    adantr
    wph
    @208
    @209
    wceq
    #
    @2
    wph
    @109
    @110
    @217
    @26
    @25
    @0
    @1
    volico
    syl2anc
    #
    adantr
    @2
    @209
    @13
    wceq
    wph
    @2
    @13
    cc0
    iftrue
    adantl
    3eqtrd
    wph
    @10
    @19
    wceq
    @2
    wph
    @9
    @18
    csumge0
    @57
    fveq2d
    adantr
    breq12d
    mpbird
    wph
    @2
    wn
    #
    wa
    #
    @4
    cc0
    @10
    cle
    @220
    @4
    @211
    @212
    cc0
    wph
    @4
    @211
    wceq
    @219
    @213
    adantr
    wph
    @211
    @212
    wceq
    @219
    @214
    adantr
    @220
    @212
    @208
    @209
    cc0
    wph
    @215
    @219
    @216
    adantr
    wph
    @217
    @219
    @218
    adantr
    @219
    @209
    cc0
    wceq
    wph
    @2
    @13
    cc0
    iffalse
    adantl
    3eqtrd
    3eqtrd
    wph
    cc0
    @10
    cle
    wbr
    @219
    wph
    @9
    cvv
    cn
    @31
    wph
    nnex
    a1i
    @81
    sge0ge0
    adantr
    eqbrtrd
    pm2.61dan
end
