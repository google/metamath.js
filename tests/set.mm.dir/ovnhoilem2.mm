include "cfv.mm"
include "co.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "covoln.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "cico.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wceq.mm"
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "wrex.mm"
include "crab.mm"
include "eleq2i.mm"
include "rabid.mm"
include "bitri.mm"
include "biimpi.mm"
include "simprd.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "cfn.mm"
include "3ad2ant1.mm"
include "wf.mm"
include "c1st.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "syl.mm"
include "xp1st.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "reex.mm"
include "a1i.mm"
include "c1.mm"
include "1nn.mm"
include "ffvelrnd.mm"
include "elmapex.mm"
include "adantr.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "id.mm"
include "nnex.mm"
include "mptex.mm"
include "fvmpt2.mm"
include "feq1d.mm"
include "3ad2ant2.mm"
include "c2nd.mm"
include "xp2nd.mm"
include "simp3.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "ixpeq2dv.mm"
include "cbviunv.mm"
include "simpr.mm"
include "fvovco.mm"
include "ixpeq2dva.mm"
include "iuneq2dv.mm"
include "simpl.mm"
include "mptexg.mm"
include "eqtrd.mm"
include "eqidd.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "adantlr.mm"
include "3eqtr4d.mm"
include "3adant3.mm"
include "sseq12d.mm"
include "mpbid.mm"
include "3adant3r.mm"
include "hoidmvle.mm"
include "mpteq2dva.mm"
include "prodeq2dv.mm"
include "cbvmptv.mm"
include "eqcomd.mm"
include "adantll.mm"
include "ad2antrr.mm"
include "c0.mm"
include "wne.mm"
include "adantlll.mm"
include "hoidmvn0val.mm"
include "3adant3l.mm"
include "breqtrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cc0.mm"
include "cpnf.mm"
include "icossxr.mm"
include "hoidmvcl.mm"
include "sseldi.mm"
include "infxrgelb.mm"
include "nfv.mm"
include "rexrd.mm"
include "hoissrrn2.mm"
include "eqsstrd.mm"
include "ovnn0val.mm"

theorem ovnhoilem2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cI: class I
  let cL: class L
  let cM: class M
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vl: setvar l
  assume ovnhoilem2.x: |- ( ph -> X e. Fin )
  assume ovnhoilem2.n: |- ( ph -> X =/= (/) )
  assume ovnhoilem2.a: |- ( ph -> A : X --> RR )
  assume ovnhoilem2.b: |- ( ph -> B : X --> RR )
  assume ovnhoilem2.i: |- I = X_ k e. X ( ( A ` k ) [,) ( B ` k ) )
  assume ovnhoilem2.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume ovnhoilem2.m: |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( I C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) }
  assume ovnhoilem2.f: |- F = ( i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) |-> ( n e. NN |-> ( l e. X |-> ( 1st ` ( ( i ` n ) ` l ) ) ) ) )
  assume ovnhoilem2.s: |- S = ( i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) |-> ( n e. NN |-> ( l e. X |-> ( 2nd ` ( ( i ` n ) ` l ) ) ) ) )

  disjoint A a
  disjoint A b
  disjoint A i
  disjoint A k
  disjoint A z
  disjoint a b
  disjoint a i
  disjoint a k
  disjoint a z
  disjoint b i
  disjoint b k
  disjoint b z
  disjoint i k
  disjoint i z
  disjoint k z
  disjoint B a
  disjoint B b
  disjoint B i
  disjoint B k
  disjoint B z
  disjoint F k
  disjoint F n
  disjoint k n
  disjoint I a
  disjoint I b
  disjoint I i
  disjoint I n
  disjoint I x
  disjoint I z
  disjoint a n
  disjoint a x
  disjoint b n
  disjoint b x
  disjoint i n
  disjoint i x
  disjoint n x
  disjoint n z
  disjoint x z
  disjoint L a
  disjoint L b
  disjoint L i
  disjoint L n
  disjoint L x
  disjoint L z
  disjoint M i
  disjoint M z
  disjoint S k
  disjoint S n
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X l
  disjoint X n
  disjoint a j
  disjoint a l
  disjoint b j
  disjoint b l
  disjoint i j
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint j n
  disjoint k l
  disjoint l n
  disjoint X x
  disjoint X z
  disjoint j x
  disjoint j z
  disjoint k x
  disjoint a ph
  disjoint b ph
  disjoint i ph
  disjoint k ph
  disjoint l ph
  disjoint n ph
  disjoint ph x
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( A ( L ` X ) B ) <_ ( ( voln* ` X ) ` I ) )

  proof
    wph
    cA
    cB
    cX
    cL
    cfv
    #
    co
    #
    cM
    cxr
    clt
    cinf
    #
    cI
    cX
    covoln
    cfv
    cfv
    #
    cle
    wph
    @1
    @2
    cle
    wbr
    #
    @1
    vz
    cv
    #
    cle
    wbr
    #
    vz
    cM
    wral
    #
    wph
    @6
    vz
    cM
    wph
    @5
    cM
    wcel
    #
    wa
    #
    cI
    vj
    cn
    vk
    cX
    vk
    cv
    #
    cico
    vj
    cv
    #
    vi
    cv
    #
    cfv
    #
    ccom
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    @5
    vj
    cn
    cX
    @14
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vi
    cr
    cr
    cxp
    #
    cX
    cmap
    co
    #
    cn
    cmap
    co
    #
    wrex
    #
    @6
    @8
    @27
    wph
    @8
    @5
    cxr
    wcel
    #
    @27
    @8
    @28
    @27
    wa
    #
    @8
    @5
    @27
    vz
    cxr
    crab
    #
    wcel
    @29
    cM
    @30
    @5
    ovnhoilem2.m
    eleq2i
    @27
    vz
    cxr
    rabid
    bitri
    biimpi
    simprd
    adantl
    @9
    @23
    @6
    vi
    @26
    wph
    @12
    @26
    wcel
    #
    @23
    @6
    wi
    wi
    @8
    wph
    @31
    @23
    @6
    wph
    @31
    @23
    w3a
    #
    @1
    vn
    cn
    vn
    cv
    #
    @12
    cF
    cfv
    #
    cfv
    #
    @33
    @12
    cS
    cfv
    #
    cfv
    #
    @0
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    @5
    cle
    @32
    vx
    cA
    cB
    @34
    @36
    vn
    vk
    cL
    cX
    va
    vb
    ovnhoilem2.l
    wph
    @31
    cX
    cfn
    wcel
    #
    @23
    ovnhoilem2.x
    3ad2ant1
    wph
    @31
    cX
    cr
    cA
    wf
    @23
    ovnhoilem2.a
    3ad2ant1
    wph
    @31
    cX
    cr
    cB
    wf
    @23
    ovnhoilem2.b
    3ad2ant1
    @31
    wph
    cn
    cr
    cX
    cmap
    co
    #
    @34
    wf
    #
    @23
    @31
    @43
    cn
    @42
    vn
    cn
    vl
    cX
    vl
    cv
    #
    @33
    @12
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
    #
    wf
    @31
    vn
    cn
    @48
    @42
    @49
    @31
    @33
    cn
    wcel
    #
    wa
    #
    @48
    @42
    wcel
    #
    cX
    cr
    @48
    wf
    #
    @51
    vl
    cX
    @47
    cr
    @48
    @51
    @44
    cX
    wcel
    #
    wa
    #
    @46
    @24
    wcel
    #
    @47
    cr
    wcel
    #
    @51
    cX
    @24
    @44
    @45
    @51
    @45
    @25
    wcel
    cX
    @24
    @45
    wf
    @31
    cn
    @25
    @33
    @12
    @12
    @25
    cn
    elmapi
    #
    ffvelrnda
    @45
    @24
    cX
    elmapi
    syl
    ffvelrnda
    #
    @46
    cr
    cr
    xp1st
    #
    syl
    @48
    eqid
    #
    fmptd
    @51
    cr
    cvv
    wcel
    #
    cX
    cvv
    wcel
    #
    @52
    @53
    wb
    @62
    @51
    reex
    a1i
    #
    @31
    @63
    @50
    @31
    c1
    @12
    cfv
    #
    @25
    wcel
    #
    @63
    @31
    cn
    @25
    c1
    @12
    @58
    c1
    cn
    wcel
    @31
    1nn
    a1i
    ffvelrnd
    @66
    @24
    cvv
    wcel
    @63
    @65
    @24
    cX
    elmapex
    simprd
    syl
    #
    adantr
    #
    cr
    cX
    @48
    cvv
    cvv
    elmapg
    syl2anc
    mpbird
    @49
    eqid
    #
    fmptd
    @31
    cn
    @42
    @34
    @49
    @31
    @31
    @49
    cvv
    wcel
    #
    @34
    @49
    wceq
    #
    @31
    id
    #
    @70
    @31
    vn
    cn
    @48
    nnex
    mptex
    #
    a1i
    vi
    @26
    @49
    cvv
    cF
    ovnhoilem2.f
    fvmpt2
    #
    syl2anc
    feq1d
    mpbird
    3ad2ant2
    @31
    wph
    cn
    @42
    @36
    wf
    #
    @23
    @31
    @75
    cn
    @42
    vn
    cn
    vl
    cX
    @46
    c2nd
    cfv
    #
    cmpt
    #
    cmpt
    #
    wf
    @31
    vn
    cn
    @77
    @42
    @78
    @51
    @77
    @42
    wcel
    #
    cX
    cr
    @77
    wf
    #
    @51
    vl
    cX
    @76
    cr
    @77
    @55
    @56
    @76
    cr
    wcel
    #
    @59
    @46
    cr
    cr
    xp2nd
    #
    syl
    @77
    eqid
    #
    fmptd
    @51
    @62
    @63
    @79
    @80
    wb
    @64
    @68
    cr
    cX
    @77
    cvv
    cvv
    elmapg
    syl2anc
    mpbird
    @78
    eqid
    #
    fmptd
    @31
    cn
    @42
    @36
    @78
    @31
    @31
    @78
    cvv
    wcel
    #
    @36
    @78
    wceq
    @72
    @85
    @31
    vn
    cn
    @77
    nnex
    mptex
    a1i
    vi
    @26
    @78
    cvv
    cS
    ovnhoilem2.s
    fvmpt2
    syl2anc
    #
    feq1d
    mpbird
    3ad2ant2
    wph
    @31
    @17
    vk
    cX
    @10
    cA
    cfv
    #
    @10
    cB
    cfv
    #
    cico
    co
    cixp
    #
    vn
    cn
    vk
    cX
    @10
    @35
    cfv
    #
    @10
    @37
    cfv
    #
    cico
    co
    #
    cixp
    #
    ciun
    #
    wss
    #
    @22
    wph
    @31
    @17
    w3a
    #
    @17
    @95
    wph
    @31
    @17
    simp3
    @96
    cI
    @89
    @16
    @94
    cI
    @89
    wceq
    #
    @96
    ovnhoilem2.i
    a1i
    wph
    @31
    @16
    @94
    wceq
    #
    @17
    @31
    @98
    wph
    @31
    vj
    cn
    vk
    cX
    @10
    @13
    cfv
    #
    c1st
    cfv
    #
    @99
    c2nd
    cfv
    #
    cico
    co
    #
    cixp
    #
    ciun
    #
    vn
    cn
    vk
    cX
    @10
    @45
    cfv
    #
    c1st
    cfv
    #
    @105
    c2nd
    cfv
    #
    cico
    co
    #
    cixp
    #
    ciun
    #
    @16
    @94
    @104
    @110
    wceq
    @31
    vj
    vn
    cn
    @103
    @109
    @11
    @33
    wceq
    #
    vk
    cX
    @102
    @108
    @111
    @100
    @106
    @101
    @107
    cico
    @111
    @99
    @105
    c1st
    @111
    @10
    @13
    @45
    @11
    @33
    @12
    fveq2
    fveq1d
    #
    fveq2d
    @111
    @99
    @105
    c2nd
    @112
    fveq2d
    oveq12d
    ixpeq2dv
    cbviunv
    a1i
    @31
    vj
    cn
    @15
    @103
    @31
    @11
    cn
    wcel
    wa
    #
    vk
    cX
    @14
    @102
    @113
    @10
    cX
    wcel
    #
    wa
    #
    @13
    cico
    cr
    cr
    cX
    @10
    @113
    cX
    @24
    @13
    wf
    #
    @114
    @113
    @13
    @25
    wcel
    @116
    @31
    cn
    @25
    @11
    @12
    @58
    ffvelrnda
    @13
    @24
    cX
    elmapi
    syl
    adantr
    @113
    @114
    simpr
    fvovco
    #
    ixpeq2dva
    iuneq2dv
    @31
    vn
    cn
    @93
    @109
    @51
    vk
    cX
    @92
    @108
    @51
    @114
    wa
    #
    @90
    @106
    @91
    @107
    cico
    @118
    @90
    @10
    @48
    cfv
    #
    @106
    @51
    @90
    @119
    wceq
    @114
    @51
    @10
    @35
    @48
    @51
    @35
    @33
    @49
    cfv
    #
    @48
    @51
    @33
    @34
    @49
    @51
    @31
    @70
    @71
    @31
    @50
    simpl
    @70
    @51
    @73
    a1i
    @74
    syl2anc
    fveq1d
    @51
    @50
    @48
    cvv
    wcel
    #
    @120
    @48
    wceq
    @31
    @50
    simpr
    #
    @31
    @121
    @50
    @31
    @63
    @121
    @67
    vl
    cX
    @47
    cvv
    mptexg
    syl
    adantr
    vn
    cn
    @48
    cvv
    @49
    @69
    fvmpt2
    syl2anc
    eqtrd
    #
    fveq1d
    adantr
    @31
    @114
    @119
    @106
    wceq
    @50
    @31
    @114
    wa
    #
    vl
    @10
    @47
    @106
    cX
    @48
    cvv
    @124
    @48
    eqidd
    @124
    @44
    @10
    wceq
    #
    wa
    #
    @46
    @105
    c1st
    @126
    @44
    @10
    @45
    @124
    @125
    simpr
    fveq2d
    fveq2d
    @31
    @114
    simpr
    #
    @124
    @105
    c1st
    fvexd
    fvmptd
    adantlr
    eqtrd
    @118
    @91
    @10
    @77
    cfv
    #
    @107
    @51
    @91
    @128
    wceq
    @114
    @51
    @10
    @37
    @77
    @51
    @37
    @33
    @78
    cfv
    #
    @77
    @31
    @37
    @129
    wceq
    @50
    @31
    @33
    @36
    @78
    @86
    fveq1d
    adantr
    @51
    @50
    @77
    cvv
    wcel
    #
    @129
    @77
    wceq
    @122
    @31
    @130
    @50
    @31
    @63
    @130
    @67
    vl
    cX
    @76
    cvv
    mptexg
    syl
    adantr
    vn
    cn
    @77
    cvv
    @78
    @84
    fvmpt2
    syl2anc
    eqtrd
    #
    fveq1d
    adantr
    @31
    @114
    @128
    @107
    wceq
    @50
    @124
    vl
    @10
    @76
    @107
    cX
    @77
    cvv
    @124
    @77
    eqidd
    @125
    @76
    @107
    wceq
    @124
    @125
    @46
    @105
    c2nd
    @44
    @10
    @45
    fveq2
    fveq2d
    adantl
    @127
    @124
    @105
    c2nd
    fvexd
    fvmptd
    adantlr
    eqtrd
    oveq12d
    ixpeq2dva
    iuneq2dv
    3eqtr4d
    adantl
    3adant3
    sseq12d
    mpbid
    3adant3r
    hoidmvle
    wph
    @31
    @22
    @40
    @5
    wceq
    @17
    wph
    @31
    @22
    w3a
    vn
    cn
    cX
    @119
    @128
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    @21
    @40
    @5
    @31
    wph
    @136
    @21
    wceq
    @22
    @31
    @135
    @20
    csumge0
    @31
    @135
    vj
    cn
    cX
    @102
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    @20
    @135
    @139
    wceq
    @31
    vn
    vj
    cn
    @134
    @138
    @33
    @11
    wceq
    #
    cX
    @133
    @137
    vk
    @140
    @114
    wa
    #
    @132
    @102
    cvol
    @141
    @119
    @100
    @128
    @101
    cico
    @141
    @119
    @10
    vl
    cX
    @44
    @13
    cfv
    #
    c1st
    cfv
    #
    cmpt
    #
    cfv
    #
    @100
    @140
    @119
    @145
    wceq
    @114
    @140
    @10
    @48
    @144
    @140
    vl
    cX
    @47
    @143
    @140
    @54
    wa
    #
    @46
    @142
    c1st
    @146
    @44
    @45
    @13
    @146
    @33
    @11
    @12
    @140
    @54
    simpl
    fveq2d
    fveq1d
    #
    fveq2d
    mpteq2dva
    fveq1d
    adantr
    @114
    @145
    @100
    wceq
    @140
    @114
    vl
    @10
    @143
    @100
    cX
    @144
    cvv
    @114
    @144
    eqidd
    @125
    @143
    @100
    wceq
    @114
    @125
    @142
    @99
    c1st
    @44
    @10
    @13
    fveq2
    #
    fveq2d
    adantl
    @114
    id
    #
    @114
    @99
    c1st
    fvexd
    fvmptd
    adantl
    eqtrd
    @141
    @128
    @10
    vl
    cX
    @142
    c2nd
    cfv
    #
    cmpt
    #
    cfv
    #
    @101
    @140
    @128
    @152
    wceq
    @114
    @140
    @10
    @77
    @151
    @140
    vl
    cX
    @76
    @150
    @146
    @46
    @142
    c2nd
    @147
    fveq2d
    mpteq2dva
    fveq1d
    adantr
    @114
    @152
    @101
    wceq
    @140
    @114
    vl
    @10
    @150
    @101
    cX
    @151
    cvv
    @114
    @151
    eqidd
    @125
    @150
    @101
    wceq
    @114
    @125
    @142
    @99
    c2nd
    @148
    fveq2d
    adantl
    @149
    @114
    @99
    c2nd
    fvexd
    fvmptd
    adantl
    eqtrd
    oveq12d
    fveq2d
    prodeq2dv
    cbvmptv
    a1i
    @31
    vj
    cn
    @138
    @19
    @113
    cX
    @137
    @18
    vk
    @115
    @102
    @14
    cvol
    @115
    @14
    @102
    @117
    eqcomd
    fveq2d
    prodeq2dv
    mpteq2dva
    eqtrd
    fveq2d
    3ad2ant2
    wph
    @31
    @40
    @136
    wceq
    @22
    wph
    @31
    wa
    #
    @39
    @135
    csumge0
    @153
    vn
    cn
    @38
    @134
    @153
    @50
    wa
    #
    @38
    @48
    @77
    @0
    co
    @134
    @154
    @35
    @48
    @37
    @77
    @0
    @31
    @50
    @35
    @48
    wceq
    wph
    @123
    adantll
    @31
    @50
    @37
    @77
    wceq
    wph
    @131
    adantll
    oveq12d
    @154
    vx
    @48
    @77
    vk
    cL
    cX
    va
    vb
    ovnhoilem2.l
    wph
    @41
    @31
    @50
    ovnhoilem2.x
    ad2antrr
    wph
    cX
    c0
    wne
    @31
    @50
    ovnhoilem2.n
    ad2antrr
    @154
    vl
    cX
    @47
    cr
    @48
    @154
    @54
    wa
    #
    @56
    @57
    @31
    @50
    @54
    @56
    wph
    @59
    adantlll
    #
    @60
    syl
    @61
    fmptd
    @154
    vl
    cX
    @76
    cr
    @77
    @155
    @56
    @81
    @156
    @82
    syl
    @83
    fmptd
    hoidmvn0val
    eqtrd
    mpteq2dva
    fveq2d
    3adant3
    wph
    @31
    @22
    simp3
    3eqtr4d
    3adant3l
    breqtrd
    3exp
    adantr
    rexlimdv
    mpd
    ralrimiva
    wph
    cM
    cxr
    wss
    #
    @1
    cxr
    wcel
    @4
    @7
    wb
    @157
    wph
    cM
    @30
    cxr
    ovnhoilem2.m
    @27
    vz
    cxr
    ssrab2
    eqsstri
    a1i
    wph
    cc0
    cpnf
    cico
    co
    cxr
    @1
    cc0
    cpnf
    icossxr
    wph
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    ovnhoilem2.l
    ovnhoilem2.x
    ovnhoilem2.a
    ovnhoilem2.b
    hoidmvcl
    sseldi
    vz
    cM
    @1
    infxrgelb
    syl2anc
    mpbird
    wph
    @3
    @2
    wph
    vz
    cI
    vi
    vj
    vk
    cM
    cX
    ovnhoilem2.x
    ovnhoilem2.n
    wph
    cI
    @89
    @42
    @97
    wph
    ovnhoilem2.i
    a1i
    wph
    @87
    @88
    vk
    cX
    wph
    vk
    nfv
    wph
    cX
    cr
    @10
    cA
    ovnhoilem2.a
    ffvelrnda
    wph
    @114
    wa
    @88
    wph
    cX
    cr
    @10
    cB
    ovnhoilem2.b
    ffvelrnda
    rexrd
    hoissrrn2
    eqsstrd
    ovnhoilem2.m
    ovnn0val
    eqcomd
    breqtrd
end
