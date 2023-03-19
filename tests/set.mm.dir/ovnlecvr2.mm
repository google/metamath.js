include "c0.mm"
include "wceq.mm"
include "covoln.mm"
include "cfv.mm"
include "cn.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "adantl.mm"
include "cico.mm"
include "cixp.mm"
include "ciun.mm"
include "cr.mm"
include "cmap.mm"
include "wss.mm"
include "adantr.mm"
include "csn.mm"
include "wne.mm"
include "c1.mm"
include "wcel.mm"
include "1nn.mm"
include "ne0i.mm"
include "ax-mp.mm"
include "a1i.mm"
include "iunconst.mm"
include "syl.mm"
include "ixpeq1.mm"
include "ixp0x.mm"
include "eqtrd.mm"
include "iuneq2dv.mm"
include "cvv.mm"
include "reex.mm"
include "mapdm0.mm"
include "3eqtr4d.mm"
include "sseqtrd.mm"
include "ovn0val.mm"
include "nfv.mm"
include "nnex.mm"
include "cpnf.mm"
include "cicc.mm"
include "icossicc.mm"
include "cfn.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "hoidmvcl.mm"
include "sseldi.mm"
include "sge0ge0mpt.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "simpl.mm"
include "neqne.mm"
include "ccom.mm"
include "cvol.mm"
include "cprod.mm"
include "cxp.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "simpr.mm"
include "wral.mm"
include "rexrd.mm"
include "icossre.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "ss2ixp.mm"
include "ixpconstg.mm"
include "iunss.mm"
include "sylibr.mm"
include "sstrd.mm"
include "eqid.mm"
include "ovnn0val.mm"
include "ssrab2.mm"
include "sge0xrclmpt.mm"
include "cop.mm"
include "opelxpi.mm"
include "fmptd.mm"
include "wb.mm"
include "xpex.mm"
include "elmapg.mm"
include "mpbird.mm"
include "ovexd.mm"
include "c1st.mm"
include "c2nd.mm"
include "mptexg.mm"
include "fvmpt2.mm"
include "coeq2d.mm"
include "fvovco.mm"
include "opex.mm"
include "fveq2d.mm"
include "fvex.mm"
include "op1stg.mm"
include "mp2an.mm"
include "op2nd.mm"
include "oveq12d.mm"
include "adantlr.mm"
include "3eqtrrd.mm"
include "ixpeq2dva.mm"
include "eqidd.mm"
include "hoidmvn0val.mm"
include "mpteq2dva.mm"
include "eqcomd.mm"
include "prodeq2dv.mm"
include "jca.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfeq.mm"
include "nfmpt.mm"
include "fveq1.mm"
include "ixpeq2d.mm"
include "iuneq2df.mm"
include "sseq2d.mm"
include "nfan.mm"
include "wi.mm"
include "a1d.mm"
include "ralrimi.mm"
include "prodeq2d.mm"
include "mpteq2da.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "infxrlb.mm"
include "pm2.61dan.mm"

theorem ovnlecvr2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vz: setvar z
  assume ovnlecvr2.x: |- ( ph -> X e. Fin )
  assume ovnlecvr2.c: |- ( ph -> C : NN --> ( RR ^m X ) )
  assume ovnlecvr2.d: |- ( ph -> D : NN --> ( RR ^m X ) )
  assume ovnlecvr2.s: |- ( ph -> A C_ U_ j e. NN X_ k e. X ( ( ( C ` j ) ` k ) [,) ( ( D ` j ) ` k ) ) )
  assume ovnlecvr2.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )

  disjoint C a
  disjoint C b
  disjoint C k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint D a
  disjoint D b
  disjoint D k
  disjoint X a
  disjoint X b
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint a j
  disjoint a x
  disjoint b j
  disjoint b x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint a ph
  disjoint b ph
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A i
  disjoint A z
  disjoint i z
  disjoint C i
  disjoint C z
  disjoint i k
  disjoint k z
  disjoint D i
  disjoint D z
  disjoint L i
  disjoint L z
  disjoint X i
  disjoint X z
  disjoint i j
  disjoint j z
  assert |- ( ph -> ( ( voln* ` X ) ` A ) <_ ( sum^ ` ( j e. NN |-> ( ( C ` j ) ( L ` X ) ( D ` j ) ) ) ) )

  proof
    wph
    cX
    c0
    wceq
    #
    cA
    cX
    covoln
    cfv
    #
    cfv
    #
    vj
    cn
    vj
    cv
    #
    cC
    cfv
    #
    @3
    cD
    cfv
    #
    cX
    cL
    cfv
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
    @0
    wa
    #
    @2
    cc0
    @8
    cle
    @10
    @2
    cA
    c0
    covoln
    cfv
    #
    cfv
    #
    cc0
    @0
    @2
    @12
    wceq
    wph
    @0
    cA
    @1
    @11
    cX
    c0
    covoln
    fveq2
    fveq1d
    adantl
    @10
    cA
    @10
    cA
    vj
    cn
    vk
    cX
    vk
    cv
    #
    @4
    cfv
    #
    @13
    @5
    cfv
    #
    cico
    co
    #
    cixp
    #
    ciun
    #
    cr
    c0
    cmap
    co
    #
    wph
    cA
    @18
    wss
    @0
    ovnlecvr2.s
    adantr
    @10
    vj
    cn
    c0
    csn
    #
    ciun
    #
    @20
    @18
    @19
    wph
    @21
    @20
    wceq
    #
    @0
    wph
    cn
    c0
    wne
    #
    @22
    @23
    wph
    c1
    cn
    wcel
    @23
    1nn
    cn
    c1
    ne0i
    ax-mp
    a1i
    vj
    cn
    @20
    iunconst
    syl
    adantr
    @0
    @18
    @21
    wceq
    wph
    @0
    vj
    cn
    @17
    @20
    @0
    @17
    @20
    wceq
    @3
    cn
    wcel
    #
    @0
    @17
    vk
    c0
    @16
    cixp
    #
    @20
    vk
    cX
    c0
    @16
    ixpeq1
    @25
    @20
    wceq
    @0
    vk
    @16
    ixp0x
    a1i
    eqtrd
    adantr
    iuneq2dv
    adantl
    @19
    @20
    wceq
    #
    @10
    cr
    cvv
    wcel
    #
    @26
    reex
    cr
    cvv
    mapdm0
    ax-mp
    a1i
    3eqtr4d
    sseqtrd
    ovn0val
    eqtrd
    wph
    cc0
    @8
    cle
    wbr
    @0
    wph
    cn
    @6
    vj
    cvv
    wph
    vj
    nfv
    #
    cn
    cvv
    wcel
    #
    wph
    nnex
    a1i
    #
    wph
    @24
    wa
    #
    cc0
    cpnf
    cico
    co
    cc0
    cpnf
    cicc
    co
    @6
    cc0
    cpnf
    icossicc
    @31
    vx
    @4
    @5
    vk
    cL
    cX
    va
    vb
    ovnlecvr2.l
    wph
    cX
    cfn
    wcel
    #
    @24
    ovnlecvr2.x
    adantr
    #
    @31
    @4
    cr
    cX
    cmap
    co
    #
    wcel
    cX
    cr
    @4
    wf
    #
    wph
    cn
    @34
    @3
    cC
    ovnlecvr2.c
    ffvelrnda
    @4
    cr
    cX
    elmapi
    syl
    #
    @31
    @5
    @34
    wcel
    cX
    cr
    @5
    wf
    #
    wph
    cn
    @34
    @3
    cD
    ovnlecvr2.d
    ffvelrnda
    @5
    cr
    cX
    elmapi
    syl
    #
    hoidmvcl
    sseldi
    #
    sge0ge0mpt
    adantr
    eqbrtrd
    wph
    @0
    wn
    #
    wa
    wph
    cX
    c0
    wne
    #
    @9
    wph
    @40
    simpl
    @40
    @41
    wph
    cX
    c0
    neqne
    adantl
    wph
    @41
    wa
    #
    @2
    cA
    vj
    cn
    vk
    cX
    @13
    cico
    @3
    vi
    cv
    #
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
    vz
    cv
    #
    vj
    cn
    cX
    @46
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
    vz
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    @8
    cle
    @42
    vz
    cA
    vi
    vj
    vk
    @61
    cX
    wph
    @32
    @41
    ovnlecvr2.x
    adantr
    #
    wph
    @41
    simpr
    #
    wph
    cA
    @34
    wss
    @41
    wph
    cA
    @18
    @34
    ovnlecvr2.s
    wph
    @17
    @34
    wss
    #
    vj
    cn
    wral
    @18
    @34
    wss
    wph
    @65
    vj
    cn
    @31
    @17
    vk
    cX
    cr
    cixp
    #
    @34
    @31
    @16
    cr
    wss
    #
    vk
    cX
    wral
    @17
    @66
    wss
    @31
    @67
    vk
    cX
    @31
    @13
    cX
    wcel
    #
    wa
    #
    @14
    cr
    wcel
    #
    @15
    cxr
    wcel
    @67
    @31
    cX
    cr
    @13
    @4
    @36
    ffvelrnda
    #
    @69
    @15
    @31
    cX
    cr
    @13
    @5
    @38
    ffvelrnda
    #
    rexrd
    @14
    @15
    icossre
    syl2anc
    ralrimiva
    vk
    cX
    @16
    cr
    ss2ixp
    syl
    wph
    @66
    @34
    wceq
    #
    @24
    wph
    @32
    @27
    @73
    ovnlecvr2.x
    @27
    wph
    reex
    a1i
    vk
    cX
    cr
    cfn
    cvv
    ixpconstg
    syl2anc
    adantr
    sseqtrd
    ralrimiva
    vj
    cn
    @17
    @34
    iunss
    sylibr
    sstrd
    adantr
    @61
    eqid
    ovnn0val
    @42
    @61
    cxr
    wss
    #
    @8
    @61
    wcel
    #
    @62
    @8
    cle
    wbr
    @74
    @42
    @60
    vz
    cxr
    ssrab2
    a1i
    @42
    @8
    cxr
    wcel
    #
    @49
    @8
    @54
    wceq
    #
    wa
    #
    vi
    @59
    wrex
    #
    wa
    @75
    @42
    @76
    @79
    wph
    @76
    @41
    wph
    vj
    cn
    @6
    cvv
    @28
    @30
    @39
    sge0xrclmpt
    adantr
    @42
    vj
    cn
    vk
    cX
    @14
    @15
    cop
    #
    cmpt
    #
    cmpt
    #
    @59
    wcel
    #
    cA
    vj
    cn
    vk
    cX
    @13
    cico
    @3
    @82
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
    @8
    vj
    cn
    cX
    @86
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
    @79
    wph
    @83
    @41
    wph
    @83
    cn
    @58
    @82
    wf
    #
    wph
    vj
    cn
    @81
    @58
    @82
    @31
    @81
    @58
    wcel
    #
    cX
    @57
    @81
    wf
    #
    @31
    vk
    cX
    @80
    @57
    @81
    @69
    @70
    @15
    cr
    wcel
    @80
    @57
    wcel
    @71
    @72
    @14
    @15
    cr
    cr
    opelxpi
    syl2anc
    @81
    eqid
    #
    fmptd
    #
    @31
    @57
    cvv
    wcel
    #
    @32
    @97
    @98
    wb
    @101
    @31
    cr
    cr
    reex
    reex
    xpex
    a1i
    @33
    @57
    cX
    @81
    cvv
    cfn
    elmapg
    syl2anc
    mpbird
    @82
    eqid
    #
    fmptd
    wph
    @58
    cvv
    wcel
    @29
    @83
    @96
    wb
    wph
    @57
    cX
    cmap
    ovexd
    @30
    @58
    cn
    @82
    cvv
    cvv
    elmapg
    syl2anc
    mpbird
    adantr
    @42
    @89
    @94
    wph
    @89
    @41
    wph
    cA
    @18
    @88
    ovnlecvr2.s
    wph
    vj
    cn
    @17
    @87
    @31
    vk
    cX
    @16
    @86
    @69
    @86
    @13
    cico
    @81
    ccom
    #
    cfv
    #
    @13
    @81
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
    @16
    @31
    @86
    @104
    wceq
    @68
    @31
    @13
    @85
    @103
    @31
    @84
    @81
    cico
    @31
    @24
    @81
    cvv
    wcel
    #
    @84
    @81
    wceq
    wph
    @24
    simpr
    wph
    @109
    @24
    wph
    @32
    @109
    ovnlecvr2.x
    vk
    cX
    @80
    cfn
    mptexg
    syl
    adantr
    vj
    cn
    @81
    cvv
    @82
    @102
    fvmpt2
    syl2anc
    coeq2d
    fveq1d
    adantr
    @69
    @81
    cico
    cr
    cr
    cX
    @13
    @31
    @98
    @68
    @100
    adantr
    @31
    @68
    simpr
    fvovco
    wph
    @68
    @108
    @16
    wceq
    @24
    wph
    @68
    wa
    #
    @106
    @14
    @107
    @15
    cico
    @110
    @106
    @80
    c1st
    cfv
    #
    @14
    @110
    @105
    @80
    c1st
    @110
    @68
    @80
    cvv
    wcel
    #
    @105
    @80
    wceq
    wph
    @68
    simpr
    @112
    @110
    @14
    @15
    opex
    a1i
    vk
    cX
    @80
    cvv
    @81
    @99
    fvmpt2
    syl2anc
    #
    fveq2d
    @111
    @14
    wceq
    #
    @110
    @14
    cvv
    wcel
    @15
    cvv
    wcel
    @114
    @13
    @4
    fvex
    #
    @13
    @5
    fvex
    #
    @14
    @15
    cvv
    cvv
    op1stg
    mp2an
    a1i
    eqtrd
    @110
    @107
    @80
    c2nd
    cfv
    #
    @15
    @110
    @105
    @80
    c2nd
    @113
    fveq2d
    @117
    @15
    wceq
    @110
    @14
    @15
    @115
    @116
    op2nd
    a1i
    eqtrd
    oveq12d
    adantlr
    3eqtrrd
    #
    ixpeq2dva
    iuneq2dv
    sseqtrd
    adantr
    @42
    vj
    cn
    cX
    @16
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
    @122
    @8
    @93
    @42
    @122
    eqidd
    @42
    @7
    @121
    csumge0
    @42
    vj
    cn
    @6
    @120
    @42
    @24
    wa
    vx
    @4
    @5
    vk
    cL
    cX
    va
    vb
    ovnlecvr2.l
    @42
    @32
    @24
    @63
    adantr
    @42
    @41
    @24
    @64
    adantr
    wph
    @24
    @35
    @41
    @36
    adantlr
    wph
    @24
    @37
    @41
    @38
    adantlr
    hoidmvn0val
    mpteq2dva
    fveq2d
    wph
    @93
    @122
    wceq
    @41
    wph
    @92
    @121
    csumge0
    wph
    vj
    cn
    @91
    @120
    @31
    cX
    @90
    @119
    vk
    @69
    @86
    @16
    cvol
    @69
    @16
    @86
    @118
    eqcomd
    fveq2d
    prodeq2dv
    mpteq2dva
    fveq2d
    adantr
    3eqtr4d
    jca
    @78
    @95
    vi
    @82
    @59
    @43
    @82
    wceq
    #
    @49
    @89
    @77
    @94
    @123
    @48
    @88
    cA
    @123
    vj
    cn
    @47
    @87
    vj
    @43
    @82
    vj
    @43
    nfcv
    vj
    cn
    @81
    nfmpt1
    nfeq
    #
    @123
    @47
    @87
    wceq
    @24
    @123
    vk
    cX
    @46
    @86
    vk
    @43
    @82
    vk
    @43
    nfcv
    vk
    vj
    cn
    @81
    vk
    cn
    nfcv
    vk
    cX
    @80
    nfmpt1
    nfmpt
    nfeq
    #
    @123
    @46
    @86
    wceq
    @68
    @123
    @13
    @45
    @85
    @123
    @44
    @84
    cico
    @3
    @43
    @82
    fveq1
    coeq2d
    fveq1d
    #
    adantr
    ixpeq2d
    adantr
    iuneq2df
    sseq2d
    @123
    @54
    @93
    @8
    @123
    @53
    @92
    csumge0
    @123
    vj
    cn
    @52
    @91
    @124
    @123
    @24
    wa
    #
    cX
    @51
    @90
    vk
    @127
    @51
    @90
    wceq
    #
    vk
    cX
    @123
    @24
    vk
    @125
    @24
    vk
    nfv
    nfan
    @123
    @68
    @128
    wi
    @24
    @123
    @128
    @68
    @123
    @46
    @86
    cvol
    @126
    fveq2d
    a1d
    adantr
    ralrimi
    prodeq2d
    mpteq2da
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl2anc
    jca
    @60
    @79
    vz
    @8
    cxr
    @50
    @8
    wceq
    #
    @56
    @78
    vi
    @59
    @129
    @55
    @77
    @49
    @50
    @8
    @54
    eqeq1
    anbi2d
    rexbidv
    elrab
    sylibr
    @61
    @8
    infxrlb
    syl2anc
    eqbrtrd
    syl2anc
    pm2.61dan
end
