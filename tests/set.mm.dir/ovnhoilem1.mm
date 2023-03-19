include "covoln.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "cvol.mm"
include "cprod.mm"
include "cle.mm"
include "cixp.mm"
include "cr.mm"
include "cmap.mm"
include "a1i.mm"
include "nfv.mm"
include "ffvelrnda.mm"
include "wcel.mm"
include "wa.mm"
include "rexrd.mm"
include "hoissrrn2.mm"
include "eqsstrd.mm"
include "ovnval2.mm"
include "wbr.mm"
include "iftrue.mm"
include "adantl.mm"
include "cpnf.mm"
include "0xr.mm"
include "pnfxr.mm"
include "hoiprodcl3.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "adantr.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "iffalse.mm"
include "wss.mm"
include "cn.mm"
include "ccom.mm"
include "ciun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cxp.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "icossxr.mm"
include "sseldi.mm"
include "wf.mm"
include "c1.mm"
include "cop.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "0re.mm"
include "mp2an.mm"
include "ifcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "cfn.mm"
include "wb.mm"
include "reex.mm"
include "xpex.mm"
include "jctil.mm"
include "elmapg.mm"
include "syl.mm"
include "mpbird.mm"
include "ovex.mm"
include "nnex.mm"
include "elmap.mm"
include "sylibr.mm"
include "eqidd.mm"
include "c1st.mm"
include "c2nd.mm"
include "mpteq2dv.mm"
include "1nn.mm"
include "mptexg.mm"
include "fvmptd.mm"
include "feq1d.mm"
include "simpr.mm"
include "fvovco.mm"
include "elexd.mm"
include "fvmpt2d.mm"
include "fveq2d.mm"
include "fvex.mm"
include "op1st.mm"
include "eqtrd.mm"
include "op2nd.mm"
include "oveq12d.mm"
include "ixpeq2dva.mm"
include "3eqtr4d.mm"
include "fveq2.mm"
include "coeq2d.mm"
include "fveq1d.mm"
include "ixpeq2dv.mm"
include "ssiun2s.mm"
include "ax-mp.mm"
include "syl6eqss.mm"
include "csn.mm"
include "eqcomd.mm"
include "prodeq2dv.mm"
include "1red.mm"
include "cicc.mm"
include "icossicc.mm"
include "hoiprodcl.mm"
include "prodeq2ad.mm"
include "sge0snmpt.mm"
include "snssi.mm"
include "ad2antrr.mm"
include "simpl.mm"
include "elsni.mm"
include "adantlr.mm"
include "cdif.mm"
include "chash.mm"
include "cexp.mm"
include "eldifi.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "elexi.mm"
include "0le0.mm"
include "ico0.mm"
include "mpbir.mm"
include "3eqtrd.mm"
include "vol0.mm"
include "cc.mm"
include "0cnd.mm"
include "fprodconst.mm"
include "wne.mm"
include "neqne.mm"
include "hashnncl.mm"
include "0exp.mm"
include "sge0ss.mm"
include "jca.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nfeq.mm"
include "fveq1.mm"
include "ixpeq2d.mm"
include "iuneq2d.mm"
include "sseq2d.mm"
include "a1d.mm"
include "ralrimi.mm"
include "prodeq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "eqcomi.mm"
include "eleqtrd.mm"
include "infxrlb.mm"
include "pm2.61dan.mm"

theorem ovnhoilem1
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cH: class H
  let cI: class I
  let cM: class M
  let cX: class X
  let vx: setvar x
  assume ovnhoilem1.x: |- ( ph -> X e. Fin )
  assume ovnhoilem1.a: |- ( ph -> A : X --> RR )
  assume ovnhoilem1.b: |- ( ph -> B : X --> RR )
  assume ovnhoilem1.c: |- I = X_ k e. X ( ( A ` k ) [,) ( B ` k ) )
  assume ovnhoilem1.m: |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( I C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) }
  assume ovnhoilem1.h: |- H = ( j e. NN |-> ( k e. X |-> if ( j = 1 , <. ( A ` k ) , ( B ` k ) >. , <. 0 , 0 >. ) ) )

  disjoint A i
  disjoint A j
  disjoint A z
  disjoint i j
  disjoint i z
  disjoint j z
  disjoint B i
  disjoint B j
  disjoint B z
  disjoint H i
  disjoint H j
  disjoint I i
  disjoint I z
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X z
  disjoint i k
  disjoint j k
  disjoint k z
  disjoint j ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ( ( voln* ` X ) ` I ) <_ prod_ k e. X ( vol ` ( ( A ` k ) [,) ( B ` k ) ) ) )

  proof
    wph
    cI
    cX
    covoln
    cfv
    cfv
    cX
    c0
    wceq
    #
    cc0
    cM
    cxr
    clt
    cinf
    #
    cif
    #
    cX
    vk
    cv
    #
    cA
    cfv
    #
    @3
    cB
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
    cle
    wph
    vz
    cI
    vi
    vj
    vk
    cM
    cX
    ovnhoilem1.x
    wph
    cI
    vk
    cX
    @6
    cixp
    #
    cr
    cX
    cmap
    co
    cI
    @9
    wceq
    wph
    ovnhoilem1.c
    a1i
    #
    wph
    @4
    @5
    vk
    cX
    wph
    vk
    nfv
    #
    wph
    cX
    cr
    @3
    cA
    ovnhoilem1.a
    ffvelrnda
    #
    wph
    @3
    cX
    wcel
    #
    wa
    #
    @5
    wph
    cX
    cr
    @3
    cB
    ovnhoilem1.b
    ffvelrnda
    #
    rexrd
    hoissrrn2
    eqsstrd
    ovnhoilem1.m
    ovnval2
    wph
    @0
    @2
    @8
    cle
    wbr
    wph
    @0
    wa
    @2
    cc0
    @8
    cle
    @0
    @2
    cc0
    wceq
    wph
    @0
    cc0
    @1
    iftrue
    adantl
    wph
    cc0
    @8
    cle
    wbr
    #
    @0
    wph
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @8
    cc0
    cpnf
    cico
    co
    #
    wcel
    @16
    @17
    wph
    0xr
    a1i
    @18
    wph
    pnfxr
    a1i
    wph
    @4
    @5
    vk
    cX
    @11
    ovnhoilem1.x
    @12
    @15
    hoiprodcl3
    #
    cc0
    cpnf
    @8
    icogelb
    syl3anc
    adantr
    eqbrtrd
    wph
    @0
    wn
    #
    wa
    #
    @2
    @1
    @8
    cle
    @21
    @2
    @1
    wceq
    wph
    @0
    cc0
    @1
    iffalse
    adantl
    @22
    cM
    cxr
    wss
    #
    @8
    cM
    wcel
    @1
    @8
    cle
    wbr
    @23
    @22
    cM
    cI
    vj
    cn
    vk
    cX
    @3
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
    @28
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
    ovnhoilem1.m
    @42
    vz
    cxr
    ssrab2
    eqsstri
    a1i
    @22
    @8
    @43
    cM
    @22
    @8
    cxr
    wcel
    #
    @31
    @8
    @36
    wceq
    #
    wa
    #
    vi
    @41
    wrex
    #
    wa
    @8
    @43
    wcel
    @22
    @44
    @47
    wph
    @44
    @21
    wph
    @19
    cxr
    @8
    cc0
    cpnf
    icossxr
    @20
    sseldi
    adantr
    @22
    cH
    @41
    wcel
    #
    cI
    vj
    cn
    vk
    cX
    @3
    cico
    @24
    cH
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
    @51
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
    @47
    wph
    @48
    @21
    wph
    cn
    @40
    cH
    wf
    @48
    wph
    vj
    cn
    vk
    cX
    @24
    c1
    wceq
    #
    @4
    @5
    cop
    #
    cc0
    cc0
    cop
    #
    cif
    #
    cmpt
    #
    @40
    cH
    wph
    @65
    @40
    wcel
    #
    @24
    cn
    wcel
    #
    wph
    @66
    cX
    @39
    @65
    wf
    #
    wph
    vk
    cX
    @64
    @39
    @65
    @14
    @61
    @62
    @63
    @39
    @14
    @4
    cr
    wcel
    @5
    cr
    wcel
    @62
    @39
    wcel
    @12
    @15
    @4
    @5
    cr
    cr
    opelxpi
    syl2anc
    #
    @63
    @39
    wcel
    #
    @14
    cc0
    cr
    wcel
    #
    @71
    @70
    0re
    0re
    cc0
    cc0
    cr
    cr
    opelxpi
    mp2an
    #
    a1i
    #
    ifcld
    @65
    eqid
    fmptd
    wph
    @39
    cvv
    wcel
    #
    cX
    cfn
    wcel
    #
    wa
    @66
    @68
    wb
    wph
    @75
    @74
    ovnhoilem1.x
    cr
    cr
    reex
    reex
    xpex
    jctil
    @39
    cX
    @65
    cvv
    cfn
    elmapg
    syl
    mpbird
    adantr
    #
    ovnhoilem1.h
    fmptd
    @40
    cn
    cH
    @39
    cX
    cmap
    ovex
    nnex
    elmap
    sylibr
    adantr
    @22
    @54
    @59
    wph
    @54
    @21
    wph
    cI
    vk
    cX
    @3
    cico
    c1
    cH
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    @53
    wph
    @9
    @9
    cI
    @80
    wph
    @9
    eqidd
    @10
    wph
    vk
    cX
    @79
    @6
    @14
    @79
    @3
    @77
    cfv
    #
    c1st
    cfv
    #
    @81
    c2nd
    cfv
    #
    cico
    co
    @6
    @14
    @77
    cico
    cr
    cr
    cX
    @3
    wph
    cX
    @39
    @77
    wf
    #
    @13
    wph
    @84
    cX
    @39
    vk
    cX
    @62
    cmpt
    #
    wf
    wph
    vk
    cX
    @62
    @39
    @85
    @69
    @85
    eqid
    fmptd
    wph
    cX
    @39
    @77
    @85
    wph
    vj
    c1
    @65
    @85
    cn
    cH
    cvv
    cH
    vj
    cn
    @65
    cmpt
    #
    wceq
    wph
    ovnhoilem1.h
    a1i
    #
    @61
    @65
    @85
    wceq
    wph
    @61
    vk
    cX
    @64
    @62
    @61
    @62
    @63
    iftrue
    mpteq2dv
    adantl
    c1
    cn
    wcel
    #
    wph
    1nn
    a1i
    wph
    @75
    @85
    cvv
    wcel
    ovnhoilem1.x
    vk
    cX
    @62
    cfn
    mptexg
    syl
    fvmptd
    #
    feq1d
    mpbird
    #
    adantr
    wph
    @13
    simpr
    fvovco
    @14
    @82
    @4
    @83
    @5
    cico
    @14
    @82
    @62
    c1st
    cfv
    #
    @4
    @14
    @81
    @62
    c1st
    wph
    vk
    cX
    @62
    @77
    cvv
    @89
    @14
    @62
    @39
    @69
    elexd
    fvmpt2d
    #
    fveq2d
    @91
    @4
    wceq
    @14
    @4
    @5
    @3
    cA
    fvex
    #
    @3
    cB
    fvex
    #
    op1st
    a1i
    eqtrd
    @14
    @83
    @62
    c2nd
    cfv
    #
    @5
    @14
    @81
    @62
    c2nd
    @92
    fveq2d
    @95
    @5
    wceq
    @14
    @4
    @5
    @93
    @94
    op2nd
    a1i
    eqtrd
    oveq12d
    eqtrd
    #
    ixpeq2dva
    3eqtr4d
    @88
    @80
    @53
    wss
    1nn
    vj
    cn
    @52
    c1
    @80
    @61
    vk
    cX
    @51
    @79
    @61
    @3
    @50
    @78
    @61
    @49
    @77
    cico
    @24
    c1
    cH
    fveq2
    #
    coeq2d
    fveq1d
    #
    ixpeq2dv
    ssiun2s
    ax-mp
    syl6eqss
    adantr
    @22
    @8
    cX
    @79
    cvol
    cfv
    #
    vk
    cprod
    #
    vj
    c1
    csn
    #
    @56
    cmpt
    csumge0
    cfv
    #
    @58
    wph
    @8
    @100
    wceq
    @21
    wph
    cX
    @7
    @99
    vk
    @14
    @99
    @7
    @14
    @79
    @6
    cvol
    @96
    fveq2d
    eqcomd
    prodeq2dv
    adantr
    wph
    @100
    @102
    wceq
    @21
    wph
    @102
    @100
    wph
    c1
    @56
    @100
    vj
    cr
    wph
    1red
    wph
    @19
    cc0
    cpnf
    cicc
    co
    #
    @100
    cc0
    cpnf
    icossicc
    #
    wph
    vk
    @77
    cX
    @11
    ovnhoilem1.x
    @90
    hoiprodcl
    sseldi
    @61
    cX
    @55
    @99
    vk
    @61
    @51
    @79
    cvol
    @98
    fveq2d
    prodeq2ad
    sge0snmpt
    eqcomd
    adantr
    @22
    @101
    cn
    @56
    vj
    cvv
    @22
    vj
    nfv
    cn
    cvv
    wcel
    @22
    nnex
    a1i
    @101
    cn
    wss
    #
    @22
    @88
    @105
    1nn
    c1
    cn
    snssi
    ax-mp
    a1i
    @22
    @24
    @101
    wcel
    #
    wa
    #
    @19
    @103
    @56
    @104
    @107
    vk
    @49
    cX
    @107
    vk
    nfv
    wph
    @75
    @21
    @106
    ovnhoilem1.x
    ad2antrr
    wph
    @106
    cX
    @39
    @49
    wf
    #
    @21
    wph
    @106
    wa
    wph
    @61
    @108
    wph
    @106
    simpl
    @106
    @61
    wph
    @24
    c1
    elsni
    adantl
    wph
    @61
    wa
    #
    @108
    @84
    wph
    @84
    @61
    @90
    adantr
    @109
    cX
    @39
    @49
    @77
    @61
    @49
    @77
    wceq
    wph
    @97
    adantl
    feq1d
    mpbird
    syl2anc
    adantlr
    hoiprodcl
    sseldi
    @22
    @24
    cn
    @101
    cdif
    wcel
    #
    wa
    @56
    cX
    cc0
    vk
    cprod
    #
    cc0
    cX
    chash
    cfv
    #
    cexp
    co
    #
    cc0
    wph
    @110
    @56
    @111
    wceq
    @21
    wph
    @110
    wa
    #
    cX
    @55
    cc0
    vk
    @114
    @13
    wa
    #
    @55
    c0
    cvol
    cfv
    #
    cc0
    @115
    @51
    c0
    cvol
    @115
    @51
    @3
    @49
    cfv
    #
    c1st
    cfv
    #
    @117
    c2nd
    cfv
    #
    cico
    co
    cc0
    cc0
    cico
    co
    #
    c0
    @115
    @49
    cico
    cr
    cr
    cX
    @3
    @114
    @108
    @13
    @114
    @108
    cX
    @39
    vk
    cX
    @63
    cmpt
    #
    wf
    #
    wph
    @122
    @110
    wph
    vk
    cX
    @63
    @39
    @121
    @73
    @121
    eqid
    fmptd
    adantr
    @114
    cX
    @39
    @49
    @121
    @114
    @49
    @65
    @121
    @114
    wph
    @67
    @49
    @65
    wceq
    wph
    @110
    simpl
    @110
    @67
    wph
    @24
    cn
    @101
    eldifi
    adantl
    wph
    vj
    cn
    @65
    cH
    cvv
    @87
    wph
    @67
    wa
    @65
    @40
    @76
    elexd
    fvmpt2d
    syl2anc
    @110
    @65
    @121
    wceq
    wph
    @110
    vk
    cX
    @64
    @63
    @110
    @61
    @62
    @63
    @110
    @24
    c1
    @24
    cn
    c1
    eldifsni
    neneqd
    iffalsed
    mpteq2dv
    adantl
    eqtrd
    #
    feq1d
    mpbird
    adantr
    @114
    @13
    simpr
    fvovco
    @115
    @118
    cc0
    @119
    cc0
    cico
    @115
    @118
    @63
    c1st
    cfv
    #
    cc0
    @115
    @117
    @63
    c1st
    @114
    vk
    cX
    @63
    @49
    cvv
    @123
    @63
    cvv
    wcel
    @115
    @63
    @39
    @72
    elexi
    a1i
    fvmpt2d
    #
    fveq2d
    @124
    cc0
    wceq
    @115
    cc0
    cc0
    cc0
    cxr
    0xr
    elexi
    #
    @126
    op1st
    a1i
    eqtrd
    @115
    @119
    @63
    c2nd
    cfv
    #
    cc0
    @115
    @117
    @63
    c2nd
    @125
    fveq2d
    @127
    cc0
    wceq
    @115
    cc0
    cc0
    @126
    @126
    op2nd
    a1i
    eqtrd
    oveq12d
    @120
    c0
    wceq
    #
    @115
    @128
    cc0
    cc0
    cle
    wbr
    #
    0le0
    @17
    @17
    @128
    @129
    wb
    0xr
    0xr
    cc0
    cc0
    ico0
    mp2an
    mpbir
    a1i
    3eqtrd
    fveq2d
    @116
    cc0
    wceq
    @115
    vol0
    a1i
    eqtrd
    prodeq2dv
    adantlr
    wph
    @111
    @113
    wceq
    #
    @21
    @110
    wph
    @75
    cc0
    cc
    wcel
    @130
    ovnhoilem1.x
    wph
    0cnd
    cX
    cc0
    vk
    fprodconst
    syl2anc
    ad2antrr
    @22
    @113
    cc0
    wceq
    #
    @110
    @22
    @112
    cn
    wcel
    #
    @131
    @22
    @132
    cX
    c0
    wne
    #
    @21
    @133
    wph
    cX
    c0
    neqne
    adantl
    @22
    @75
    @132
    @133
    wb
    wph
    @75
    @21
    ovnhoilem1.x
    adantr
    cX
    hashnncl
    syl
    mpbird
    @112
    0exp
    syl
    adantr
    3eqtrd
    sge0ss
    3eqtrd
    jca
    @46
    @60
    vi
    cH
    @41
    @25
    cH
    wceq
    #
    @31
    @54
    @45
    @59
    @134
    @30
    @53
    cI
    @134
    vj
    cn
    @29
    @52
    @134
    vk
    cX
    @28
    @51
    vk
    @25
    cH
    vk
    @25
    nfcv
    vk
    cH
    @86
    ovnhoilem1.h
    vk
    vj
    cn
    @65
    vk
    cn
    nfcv
    vk
    cX
    @64
    nfmpt1
    nfmpt
    nfcxfr
    nfeq
    #
    @134
    @28
    @51
    wceq
    @13
    @134
    @3
    @27
    @50
    @134
    @26
    @49
    cico
    @24
    @25
    cH
    fveq1
    coeq2d
    fveq1d
    #
    adantr
    ixpeq2d
    iuneq2d
    sseq2d
    @134
    @36
    @58
    @8
    @134
    @35
    @57
    csumge0
    @134
    vj
    cn
    @34
    @56
    @134
    cX
    @33
    @55
    vk
    @134
    @33
    @55
    wceq
    #
    vk
    cX
    @135
    @134
    @137
    @13
    @134
    @28
    @51
    cvol
    @136
    fveq2d
    a1d
    ralrimi
    prodeq2d
    mpteq2dv
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl2anc
    jca
    @42
    @47
    vz
    @8
    cxr
    @32
    @8
    wceq
    #
    @38
    @46
    vi
    @41
    @138
    @37
    @45
    @31
    @32
    @8
    @36
    eqeq1
    anbi2d
    rexbidv
    elrab
    sylibr
    @43
    cM
    wceq
    @22
    cM
    @43
    ovnhoilem1.m
    eqcomi
    a1i
    eleqtrd
    cM
    @8
    infxrlb
    syl2anc
    eqbrtrd
    pm2.61dan
    eqbrtrd
end
