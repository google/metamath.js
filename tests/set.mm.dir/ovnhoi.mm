include "covoln.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cico.mm"
include "cixp.mm"
include "cr.mm"
include "cmap.mm"
include "wceq.mm"
include "a1i.mm"
include "nfv.mm"
include "ffvelrnda.mm"
include "wcel.mm"
include "wa.mm"
include "rexrd.mm"
include "hoissrrn2.mm"
include "eqsstrd.mm"
include "ovnxrcl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cxr.mm"
include "icossxr.mm"
include "hoidmvcl.mm"
include "sseldi.mm"
include "c0.mm"
include "cle.mm"
include "wbr.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "adantl.mm"
include "wss.mm"
include "csn.mm"
include "ixpeq1.mm"
include "ixp0x.mm"
include "eqtrd.mm"
include "cvv.mm"
include "reex.mm"
include "mapdm0.mm"
include "ax-mp.mm"
include "3eqtr4d.mm"
include "eqimss.mm"
include "syl.mm"
include "ovn0val.mm"
include "0red.mm"
include "eqeltrd.mm"
include "eqidd.mm"
include "oveqd.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "feq2d.mm"
include "mpbid.mm"
include "hoidmv0val.mm"
include "eqled.mm"
include "wn.mm"
include "cvol.mm"
include "cprod.mm"
include "cn.mm"
include "c1.mm"
include "cop.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "ciun.mm"
include "csumge0.mm"
include "cxp.mm"
include "wrex.mm"
include "crab.mm"
include "eqid.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "cbvmptv.mm"
include "ovnhoilem1.mm"
include "cfn.mm"
include "wne.mm"
include "neqne.mm"
include "hoidmvn0val.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "pm2.61dan.mm"
include "c2nd.mm"
include "c1st.mm"
include "cmpt2.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "prodeq2ad.mm"
include "ifeq2d.mm"
include "oveq2d.mm"
include "cbvmpt2v.mm"
include "oveq2.mm"
include "prodeq1.mm"
include "ifbieq2d.mm"
include "mpt2eq123dv.mm"
include "eqtri.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "wb.mm"
include "simpl.mm"
include "coeq2d.mm"
include "ixpeq2dv.mm"
include "iuneq2dv.mm"
include "sseq2d.mm"
include "prodeq2dv.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "bitrd.mm"
include "cbvrabv.mm"
include "mpteq2dva.mm"
include "mpteq2i.mm"
include "ovnhoilem2.mm"
include "xrletrid.mm"

theorem ovnhoi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cI: class I
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vz: setvar z
  let vy: setvar y
  let vh: setvar h
  let vw: setvar w
  let vl: setvar l
  assume ovnhoi.x: |- ( ph -> X e. Fin )
  assume ovnhoi.a: |- ( ph -> A : X --> RR )
  assume ovnhoi.b: |- ( ph -> B : X --> RR )
  assume ovnhoi.c: |- I = X_ k e. X ( ( A ` k ) [,) ( B ` k ) )
  assume ovnhoi.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A c
  disjoint A d
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint c k
  disjoint d k
  disjoint A i
  disjoint A j
  disjoint A n
  disjoint A z
  disjoint c i
  disjoint c j
  disjoint c n
  disjoint c z
  disjoint d i
  disjoint d j
  disjoint d n
  disjoint d z
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i z
  disjoint j k
  disjoint j n
  disjoint j z
  disjoint k n
  disjoint k z
  disjoint n z
  disjoint B c
  disjoint B d
  disjoint B i
  disjoint B j
  disjoint B n
  disjoint B z
  disjoint I c
  disjoint I d
  disjoint I i
  disjoint I n
  disjoint I y
  disjoint I z
  disjoint c y
  disjoint d y
  disjoint i y
  disjoint n y
  disjoint y z
  disjoint I h
  disjoint I w
  disjoint h i
  disjoint h w
  disjoint h z
  disjoint i w
  disjoint w z
  disjoint L c
  disjoint L d
  disjoint L i
  disjoint L n
  disjoint L y
  disjoint L z
  disjoint X c
  disjoint X d
  disjoint X y
  disjoint a y
  disjoint b y
  disjoint c x
  disjoint d x
  disjoint k y
  disjoint x y
  disjoint X h
  disjoint X i
  disjoint X j
  disjoint X w
  disjoint X z
  disjoint h j
  disjoint h k
  disjoint j w
  disjoint k w
  disjoint X l
  disjoint X n
  disjoint c l
  disjoint d l
  disjoint i l
  disjoint j l
  disjoint k l
  disjoint l n
  disjoint c ph
  disjoint d ph
  disjoint ph y
  disjoint i ph
  disjoint j ph
  disjoint l ph
  disjoint n ph
  disjoint j y
  disjoint ph z
  assert |- ( ph -> ( ( voln* ` X ) ` I ) = ( A ( L ` X ) B ) )

  proof
    wph
    cI
    cX
    covoln
    cfv
    #
    cfv
    #
    cA
    cB
    cX
    cL
    cfv
    #
    co
    #
    wph
    cI
    cX
    ovnhoi.x
    wph
    cI
    vk
    cX
    vk
    cv
    #
    cA
    cfv
    #
    @4
    cB
    cfv
    #
    cico
    co
    #
    cixp
    #
    cr
    cX
    cmap
    co
    cI
    @8
    wceq
    #
    wph
    ovnhoi.c
    a1i
    wph
    @5
    @6
    vk
    cX
    wph
    vk
    nfv
    wph
    cX
    cr
    @4
    cA
    ovnhoi.a
    ffvelrnda
    wph
    @4
    cX
    wcel
    #
    wa
    @6
    wph
    cX
    cr
    @4
    cB
    ovnhoi.b
    ffvelrnda
    rexrd
    hoissrrn2
    eqsstrd
    ovnxrcl
    wph
    cc0
    cpnf
    cico
    co
    cxr
    @3
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
    ovnhoi.l
    ovnhoi.x
    ovnhoi.a
    ovnhoi.b
    hoidmvcl
    sseldi
    wph
    cX
    c0
    wceq
    #
    @1
    @3
    cle
    wbr
    wph
    @11
    wa
    #
    @1
    @3
    @12
    @1
    cc0
    cr
    @12
    @1
    cI
    c0
    covoln
    cfv
    #
    cfv
    #
    cc0
    @11
    @1
    @14
    wceq
    wph
    @11
    cI
    @0
    @13
    cX
    c0
    covoln
    fveq2
    fveq1d
    adantl
    @12
    cI
    @12
    cI
    cr
    c0
    cmap
    co
    #
    wceq
    cI
    @15
    wss
    @12
    @8
    c0
    csn
    #
    cI
    @15
    @11
    @8
    @16
    wceq
    wph
    @11
    @8
    vk
    c0
    @7
    cixp
    #
    @16
    vk
    cX
    c0
    @7
    ixpeq1
    @17
    @16
    wceq
    @11
    vk
    @7
    ixp0x
    a1i
    eqtrd
    adantl
    @9
    @12
    ovnhoi.c
    a1i
    @15
    @16
    wceq
    #
    @12
    cr
    cvv
    wcel
    @18
    reex
    cr
    cvv
    mapdm0
    ax-mp
    a1i
    3eqtr4d
    cI
    @15
    eqimss
    syl
    ovn0val
    eqtrd
    #
    @12
    0red
    #
    eqeltrd
    @12
    cc0
    cc0
    @1
    @3
    @12
    cc0
    eqidd
    @19
    @12
    @3
    cA
    cB
    c0
    cL
    cfv
    #
    co
    #
    cc0
    @11
    @3
    @22
    wceq
    wph
    @11
    @2
    @21
    cA
    cB
    cX
    c0
    cL
    fveq2
    oveqd
    adantl
    @12
    vx
    cA
    cB
    vk
    cL
    va
    vb
    ovnhoi.l
    @12
    cX
    cr
    cA
    wf
    #
    c0
    cr
    cA
    wf
    wph
    @23
    @11
    ovnhoi.a
    adantr
    @12
    cX
    c0
    cr
    cA
    wph
    @11
    simpr
    #
    feq2d
    mpbid
    @12
    cX
    cr
    cB
    wf
    #
    c0
    cr
    cB
    wf
    wph
    @25
    @11
    ovnhoi.b
    adantr
    @12
    cX
    c0
    cr
    cB
    @24
    feq2d
    mpbid
    hoidmv0val
    eqtrd
    #
    3eqtr4d
    #
    eqled
    wph
    @11
    wn
    #
    wa
    #
    @1
    cX
    @7
    cvol
    cfv
    vk
    cprod
    #
    @3
    cle
    wph
    @1
    @30
    cle
    wbr
    @28
    wph
    vz
    cA
    cB
    vi
    vj
    vk
    vn
    cn
    vk
    cX
    vn
    cv
    #
    c1
    wceq
    #
    @5
    @6
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
    cmpt
    cI
    cI
    vj
    cn
    vk
    cX
    @4
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
    @41
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
    cX
    cmap
    co
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
    cX
    ovnhoi.x
    ovnhoi.a
    ovnhoi.b
    ovnhoi.c
    @54
    eqid
    vn
    vj
    cn
    @36
    vk
    cX
    @37
    c1
    wceq
    #
    @33
    @34
    cif
    #
    cmpt
    @31
    @37
    wceq
    #
    vk
    cX
    @35
    @56
    @57
    @32
    @55
    @33
    @34
    @31
    @37
    c1
    eqeq1
    ifbid
    mpteq2dv
    cbvmptv
    ovnhoilem1
    adantr
    @29
    @3
    @30
    @29
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    ovnhoi.l
    wph
    cX
    cfn
    wcel
    @28
    ovnhoi.x
    adantr
    #
    @28
    cX
    c0
    wne
    wph
    cX
    c0
    neqne
    adantl
    #
    wph
    @23
    @28
    ovnhoi.a
    adantr
    #
    wph
    @25
    @28
    ovnhoi.b
    adantr
    #
    hoidmvn0val
    eqcomd
    breqtrd
    pm2.61dan
    wph
    @11
    @3
    @1
    cle
    wbr
    @12
    @3
    @1
    @12
    @3
    cc0
    cr
    @26
    @20
    eqeltrd
    @12
    @1
    @3
    @27
    eqcomd
    eqled
    @29
    vy
    vz
    cA
    cB
    vi
    @52
    vj
    cn
    vl
    cX
    vl
    cv
    #
    @39
    cfv
    #
    c2nd
    cfv
    #
    cmpt
    #
    cmpt
    #
    cmpt
    vi
    vj
    vk
    vn
    vi
    @52
    vj
    cn
    vl
    cX
    @63
    c1st
    cfv
    #
    cmpt
    #
    cmpt
    #
    cmpt
    cI
    cL
    cI
    vj
    cn
    vk
    cX
    @4
    cico
    @37
    vh
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
    vw
    cv
    #
    vj
    cn
    cX
    @73
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
    vh
    @52
    wrex
    #
    vw
    cxr
    crab
    cX
    vc
    vd
    vl
    @58
    @59
    @60
    @61
    ovnhoi.c
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
    @86
    @85
    c0
    wceq
    #
    cc0
    @85
    @4
    va
    cv
    #
    cfv
    #
    @4
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
    vy
    cfn
    vc
    vd
    cr
    vy
    cv
    #
    cmap
    co
    #
    @98
    @97
    c0
    wceq
    #
    cc0
    @97
    @4
    vc
    cv
    #
    cfv
    #
    @4
    vd
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
    ovnhoi.l
    vx
    vy
    cfn
    @96
    @108
    @85
    @97
    wceq
    #
    @96
    vc
    vd
    @86
    @86
    @87
    cc0
    @85
    @105
    vk
    cprod
    #
    cif
    #
    cmpt2
    #
    @108
    @96
    @112
    wceq
    @109
    va
    vb
    vc
    vd
    @86
    @86
    @95
    @111
    @87
    cc0
    @85
    @101
    @91
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
    @88
    @100
    wceq
    #
    @87
    @94
    @115
    cc0
    @116
    @85
    @93
    @114
    vk
    @116
    @92
    @113
    cvol
    @116
    @89
    @101
    @91
    cico
    @4
    @88
    @100
    fveq1
    oveq1d
    fveq2d
    prodeq2ad
    ifeq2d
    @90
    @102
    wceq
    #
    @87
    @115
    @110
    cc0
    @117
    @85
    @114
    @105
    vk
    @117
    @113
    @104
    cvol
    @117
    @91
    @103
    @101
    cico
    @4
    @90
    @102
    fveq1
    oveq2d
    fveq2d
    prodeq2ad
    ifeq2d
    cbvmpt2v
    a1i
    @109
    vc
    vd
    @86
    @86
    @111
    @98
    @98
    @107
    @85
    @97
    cr
    cmap
    oveq2
    #
    @118
    @109
    @87
    @99
    @110
    @106
    cc0
    @85
    @97
    c0
    eqeq1
    @85
    @97
    @105
    vk
    prodeq1
    ifbieq2d
    mpt2eq123dv
    eqtrd
    cbvmptv
    eqtri
    @84
    @53
    vw
    vz
    cxr
    @77
    @45
    wceq
    #
    @84
    @76
    @45
    @81
    wceq
    #
    wa
    #
    vh
    @52
    wrex
    #
    @53
    @119
    @83
    @121
    vh
    @52
    @119
    @82
    @120
    @76
    @77
    @45
    @81
    eqeq1
    anbi2d
    rexbidv
    @122
    @53
    wb
    @119
    @121
    @51
    vh
    vi
    @52
    @70
    @38
    wceq
    #
    @76
    @44
    @120
    @50
    @123
    @75
    @43
    cI
    @123
    vj
    cn
    @74
    @42
    @123
    @37
    cn
    wcel
    #
    wa
    #
    vk
    cX
    @73
    @41
    @125
    @4
    @72
    @40
    @125
    @71
    @39
    cico
    @125
    @37
    @70
    @38
    @123
    @124
    simpl
    fveq1d
    coeq2d
    fveq1d
    ixpeq2dv
    iuneq2dv
    sseq2d
    @123
    @81
    @49
    @45
    @123
    @80
    @48
    csumge0
    @123
    vj
    cn
    @79
    @47
    @123
    cX
    @78
    @46
    vk
    @123
    @10
    wa
    #
    @73
    @41
    cvol
    @126
    @4
    @72
    @40
    @126
    @71
    @39
    cico
    @126
    @37
    @70
    @38
    @123
    @10
    simpl
    fveq1d
    coeq2d
    fveq1d
    fveq2d
    prodeq2dv
    mpteq2dv
    fveq2d
    eqeq2d
    anbi12d
    cbvrexv
    a1i
    bitrd
    cbvrabv
    vi
    @52
    @69
    vn
    cn
    vl
    cX
    @62
    @31
    @38
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
    vj
    vn
    cn
    @68
    @130
    @37
    @31
    wceq
    #
    vl
    cX
    @67
    @129
    @131
    @62
    cX
    wcel
    #
    wa
    #
    @63
    @128
    c1st
    @133
    @62
    @39
    @127
    @133
    @37
    @31
    @38
    @131
    @132
    simpl
    fveq2d
    fveq1d
    #
    fveq2d
    mpteq2dva
    cbvmptv
    mpteq2i
    vi
    @52
    @66
    vn
    cn
    vl
    cX
    @128
    c2nd
    cfv
    #
    cmpt
    #
    cmpt
    vj
    vn
    cn
    @65
    @136
    @131
    vl
    cX
    @64
    @135
    @133
    @63
    @128
    c2nd
    @134
    fveq2d
    mpteq2dva
    cbvmptv
    mpteq2i
    ovnhoilem2
    pm2.61dan
    xrletrid
end
