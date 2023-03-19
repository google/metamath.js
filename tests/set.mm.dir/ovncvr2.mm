include "cn.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cico.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "covoln.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "c1st.mm"
include "wcel.mm"
include "cxp.mm"
include "ccom.mm"
include "crab.mm"
include "cpw.mm"
include "cvv.mm"
include "wceq.mm"
include "a1i.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "adantl.mm"
include "wb.mm"
include "ovexd.mm"
include "ssexd.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmptd.mm"
include "ssrab2.mm"
include "eqsstrd.mm"
include "crp.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "rabbidva2.mm"
include "mpteq2dv.mm"
include "rpex.mm"
include "mptex.mm"
include "oveq2.mm"
include "fvex.mm"
include "eleqtrd.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylib.mm"
include "simpld.mm"
include "sseldd.mm"
include "elmapi.mm"
include "adantr.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "eqid.mm"
include "fmptd.mm"
include "cfn.mm"
include "reex.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "feq1d.mm"
include "c2nd.mm"
include "xp2nd.mm"
include "jca.mm"
include "wi.mm"
include "idi.mm"
include "coeq2d.mm"
include "fveq1d.mm"
include "ixpeq2dv.mm"
include "iuneq2dv.mm"
include "sseq2d.mm"
include "simprd.mm"
include "fvovco.mm"
include "mptexg.mm"
include "fvmpt2d.mm"
include "fvexd.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "ixpeq2dva.mm"
include "sseqtrd.mm"
include "coeq2.mm"
include "ad2antlr.mm"
include "adantllr.mm"
include "adantlr.mm"
include "3eqtrd.mm"
include "prodeq2dv.mm"
include "fvmpt2.mm"
include "volicore.mm"
include "fprodrecl.mm"
include "mpteq2dva.mm"
include "eqbrtrd.mm"
include "jca31.mm"

theorem ovncvr2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cI: class I
  let cL: class L
  let cX: class X
  let vr: setvar r
  let va: setvar a
  let vl: setvar l
  let vx: setvar x
  assume ovncvr2.x: |- ( ph -> X e. Fin )
  assume ovncvr2.a: |- ( ph -> A C_ ( RR ^m X ) )
  assume ovncvr2.e: |- ( ph -> E e. RR+ )
  assume ovncvr2.c: |- C = ( a e. ~P ( RR ^m X ) |-> { l e. ( ( ( RR X. RR ) ^m X ) ^m NN ) | a C_ U_ j e. NN X_ k e. X ( ( [,) o. ( l ` j ) ) ` k ) } )
  assume ovncvr2.l: |- L = ( h e. ( ( RR X. RR ) ^m X ) |-> prod_ k e. X ( vol ` ( ( [,) o. h ) ` k ) ) )
  assume ovncvr2.d: |- D = ( a e. ~P ( RR ^m X ) |-> ( r e. RR+ |-> { i e. ( C ` a ) | ( sum^ ` ( j e. NN |-> ( L ` ( i ` j ) ) ) ) <_ ( ( ( voln* ` X ) ` a ) +e r ) } ) )
  assume ovncvr2.i: |- ( ph -> I e. ( ( D ` A ) ` E ) )
  assume ovncvr2.b: |- B = ( j e. NN |-> ( k e. X |-> ( 1st ` ( ( I ` j ) ` k ) ) ) )
  assume ovncvr2.t: |- T = ( j e. NN |-> ( k e. X |-> ( 2nd ` ( ( I ` j ) ` k ) ) ) )

  disjoint A a
  disjoint A i
  disjoint A r
  disjoint a i
  disjoint a r
  disjoint i r
  disjoint A l
  disjoint a l
  disjoint B h
  disjoint C a
  disjoint C i
  disjoint C r
  disjoint E i
  disjoint E r
  disjoint I h
  disjoint I j
  disjoint I k
  disjoint h j
  disjoint h k
  disjoint j k
  disjoint I i
  disjoint i j
  disjoint I l
  disjoint j l
  disjoint k l
  disjoint L a
  disjoint L i
  disjoint L r
  disjoint T h
  disjoint X a
  disjoint X i
  disjoint X j
  disjoint X r
  disjoint a j
  disjoint j r
  disjoint X h
  disjoint X k
  disjoint X l
  disjoint a k
  disjoint a ph
  disjoint j ph
  disjoint k ph
  disjoint h ph
  disjoint ph r
  disjoint k x
  assert |- ( ph -> ( ( ( B : NN --> ( RR ^m X ) /\ T : NN --> ( RR ^m X ) ) /\ A C_ U_ j e. NN X_ k e. X ( ( ( B ` j ) ` k ) [,) ( ( T ` j ) ` k ) ) ) /\ ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( ( B ` j ) ` k ) [,) ( ( T ` j ) ` k ) ) ) ) ) <_ ( ( ( voln* ` X ) ` A ) +e E ) ) )

  proof
    wph
    cn
    cr
    cX
    cmap
    co
    #
    cB
    wf
    #
    cn
    @0
    cT
    wf
    #
    wa
    cA
    vj
    cn
    vk
    cX
    vk
    cv
    #
    vj
    cv
    #
    cB
    cfv
    #
    cfv
    #
    @3
    @4
    cT
    cfv
    #
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
    vj
    cn
    cX
    @9
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
    cA
    cX
    covoln
    cfv
    #
    cfv
    #
    cE
    cxad
    co
    #
    cle
    wbr
    wph
    @1
    @2
    wph
    @1
    cn
    @0
    vj
    cn
    vk
    cX
    @3
    @4
    cI
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
    wph
    vj
    cn
    @22
    @0
    @23
    wph
    @4
    cn
    wcel
    #
    wa
    #
    @22
    @0
    wcel
    #
    cX
    cr
    @22
    wf
    #
    @25
    vk
    cX
    @21
    cr
    @22
    @25
    @3
    cX
    wcel
    #
    wa
    #
    @20
    cr
    cr
    cxp
    #
    wcel
    #
    @21
    cr
    wcel
    @25
    cX
    @30
    @3
    @19
    @25
    @19
    @30
    cX
    cmap
    co
    #
    wcel
    cX
    @30
    @19
    wf
    #
    @25
    cn
    @32
    @4
    cI
    wph
    cn
    @32
    cI
    wf
    #
    @24
    wph
    cI
    @32
    cn
    cmap
    co
    #
    wcel
    #
    @34
    wph
    cA
    cC
    cfv
    #
    @35
    cI
    wph
    @37
    cA
    vj
    cn
    vk
    cX
    @3
    cico
    @4
    vl
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
    vl
    @35
    crab
    #
    @35
    wph
    va
    cA
    va
    cv
    #
    @43
    wss
    #
    vl
    @35
    crab
    #
    @45
    @0
    cpw
    #
    cC
    cvv
    cC
    va
    @49
    @48
    cmpt
    wceq
    wph
    ovncvr2.c
    a1i
    @46
    cA
    wceq
    #
    @48
    @45
    wceq
    wph
    @50
    @47
    @44
    vl
    @35
    @46
    cA
    @43
    sseq1
    rabbidv
    adantl
    wph
    cA
    @49
    wcel
    #
    cA
    @0
    wss
    #
    ovncvr2.a
    wph
    cA
    cvv
    wcel
    @51
    @52
    wb
    wph
    cA
    @0
    cvv
    wph
    cr
    cX
    cmap
    ovexd
    ovncvr2.a
    ssexd
    cA
    @0
    cvv
    elpwg
    syl
    mpbird
    #
    @45
    cvv
    wcel
    wph
    @44
    vl
    @35
    @32
    cn
    cmap
    ovex
    rabex
    a1i
    fvmptd
    #
    @45
    @35
    wss
    wph
    @44
    vl
    @35
    ssrab2
    a1i
    eqsstrd
    wph
    cI
    @37
    wcel
    #
    vj
    cn
    @19
    cL
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @18
    cle
    wbr
    #
    wph
    cI
    vj
    cn
    @4
    vi
    cv
    #
    cfv
    #
    cL
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @18
    cle
    wbr
    #
    vi
    @37
    crab
    #
    wcel
    @55
    @59
    wa
    wph
    cI
    cE
    cA
    cD
    cfv
    #
    cfv
    @66
    ovncvr2.i
    wph
    vr
    cE
    @64
    @17
    vr
    cv
    #
    cxad
    co
    #
    cle
    wbr
    #
    vi
    @37
    crab
    #
    @66
    crp
    @67
    cvv
    wph
    va
    cA
    vr
    crp
    @64
    @46
    @16
    cfv
    #
    @68
    cxad
    co
    #
    cle
    wbr
    #
    vi
    @46
    cC
    cfv
    #
    crab
    #
    cmpt
    #
    vr
    crp
    @71
    cmpt
    #
    @49
    cD
    cvv
    cD
    va
    @49
    @77
    cmpt
    wceq
    wph
    ovncvr2.d
    a1i
    @50
    @77
    @78
    wceq
    wph
    @50
    vr
    crp
    @76
    @71
    @50
    @74
    @70
    vi
    @75
    @37
    @50
    @60
    @75
    wcel
    @60
    @37
    wcel
    @74
    @70
    @50
    @75
    @37
    @60
    @46
    cA
    cC
    fveq2
    eleq2d
    @50
    @73
    @69
    @64
    cle
    @50
    @72
    @17
    @68
    cxad
    @46
    cA
    @16
    fveq2
    oveq1d
    breq2d
    anbi12d
    rabbidva2
    mpteq2dv
    adantl
    @53
    @78
    cvv
    wcel
    wph
    vr
    crp
    @71
    rpex
    mptex
    a1i
    fvmptd
    @68
    cE
    wceq
    #
    @71
    @66
    wceq
    wph
    @79
    @70
    @65
    vi
    @37
    @79
    @69
    @18
    @64
    cle
    @68
    cE
    @17
    cxad
    oveq2
    breq2d
    rabbidv
    adantl
    ovncvr2.e
    @66
    cvv
    wcel
    wph
    @65
    vi
    @37
    cA
    cC
    fvex
    rabex
    a1i
    fvmptd
    eleqtrd
    @65
    @59
    vi
    cI
    @37
    @60
    cI
    wceq
    #
    @64
    @58
    @18
    cle
    @80
    @63
    @57
    csumge0
    @80
    vj
    cn
    @62
    @56
    @80
    @61
    @19
    cL
    @4
    @60
    cI
    fveq1
    fveq2d
    mpteq2dv
    fveq2d
    breq1d
    elrab
    sylib
    #
    simpld
    #
    sseldd
    cI
    @32
    cn
    elmapi
    syl
    adantr
    wph
    @24
    simpr
    #
    ffvelrnd
    #
    @19
    @30
    cX
    elmapi
    syl
    #
    ffvelrnda
    #
    @20
    cr
    cr
    xp1st
    syl
    @22
    eqid
    fmptd
    #
    wph
    @26
    @27
    wb
    #
    @24
    wph
    cr
    cvv
    wcel
    #
    cX
    cfn
    wcel
    #
    @88
    @89
    wph
    reex
    a1i
    #
    ovncvr2.x
    cr
    cX
    @22
    cvv
    cfn
    elmapg
    syl2anc
    adantr
    mpbird
    @23
    eqid
    fmptd
    wph
    cn
    @0
    cB
    @23
    cB
    @23
    wceq
    wph
    ovncvr2.b
    a1i
    #
    feq1d
    mpbird
    wph
    @2
    cn
    @0
    vj
    cn
    vk
    cX
    @20
    c2nd
    cfv
    #
    cmpt
    #
    cmpt
    #
    wf
    wph
    vj
    cn
    @94
    @0
    @95
    @25
    @94
    @0
    wcel
    #
    cX
    cr
    @94
    wf
    #
    @25
    vk
    cX
    @93
    cr
    @94
    @29
    @31
    @93
    cr
    wcel
    @86
    @20
    cr
    cr
    xp2nd
    syl
    @94
    eqid
    fmptd
    #
    wph
    @96
    @97
    wb
    #
    @24
    wph
    @89
    @90
    @99
    @91
    ovncvr2.x
    cr
    cX
    @94
    cvv
    cfn
    elmapg
    syl2anc
    adantr
    mpbird
    @95
    eqid
    fmptd
    wph
    cn
    @0
    cT
    @95
    cT
    @95
    wceq
    wph
    ovncvr2.t
    a1i
    #
    feq1d
    mpbird
    jca
    wph
    cA
    vj
    cn
    vk
    cX
    @3
    cico
    @19
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    @11
    wph
    @36
    cA
    @104
    wss
    #
    wph
    cI
    @45
    wcel
    @36
    @105
    wa
    wph
    cI
    @37
    @45
    @82
    wph
    @37
    @45
    wceq
    wi
    @54
    idi
    eleqtrd
    @44
    @105
    vl
    cI
    @35
    @38
    cI
    wceq
    #
    @43
    @104
    cA
    @106
    vj
    cn
    @42
    @103
    @106
    @42
    @103
    wceq
    @24
    @106
    vk
    cX
    @41
    @102
    @106
    @3
    @40
    @101
    @106
    @39
    @19
    cico
    @4
    @38
    cI
    fveq1
    coeq2d
    fveq1d
    ixpeq2dv
    adantr
    iuneq2dv
    sseq2d
    elrab
    sylib
    simprd
    wph
    vj
    cn
    @103
    @10
    @25
    vk
    cX
    @102
    @9
    @29
    @102
    @21
    @93
    cico
    co
    #
    @9
    @29
    @19
    cico
    cr
    cr
    cX
    @3
    @25
    @33
    @28
    @85
    adantr
    @25
    @28
    simpr
    #
    fvovco
    #
    @29
    @21
    @6
    @93
    @8
    cico
    @29
    @6
    @21
    @25
    vk
    cX
    @21
    @5
    cvv
    wph
    vj
    cn
    @22
    cB
    cvv
    @92
    wph
    @22
    cvv
    wcel
    #
    @24
    wph
    @90
    @110
    ovncvr2.x
    vk
    cX
    @21
    cfn
    mptexg
    syl
    adantr
    #
    fvmpt2d
    @29
    @20
    c1st
    fvexd
    fvmpt2d
    eqcomd
    @29
    @8
    @93
    @25
    vk
    cX
    @93
    @7
    cvv
    wph
    vj
    cn
    @94
    cT
    cvv
    @100
    wph
    @94
    cvv
    wcel
    #
    @24
    wph
    @90
    @112
    ovncvr2.x
    vk
    cX
    @93
    cfn
    mptexg
    syl
    adantr
    #
    fvmpt2d
    @29
    @20
    c2nd
    fvexd
    fvmpt2d
    eqcomd
    oveq12d
    #
    eqtrd
    ixpeq2dva
    iuneq2dv
    sseqtrd
    wph
    @15
    @58
    @18
    cle
    wph
    @14
    @57
    csumge0
    wph
    vj
    cn
    @13
    @56
    @25
    @56
    @13
    @25
    vh
    @19
    cX
    @3
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
    vk
    cprod
    #
    @13
    @32
    cL
    cr
    cL
    vh
    @32
    @119
    cmpt
    wceq
    @25
    ovncvr2.l
    a1i
    @25
    @115
    @19
    wceq
    #
    wa
    #
    cX
    @118
    @12
    vk
    @121
    @28
    wa
    #
    @117
    @9
    cvol
    @122
    @117
    @102
    @107
    @9
    wph
    @120
    @28
    @117
    @102
    wceq
    #
    @24
    @120
    @123
    wph
    @28
    @120
    @3
    @116
    @101
    @115
    @19
    cico
    coeq2
    fveq1d
    ad2antlr
    adantllr
    @25
    @28
    @102
    @107
    wceq
    @120
    @109
    adantlr
    @25
    @28
    @107
    @9
    wceq
    @120
    @114
    adantlr
    3eqtrd
    fveq2d
    prodeq2dv
    @84
    @25
    cX
    @12
    vk
    wph
    @90
    @24
    ovncvr2.x
    adantr
    @29
    @6
    cr
    wcel
    @8
    cr
    wcel
    @12
    cr
    wcel
    @29
    cX
    cr
    @3
    @5
    @25
    cX
    cr
    @5
    wf
    #
    @28
    @25
    @124
    @27
    @87
    @25
    cX
    cr
    @5
    @22
    @25
    @24
    @110
    @5
    @22
    wceq
    @83
    @111
    vj
    cn
    @22
    cvv
    cB
    ovncvr2.b
    fvmpt2
    syl2anc
    feq1d
    mpbird
    adantr
    @108
    ffvelrnd
    @29
    cX
    cr
    @3
    @7
    @25
    cX
    cr
    @7
    wf
    #
    @28
    @25
    @125
    @97
    @98
    @25
    cX
    cr
    @7
    @94
    @25
    @24
    @112
    @7
    @94
    wceq
    @83
    @113
    vj
    cn
    @94
    cvv
    cT
    ovncvr2.t
    fvmpt2
    syl2anc
    feq1d
    mpbird
    adantr
    @108
    ffvelrnd
    @6
    @8
    volicore
    syl2anc
    fprodrecl
    fvmptd
    eqcomd
    mpteq2dva
    fveq2d
    wph
    @55
    @59
    @81
    simprd
    eqbrtrd
    jca31
end
