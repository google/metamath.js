include "cn.mm"
include "ciun.mm"
include "covol.mm"
include "cfv.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "ovolcl.mm"
include "syl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cle.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "cv.mm"
include "c2nd.mm"
include "c1st.mm"
include "wa.mm"
include "cmap.mm"
include "adantr.mm"
include "wf1o.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "ffvelrnd.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "nnex.mm"
include "elmap.mm"
include "sylib.mm"
include "xp2nd.mm"
include "fmptd.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "eqid.mm"
include "ovolsf.mm"
include "frn.mm"
include "3syl.mm"
include "icossxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "rpred.mm"
include "readdcld.mm"
include "rexrd.mm"
include "cioo.mm"
include "cuni.mm"
include "wbr.mm"
include "wrex.mm"
include "eliun.mm"
include "w3a.mm"
include "3adant3.mm"
include "wb.mm"
include "ovolfioo.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp3.mm"
include "rsp.mm"
include "sylc.mm"
include "ccnv.mm"
include "simpl1.mm"
include "f1ocnv.mm"
include "4syl.mm"
include "simpl2.mm"
include "simpr.mm"
include "fovrnd.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "cop.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "opelxpi.mm"
include "f1ocnvfv2.mm"
include "syl5eq.mm"
include "vex.mm"
include "op1st.mm"
include "syl6eq.mm"
include "op2nd.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "biimprd.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "rexlimdv3a.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "mpbird.mm"
include "ovollb.mm"
include "c1.mm"
include "cfz.mm"
include "cfn.mm"
include "fzfi.mm"
include "elfznn.mm"
include "ffvelrn.mm"
include "nnre.mm"
include "syl2an.mm"
include "fimaxre3.mm"
include "sylancr.mm"
include "cfl.mm"
include "wi.mm"
include "fllep1.mm"
include "ad2antlr.mm"
include "adantlr.mm"
include "simplr.mm"
include "flcl.mm"
include "peano2zd.mm"
include "zred.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "ralimdva.mm"
include "simpll.mm"
include "sylan.mm"
include "crp.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cz.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "ovoliunlem1.mm"
include "expr.mm"
include "syld.mm"
include "wfn.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "supxrleub.mm"
include "xrletrd.mm"

theorem ovoliunlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let cK: class K
  let cL: class L
  assume ovoliun.t: |- T = seq 1 ( + , G )
  assume ovoliun.g: |- G = ( n e. NN |-> ( vol* ` A ) )
  assume ovoliun.a: |- ( ( ph /\ n e. NN ) -> A C_ RR )
  assume ovoliun.v: |- ( ( ph /\ n e. NN ) -> ( vol* ` A ) e. RR )
  assume ovoliun.r: |- ( ph -> sup ( ran T , RR* , < ) e. RR )
  assume ovoliun.b: |- ( ph -> B e. RR+ )
  assume ovoliun.s: |- S = seq 1 ( + , ( ( abs o. - ) o. ( F ` n ) ) )
  assume ovoliun.u: |- U = seq 1 ( + , ( ( abs o. - ) o. H ) )
  assume ovoliun.h: |- H = ( k e. NN |-> ( ( F ` ( 1st ` ( J ` k ) ) ) ` ( 2nd ` ( J ` k ) ) ) )
  assume ovoliun.j: |- ( ph -> J : NN -1-1-onto-> ( NN X. NN ) )
  assume ovoliun.f: |- ( ph -> F : NN --> ( ( <_ i^i ( RR X. RR ) ) ^m NN ) )
  assume ovoliun.x1: |- ( ( ph /\ n e. NN ) -> A C_ U. ran ( (,) o. ( F ` n ) ) )
  assume ovoliun.x2: |- ( ( ph /\ n e. NN ) -> sup ( ran S , RR* , < ) <_ ( ( vol* ` A ) + ( B / ( 2 ^ n ) ) ) )

  disjoint G n
  disjoint T n
  disjoint A k
  disjoint k n
  disjoint B k
  disjoint B n
  disjoint F k
  disjoint F n
  disjoint J k
  disjoint J n
  disjoint H n
  disjoint k ph
  disjoint n ph
  disjoint S k
  disjoint G k
  disjoint T k
  disjoint ph w
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint f n
  disjoint B f
  disjoint g n
  disjoint B g
  disjoint j n
  disjoint B j
  disjoint m n
  disjoint B m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint f i
  disjoint F f
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i z
  disjoint F i
  disjoint F j
  disjoint F m
  disjoint F x
  disjoint F z
  disjoint i w
  disjoint i y
  disjoint J i
  disjoint j w
  disjoint J j
  disjoint k w
  disjoint m w
  disjoint J m
  disjoint n w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint K i
  disjoint K j
  disjoint K m
  disjoint K n
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L n
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint H f
  disjoint H j
  disjoint H m
  disjoint H z
  disjoint g i
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S f
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint G m
  disjoint G x
  disjoint T g
  disjoint T j
  disjoint T m
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U f
  disjoint U j
  disjoint U x
  disjoint U y
  disjoint U z
  assert |- ( ph -> ( vol* ` U_ n e. NN A ) <_ ( sup ( ran T , RR* , < ) + B ) )

  proof
    wph
    vn
    cn
    cA
    ciun
    #
    covol
    cfv
    #
    cU
    crn
    #
    cxr
    clt
    csup
    #
    cT
    crn
    cxr
    clt
    csup
    #
    cB
    caddc
    co
    #
    wph
    @0
    cr
    wss
    #
    @1
    cxr
    wcel
    wph
    cA
    cr
    wss
    #
    vn
    cn
    wral
    @6
    wph
    @7
    vn
    cn
    ovoliun.a
    ralrimiva
    vn
    cn
    cA
    cr
    iunss
    sylibr
    #
    @0
    ovolcl
    syl
    wph
    @2
    cxr
    wss
    #
    @3
    cxr
    wcel
    wph
    @2
    cc0
    cpnf
    cico
    co
    #
    cxr
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cH
    wf
    #
    cn
    @10
    cU
    wf
    #
    @2
    @10
    wss
    wph
    vk
    cn
    vk
    cv
    #
    cJ
    cfv
    #
    c2nd
    cfv
    #
    @16
    c1st
    cfv
    #
    cF
    cfv
    #
    cfv
    #
    @12
    cH
    wph
    @15
    cn
    wcel
    #
    wa
    #
    cn
    @12
    @17
    @19
    @22
    @19
    @12
    cn
    cmap
    co
    #
    wcel
    cn
    @12
    @19
    wf
    @22
    cn
    @23
    @18
    cF
    wph
    cn
    @23
    cF
    wf
    #
    @21
    ovoliun.f
    adantr
    @22
    @16
    cn
    cn
    cxp
    #
    wcel
    #
    @18
    cn
    wcel
    wph
    cn
    @25
    @15
    cJ
    wph
    cn
    @25
    cJ
    wf1o
    #
    cn
    @25
    cJ
    wf
    #
    ovoliun.j
    cn
    @25
    cJ
    f1of
    syl
    #
    ffvelrnda
    #
    @16
    cn
    cn
    xp1st
    syl
    ffvelrnd
    @12
    cn
    @19
    @11
    cle
    cr
    cr
    reex
    reex
    xpex
    inex2
    #
    nnex
    elmap
    sylib
    @22
    @26
    @17
    cn
    wcel
    @30
    @16
    cn
    cn
    xp2nd
    syl
    ffvelrnd
    ovoliun.h
    fmptd
    #
    cU
    cH
    cabs
    cmin
    ccom
    cH
    ccom
    #
    @33
    eqid
    ovoliun.u
    ovolsf
    #
    cn
    @10
    cU
    frn
    3syl
    cc0
    cpnf
    icossxr
    syl6ss
    #
    @2
    supxrcl
    syl
    wph
    @5
    wph
    @4
    cB
    ovoliun.r
    wph
    cB
    ovoliun.b
    rpred
    readdcld
    rexrd
    #
    wph
    @13
    @0
    cioo
    cH
    ccom
    crn
    cuni
    wss
    #
    @1
    @3
    cle
    wbr
    @32
    wph
    @37
    vm
    cv
    #
    cH
    cfv
    #
    c1st
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @41
    @39
    c2nd
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vm
    cn
    wrex
    #
    vz
    @0
    wral
    #
    wph
    @46
    vz
    @0
    @41
    @0
    wcel
    @41
    cA
    wcel
    #
    vn
    cn
    wrex
    wph
    @46
    vn
    @41
    cn
    cA
    eliun
    wph
    @48
    @46
    vn
    cn
    wph
    vn
    cv
    #
    cn
    wcel
    #
    @48
    w3a
    #
    vj
    cv
    #
    @49
    cF
    cfv
    #
    cfv
    #
    c1st
    cfv
    #
    @41
    clt
    wbr
    #
    @41
    @54
    c2nd
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vj
    cn
    wrex
    #
    @46
    @51
    @60
    vz
    cA
    wral
    #
    @48
    @60
    @51
    cA
    cioo
    @53
    ccom
    crn
    cuni
    wss
    #
    @61
    wph
    @50
    @62
    @48
    ovoliun.x1
    3adant3
    @51
    @7
    cn
    @12
    @53
    wf
    #
    @62
    @61
    wb
    wph
    @50
    @7
    @48
    ovoliun.a
    3adant3
    wph
    @50
    @63
    @48
    wph
    @50
    wa
    @53
    @23
    wcel
    @63
    wph
    cn
    @23
    @49
    cF
    ovoliun.f
    ffvelrnda
    @12
    cn
    @53
    @31
    nnex
    elmap
    sylib
    3adant3
    vz
    cA
    vj
    @53
    ovolfioo
    syl2anc
    mpbid
    wph
    @50
    @48
    simp3
    @60
    vz
    cA
    rsp
    sylc
    @51
    @59
    @46
    vj
    cn
    @51
    @52
    cn
    wcel
    #
    wa
    #
    @49
    @52
    cJ
    ccnv
    #
    co
    #
    cn
    wcel
    #
    @59
    @67
    cH
    cfv
    #
    c1st
    cfv
    #
    @41
    clt
    wbr
    #
    @41
    @69
    c2nd
    cfv
    #
    clt
    wbr
    #
    wa
    #
    @46
    @65
    @49
    @52
    cn
    cn
    cn
    @66
    @65
    wph
    @27
    @25
    cn
    @66
    wf1o
    @25
    cn
    @66
    wf
    wph
    @50
    @48
    @64
    simpl1
    #
    ovoliun.j
    cn
    @25
    cJ
    f1ocnv
    @25
    cn
    @66
    f1of
    4syl
    wph
    @50
    @48
    @64
    simpl2
    #
    @51
    @64
    simpr
    #
    fovrnd
    #
    @65
    @74
    @59
    @65
    @71
    @56
    @73
    @58
    @65
    @70
    @55
    @41
    clt
    @65
    @69
    @54
    c1st
    @65
    @69
    @67
    cJ
    cfv
    #
    c2nd
    cfv
    #
    @79
    c1st
    cfv
    #
    cF
    cfv
    #
    cfv
    #
    @54
    @65
    @68
    @69
    @83
    wceq
    @78
    vk
    @67
    @20
    @83
    cn
    cH
    @15
    @67
    wceq
    #
    @17
    @80
    @19
    @82
    @84
    @18
    @81
    cF
    @84
    @16
    @79
    c1st
    @15
    @67
    cJ
    fveq2
    #
    fveq2d
    fveq2d
    @84
    @16
    @79
    c2nd
    @85
    fveq2d
    fveq12d
    ovoliun.h
    @80
    @82
    fvex
    fvmpt
    syl
    @65
    @80
    @52
    @82
    @53
    @65
    @81
    @49
    cF
    @65
    @81
    @49
    @52
    cop
    #
    c1st
    cfv
    @49
    @65
    @79
    @86
    c1st
    @65
    @79
    @86
    @66
    cfv
    #
    cJ
    cfv
    #
    @86
    @67
    @87
    cJ
    @49
    @52
    @66
    df-ov
    fveq2i
    @65
    @27
    @86
    @25
    wcel
    #
    @88
    @86
    wceq
    @65
    wph
    @27
    @75
    ovoliun.j
    syl
    @65
    @50
    @64
    @89
    @76
    @77
    @49
    @52
    cn
    cn
    opelxpi
    syl2anc
    cn
    @25
    @86
    cJ
    f1ocnvfv2
    syl2anc
    syl5eq
    #
    fveq2d
    @49
    @52
    vn
    vex
    #
    vj
    vex
    #
    op1st
    syl6eq
    fveq2d
    @65
    @80
    @86
    c2nd
    cfv
    @52
    @65
    @79
    @86
    c2nd
    @90
    fveq2d
    @49
    @52
    @91
    @92
    op2nd
    syl6eq
    fveq12d
    eqtrd
    #
    fveq2d
    breq1d
    @65
    @72
    @57
    @41
    clt
    @65
    @69
    @54
    c2nd
    @93
    fveq2d
    breq2d
    anbi12d
    biimprd
    @45
    @74
    vm
    @67
    cn
    @38
    @67
    wceq
    #
    @42
    @71
    @44
    @73
    @94
    @40
    @70
    @41
    clt
    @94
    @39
    @69
    c1st
    @38
    @67
    cH
    fveq2
    #
    fveq2d
    breq1d
    @94
    @43
    @72
    @41
    clt
    @94
    @39
    @69
    c2nd
    @95
    fveq2d
    breq2d
    anbi12d
    rspcev
    syl6an
    rexlimdva
    mpd
    rexlimdv3a
    syl5bi
    ralrimiv
    wph
    @6
    @13
    @37
    @47
    wb
    @8
    @32
    vz
    @0
    vm
    cH
    ovolfioo
    syl2anc
    mpbird
    @0
    cU
    cH
    ovoliun.u
    ovollb
    syl2anc
    wph
    @3
    @5
    cle
    wbr
    #
    @41
    @5
    cle
    wbr
    #
    vz
    @2
    wral
    #
    wph
    @98
    @52
    cU
    cfv
    #
    @5
    cle
    wbr
    #
    vj
    cn
    wral
    #
    wph
    @100
    vj
    cn
    wph
    @64
    wa
    #
    vw
    cv
    #
    cJ
    cfv
    #
    c1st
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vw
    c1
    @52
    cfz
    co
    #
    wral
    #
    vx
    cr
    wrex
    #
    @100
    @102
    @108
    cfn
    wcel
    @105
    cr
    wcel
    #
    vw
    @108
    wral
    #
    @110
    c1
    @52
    fzfi
    wph
    @112
    @64
    wph
    @111
    vw
    @108
    wph
    @28
    @103
    cn
    wcel
    #
    @111
    @103
    @108
    wcel
    #
    @29
    @103
    @52
    elfznn
    @28
    @113
    wa
    @104
    @25
    wcel
    @105
    cn
    wcel
    @111
    cn
    @25
    @103
    cJ
    ffvelrn
    @104
    cn
    cn
    xp1st
    @105
    nnre
    3syl
    syl2an
    #
    ralrimiva
    adantr
    vx
    vw
    @108
    @105
    fimaxre3
    sylancr
    @102
    @109
    @100
    vx
    cr
    @102
    @106
    cr
    wcel
    #
    wa
    @109
    @105
    @106
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cle
    wbr
    #
    vw
    @108
    wral
    #
    @100
    wph
    @116
    @109
    @120
    wi
    @64
    wph
    @116
    wa
    #
    @107
    @119
    vw
    @108
    @121
    @114
    wa
    #
    @107
    @106
    @118
    cle
    wbr
    #
    @119
    @116
    @123
    wph
    @114
    @106
    fllep1
    ad2antlr
    @122
    @111
    @116
    @118
    cr
    wcel
    #
    @107
    @123
    wa
    @119
    wi
    wph
    @114
    @111
    @116
    @115
    adantlr
    wph
    @116
    @114
    simplr
    @116
    @124
    wph
    @114
    @116
    @118
    @116
    @117
    @106
    flcl
    peano2zd
    #
    zred
    ad2antlr
    @105
    @106
    @118
    letr
    syl3anc
    mpan2d
    ralimdva
    adantlr
    @102
    @116
    @120
    @100
    @102
    @116
    @120
    wa
    #
    wa
    #
    vw
    cA
    cB
    cS
    cT
    cU
    vk
    vn
    cF
    cG
    cH
    cJ
    @52
    @118
    ovoliun.t
    ovoliun.g
    @127
    wph
    @50
    @7
    wph
    @64
    @126
    simpll
    #
    ovoliun.a
    sylan
    @127
    wph
    @50
    cA
    covol
    cfv
    #
    cr
    wcel
    @128
    ovoliun.v
    sylan
    @127
    wph
    @4
    cr
    wcel
    @128
    ovoliun.r
    syl
    @127
    wph
    cB
    crp
    wcel
    @128
    ovoliun.b
    syl
    ovoliun.s
    ovoliun.u
    ovoliun.h
    @127
    wph
    @27
    @128
    ovoliun.j
    syl
    @127
    wph
    @24
    @128
    ovoliun.f
    syl
    @127
    wph
    @50
    @62
    @128
    ovoliun.x1
    sylan
    @127
    wph
    @50
    cS
    crn
    cxr
    clt
    csup
    @129
    cB
    c2
    @49
    cexp
    co
    cdiv
    co
    caddc
    co
    cle
    wbr
    @128
    ovoliun.x2
    sylan
    wph
    @64
    @126
    simplr
    @116
    @118
    cz
    wcel
    @102
    @120
    @125
    ad2antrl
    @102
    @116
    @120
    simprr
    ovoliunlem1
    expr
    syld
    rexlimdva
    mpd
    ralrimiva
    wph
    @13
    @14
    cU
    cn
    wfn
    @98
    @101
    wb
    @32
    @34
    cn
    @10
    cU
    ffn
    @97
    @100
    vz
    vj
    cn
    cU
    @41
    @99
    @5
    cle
    breq1
    ralrn
    4syl
    mpbird
    wph
    @9
    @5
    cxr
    wcel
    @96
    @98
    wb
    @35
    @36
    vz
    @2
    @5
    supxrleub
    syl2anc
    mpbird
    xrletrd
end
