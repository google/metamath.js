include "cn.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "cq.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "wceq.mm"
include "copab.mm"
include "cen.mm"
include "wbr.mm"
include "c1.mm"
include "wrex.mm"
include "cz.mm"
include "c1st.mm"
include "cabs.mm"
include "cmo.mm"
include "c2nd.mm"
include "cop.mm"
include "cfz.mm"
include "cxp.mm"
include "csdm.mm"
include "com.mm"
include "cfn.mm"
include "fzfi.mm"
include "xpfi.mm"
include "mp2an.mm"
include "isfinite.mm"
include "mpbi.mm"
include "nnenom.mm"
include "ensymi.mm"
include "sdomentr.mm"
include "ensym.mm"
include "ad2antll.mm"
include "sylancr.mm"
include "opabssxp.mm"
include "sseli.mm"
include "cvv.mm"
include "simprrl.mm"
include "nnzd.mm"
include "simpllr.mm"
include "simplr.mm"
include "nnabscl.mm"
include "syl2anc.mm"
include "zmodfz.mm"
include "simprrr.mm"
include "jca.mm"
include "ex.mm"
include "elxp7.mm"
include "opelxp.mm"
include "3imtr4g.mm"
include "syl5.mm"
include "imp.mm"
include "adantlrr.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "opeq12d.mm"
include "fphpd.mm"
include "wi.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveqan12d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "cbvopabv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "wex.mm"
include "elopab.mm"
include "w3a.mm"
include "simp3ll.mm"
include "3expb.mm"
include "3ad2ant1.mm"
include "simp3lr.mm"
include "simp1lr.mm"
include "3adant1r.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "simp2ll.mm"
include "3adant2l.mm"
include "simp2lr.mm"
include "simp2l.mm"
include "simp1rl.mm"
include "simp3l.mm"
include "simp3.mm"
include "simp2.mm"
include "simp1.mm"
include "3netr3d.mm"
include "vex.mm"
include "opth.mm"
include "necon3abii.mm"
include "sylib.mm"
include "syl3anc.mm"
include "simp1rr.mm"
include "3adant1l.mm"
include "simp2rr.mm"
include "simp3r.mm"
include "ovex.mm"
include "simprl.mm"
include "simpll.mm"
include "fveq2d.mm"
include "op1st.mm"
include "syl6eq.mm"
include "3eqtr3d.mm"
include "simprr.mm"
include "op2nd.mm"
include "3adant3.mm"
include "mpd.mm"
include "simpld.mm"
include "simprd.mm"
include "pellexlem6.mm"
include "3exp.mm"
include "exlimdvv.mm"
include "syl5bi.mm"
include "impd.mm"
include "sylan2i.mm"
include "rexlimdvv.mm"
include "mpdan.mm"
include "pellexlem5.mm"
include "r19.29a.mm"

theorem pellex
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cF: class F
  let vz: setvar z
  let wph: wff ph

  disjoint D x
  disjoint D y
  disjoint x y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint A c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint A d
  disjoint e f
  disjoint e g
  disjoint A e
  disjoint f g
  disjoint A f
  disjoint A g
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B g
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C g
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D g
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E d
  disjoint E e
  disjoint E f
  disjoint E g
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint g x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint g y
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint g z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint g ph
  assert |- ( ( D e. NN /\ -. ( sqrt ` D ) e. QQ ) -> E. x e. NN E. y e. NN ( ( x ^ 2 ) - ( D x. ( y ^ 2 ) ) ) = 1 )

  proof
    cD
    cn
    wcel
    #
    cD
    csqrt
    cfv
    cq
    wcel
    wn
    #
    wa
    #
    va
    cv
    #
    cc0
    wne
    #
    vb
    cv
    #
    cn
    wcel
    #
    vc
    cv
    #
    cn
    wcel
    #
    wa
    #
    @5
    c2
    cexp
    co
    #
    cD
    @7
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @3
    wceq
    #
    wa
    #
    vb
    vc
    copab
    #
    cn
    cen
    wbr
    #
    wa
    #
    vx
    cv
    c2
    cexp
    co
    cD
    vy
    cv
    c2
    cexp
    co
    cmul
    co
    cmin
    co
    c1
    wceq
    vy
    cn
    wrex
    vx
    cn
    wrex
    #
    va
    cz
    @2
    @3
    cz
    wcel
    #
    wa
    #
    @18
    wa
    #
    vd
    cv
    #
    ve
    cv
    #
    wne
    #
    @23
    c1st
    cfv
    #
    @3
    cabs
    cfv
    #
    cmo
    co
    #
    @23
    c2nd
    cfv
    #
    @27
    cmo
    co
    #
    cop
    #
    @24
    c1st
    cfv
    #
    @27
    cmo
    co
    #
    @24
    c2nd
    cfv
    #
    @27
    cmo
    co
    #
    cop
    #
    wceq
    #
    wa
    #
    ve
    @16
    wrex
    vd
    @16
    wrex
    #
    @19
    @22
    vd
    ve
    @16
    cc0
    @27
    c1
    cmin
    co
    #
    cfz
    co
    #
    @41
    cxp
    #
    @31
    @36
    @22
    @42
    cn
    csdm
    wbr
    #
    cn
    @16
    cen
    wbr
    #
    @42
    @16
    csdm
    wbr
    @42
    com
    csdm
    wbr
    #
    com
    cn
    cen
    wbr
    @43
    @42
    cfn
    wcel
    #
    @45
    @41
    cfn
    wcel
    #
    @47
    @46
    cc0
    @40
    fzfi
    #
    @48
    @41
    @41
    xpfi
    mp2an
    @42
    isfinite
    mpbi
    cn
    com
    nnenom
    ensymi
    @42
    com
    cn
    sdomentr
    mp2an
    @17
    @44
    @21
    @4
    @16
    cn
    ensym
    ad2antll
    @42
    cn
    @16
    sdomentr
    sylancr
    @21
    @4
    @23
    @16
    wcel
    #
    @31
    @42
    wcel
    #
    @17
    @21
    @4
    wa
    #
    @49
    @50
    @49
    @23
    cn
    cn
    cxp
    #
    wcel
    #
    @51
    @50
    @16
    @52
    @23
    @14
    vb
    vc
    cn
    cn
    opabssxp
    sseli
    @51
    @23
    cvv
    cvv
    cxp
    wcel
    #
    @26
    cn
    wcel
    #
    @29
    cn
    wcel
    #
    wa
    wa
    #
    @28
    @41
    wcel
    #
    @30
    @41
    wcel
    #
    wa
    #
    @53
    @50
    @51
    @57
    @60
    @51
    @57
    wa
    #
    @58
    @59
    @61
    @26
    cz
    wcel
    @27
    cn
    wcel
    #
    @58
    @61
    @26
    @51
    @54
    @55
    @56
    simprrl
    nnzd
    @61
    @20
    @4
    @62
    @2
    @20
    @4
    @57
    simpllr
    @21
    @4
    @57
    simplr
    @3
    nnabscl
    syl2anc
    #
    @26
    @27
    zmodfz
    syl2anc
    @61
    @29
    cz
    wcel
    @62
    @59
    @61
    @29
    @51
    @54
    @55
    @56
    simprrr
    nnzd
    @63
    @29
    @27
    zmodfz
    syl2anc
    jca
    ex
    @23
    cn
    cn
    elxp7
    @28
    @30
    @41
    @41
    opelxp
    3imtr4g
    syl5
    imp
    adantlrr
    vd
    ve
    weq
    #
    @28
    @33
    @30
    @35
    @64
    @26
    @32
    @27
    cmo
    @23
    @24
    c1st
    fveq2
    oveq1d
    @64
    @29
    @34
    @27
    cmo
    @23
    @24
    c2nd
    fveq2
    oveq1d
    opeq12d
    fphpd
    @21
    @4
    @39
    @19
    @17
    @51
    @39
    @19
    @51
    @38
    @19
    vd
    ve
    @16
    @16
    @24
    @16
    wcel
    #
    @51
    @49
    @24
    vf
    cv
    #
    cn
    wcel
    #
    vg
    cv
    #
    cn
    wcel
    #
    wa
    #
    @66
    c2
    cexp
    co
    #
    cD
    @68
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @3
    wceq
    #
    wa
    #
    vf
    vg
    copab
    #
    wcel
    #
    @38
    @19
    wi
    #
    @65
    @78
    @16
    @77
    @24
    @15
    @76
    vb
    vc
    vf
    vg
    vb
    vf
    weq
    #
    vc
    vg
    weq
    #
    wa
    #
    @9
    @70
    @14
    @75
    @80
    @6
    @67
    @81
    @8
    @69
    @5
    @66
    cn
    eleq1
    @7
    @68
    cn
    eleq1
    bi2anan9
    @82
    @13
    @74
    @3
    @80
    @81
    @10
    @71
    @12
    @73
    cmin
    @5
    @66
    c2
    cexp
    oveq1
    @81
    @11
    @72
    cD
    cmul
    @7
    @68
    c2
    cexp
    oveq1
    oveq2d
    oveqan12d
    eqeq1d
    anbi12d
    cbvopabv
    eleq2i
    biimpi
    @51
    @49
    @78
    @79
    @49
    @23
    @5
    @7
    cop
    #
    wceq
    #
    @15
    wa
    #
    vc
    wex
    vb
    wex
    @51
    @78
    @79
    wi
    #
    @15
    vb
    vc
    @23
    elopab
    @51
    @85
    @86
    vb
    vc
    @51
    @85
    @86
    @78
    @24
    @66
    @68
    cop
    #
    wceq
    #
    @76
    wa
    #
    vg
    wex
    vf
    wex
    @51
    @85
    wa
    #
    @79
    @76
    vf
    vg
    @24
    elopab
    @90
    @89
    @79
    vf
    vg
    @90
    @89
    @38
    @19
    @90
    @89
    @38
    w3a
    #
    @5
    @7
    @3
    cD
    @66
    @68
    vx
    vy
    @90
    @89
    @6
    @38
    @51
    @84
    @15
    @6
    @6
    @8
    @14
    @51
    @84
    simp3ll
    3expb
    3ad2ant1
    @90
    @89
    @8
    @38
    @51
    @84
    @15
    @8
    @6
    @8
    @14
    @51
    @84
    simp3lr
    3expb
    3ad2ant1
    @51
    @89
    @38
    @20
    @85
    @2
    @20
    @4
    @89
    @38
    simp1lr
    3adant1r
    @90
    @89
    @0
    @38
    @0
    @1
    @20
    @4
    @85
    simp-4l
    3ad2ant1
    @90
    @89
    @1
    @38
    @0
    @1
    @20
    @4
    @85
    simp-4r
    3ad2ant1
    @90
    @76
    @38
    @67
    @88
    @67
    @69
    @75
    @90
    @38
    simp2ll
    3adant2l
    @90
    @76
    @38
    @69
    @88
    @67
    @69
    @75
    @90
    @38
    simp2lr
    3adant2l
    @91
    @88
    @84
    @25
    @82
    wn
    #
    @90
    @88
    @76
    @38
    simp2l
    #
    @84
    @15
    @51
    @89
    @38
    simp1rl
    #
    @90
    @89
    @25
    @37
    simp3l
    @88
    @84
    @25
    w3a
    #
    @83
    @87
    wne
    @92
    @95
    @23
    @24
    @83
    @87
    @88
    @84
    @25
    simp3
    @88
    @84
    @25
    simp2
    @88
    @84
    @25
    simp1
    3netr3d
    @82
    @83
    @87
    @5
    @7
    @66
    @68
    vb
    vex
    #
    vc
    vex
    #
    opth
    necon3abii
    sylib
    syl3anc
    @21
    @4
    @85
    @89
    @38
    simp1lr
    @85
    @89
    @38
    @14
    @51
    @9
    @14
    @84
    @89
    @38
    simp1rr
    3adant1l
    @70
    @75
    @88
    @90
    @38
    simp2rr
    @91
    @5
    @27
    cmo
    co
    #
    @66
    @27
    cmo
    co
    #
    wceq
    #
    @7
    @27
    cmo
    co
    #
    @68
    @27
    cmo
    co
    #
    wceq
    #
    @91
    @84
    @88
    @37
    @100
    @103
    wa
    #
    @94
    @93
    @90
    @89
    @25
    @37
    simp3r
    @84
    @88
    @37
    w3a
    #
    @28
    @33
    wceq
    #
    @30
    @35
    wceq
    #
    wa
    #
    @104
    @105
    @37
    @108
    @84
    @88
    @37
    simp3
    @28
    @30
    @33
    @35
    @26
    @27
    cmo
    ovex
    @29
    @27
    cmo
    ovex
    opth
    sylib
    @84
    @88
    @108
    @104
    wi
    @37
    @84
    @88
    wa
    #
    @108
    @104
    @109
    @108
    wa
    #
    @100
    @103
    @110
    @28
    @33
    @98
    @99
    @109
    @106
    @107
    simprl
    @110
    @26
    @5
    @27
    cmo
    @110
    @26
    @83
    c1st
    cfv
    @5
    @110
    @23
    @83
    c1st
    @84
    @88
    @108
    simpll
    #
    fveq2d
    @5
    @7
    @96
    @97
    op1st
    syl6eq
    oveq1d
    @110
    @32
    @66
    @27
    cmo
    @110
    @32
    @87
    c1st
    cfv
    @66
    @110
    @24
    @87
    c1st
    @84
    @88
    @108
    simplr
    #
    fveq2d
    @66
    @68
    vf
    vex
    #
    vg
    vex
    #
    op1st
    syl6eq
    oveq1d
    3eqtr3d
    @110
    @30
    @35
    @101
    @102
    @109
    @106
    @107
    simprr
    @110
    @29
    @7
    @27
    cmo
    @110
    @29
    @83
    c2nd
    cfv
    @7
    @110
    @23
    @83
    c2nd
    @111
    fveq2d
    @5
    @7
    @96
    @97
    op2nd
    syl6eq
    oveq1d
    @110
    @34
    @68
    @27
    cmo
    @110
    @34
    @87
    c2nd
    cfv
    @68
    @110
    @24
    @87
    c2nd
    @112
    fveq2d
    @66
    @68
    @113
    @114
    op2nd
    syl6eq
    oveq1d
    3eqtr3d
    jca
    ex
    3adant3
    mpd
    syl3anc
    #
    simpld
    @91
    @100
    @103
    @115
    simprd
    pellexlem6
    3exp
    exlimdvv
    syl5bi
    ex
    exlimdvv
    syl5bi
    impd
    sylan2i
    rexlimdvv
    imp
    adantlrr
    mpdan
    va
    vb
    vc
    cD
    pellexlem5
    r19.29a
end
