include "cn.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "cq.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "c1st.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c2nd.mm"
include "cmul.mm"
include "cmin.mm"
include "wceq.mm"
include "cc0.mm"
include "wne.mm"
include "cabs.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "copab.mm"
include "crab.mm"
include "cen.mm"
include "cfl.mm"
include "cneg.mm"
include "cfz.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "cz.mm"
include "pellexlem4.mm"
include "cfn.mm"
include "fzfi.mm"
include "diffi.mm"
include "mp1i.mm"
include "cop.mm"
include "wex.mm"
include "elopab.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "vex.mm"
include "op1st.mm"
include "oveq1i.mm"
include "op2nd.mm"
include "oveq2i.mm"
include "oveq12i.mm"
include "syl6eq.mm"
include "ad2antrl.mm"
include "simprrl.mm"
include "simpl.mm"
include "simprr.mm"
include "ad2antll.mm"
include "cle.mm"
include "nnz.mm"
include "ad2antrr.mm"
include "zsqcl.mm"
include "syl.mm"
include "simplr.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "zsubcld.mm"
include "cr.mm"
include "1re.mm"
include "2re.mm"
include "nnre.mm"
include "cn0.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "resqrtcld.mm"
include "remulcl.mm"
include "sylancr.mm"
include "readdcl.mm"
include "flcld.mm"
include "znegcld.mm"
include "zred.mm"
include "nn0abscl.mm"
include "nn0zd.mm"
include "peano2re.mm"
include "flltp1.mm"
include "lttrd.mm"
include "wb.mm"
include "zleltp1.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "absle.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "w3a.mm"
include "elfz.mm"
include "biimpar.mm"
include "syl31anc.mm"
include "syl12anc.mm"
include "adantlr.mm"
include "simprl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "eqeltrd.mm"
include "ex.mm"
include "exlimdvv.mm"
include "syl5bi.mm"
include "imp.mm"
include "fiphp3d.mm"
include "wi.mm"
include "eldif.mm"
include "elfzelz.mm"
include "simp2.mm"
include "velsn.mm"
include "biimpri.mm"
include "necon3bi.mm"
include "3ad2ant3.mm"
include "jca.mm"
include "3exp.mm"
include "syl5.mm"
include "impd.mm"
include "simp2l.mm"
include "simp2r.mm"
include "cdom.mm"
include "cxp.mm"
include "cvv.mm"
include "wss.mm"
include "nnex.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssdomg.mm"
include "mp2.mm"
include "xpnnen.mm"
include "domentr.mm"
include "mp2an.mm"
include "ensym.mm"
include "ssexi.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "jca32.mm"
include "2eximdv.mm"
include "3imtr4g.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "ssrdv.mm"
include "3adant3.mm"
include "mpsyl.mm"
include "endomtr.mm"
include "sbth.mm"
include "syld.mm"
include "reximdv2.mm"
include "mpd.mm"

theorem pellexlem5
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  let wph: wff ph

  disjoint D x
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint x z
  disjoint y z
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
  assert |- ( ( D e. NN /\ -. ( sqrt ` D ) e. QQ ) -> E. x e. ZZ ( x =/= 0 /\ { <. y , z >. | ( ( y e. NN /\ z e. NN ) /\ ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) ) = x ) } ~~ NN ) )

  proof
    cD
    cn
    wcel
    #
    cD
    csqrt
    cfv
    #
    cq
    wcel
    wn
    #
    wa
    #
    va
    cv
    #
    c1st
    cfv
    #
    c2
    cexp
    co
    #
    cD
    @4
    c2nd
    cfv
    #
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
    vx
    cv
    #
    wceq
    #
    va
    vy
    cv
    #
    cn
    wcel
    #
    vz
    cv
    #
    cn
    wcel
    #
    wa
    #
    @13
    c2
    cexp
    co
    #
    cD
    @15
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
    cc0
    wne
    #
    @21
    cabs
    cfv
    #
    c1
    c2
    @1
    cmul
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    wa
    #
    vy
    vz
    copab
    #
    crab
    #
    cn
    cen
    wbr
    #
    vx
    @25
    cfl
    cfv
    #
    cneg
    #
    @32
    cfz
    co
    #
    cc0
    csn
    #
    cdif
    #
    wrex
    @11
    cc0
    wne
    #
    @17
    @21
    @11
    wceq
    #
    wa
    #
    vy
    vz
    copab
    #
    cn
    cen
    wbr
    #
    wa
    #
    vx
    cz
    wrex
    @3
    va
    vx
    @29
    @36
    @10
    vy
    vz
    cD
    pellexlem4
    @34
    cfn
    wcel
    @36
    cfn
    wcel
    @3
    @33
    @32
    fzfi
    @34
    @35
    diffi
    mp1i
    @3
    @4
    @29
    wcel
    #
    @10
    @36
    wcel
    #
    @43
    @4
    @13
    @15
    cop
    #
    wceq
    #
    @28
    wa
    #
    vz
    wex
    vy
    wex
    @3
    @44
    @28
    vy
    vz
    @4
    elopab
    @3
    @47
    @44
    vy
    vz
    @3
    @47
    @44
    @3
    @47
    wa
    #
    @10
    @21
    @36
    @46
    @10
    @21
    wceq
    @3
    @28
    @46
    @10
    @45
    c1st
    cfv
    #
    c2
    cexp
    co
    #
    cD
    @45
    c2nd
    cfv
    #
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
    @21
    @46
    @6
    @50
    @9
    @53
    cmin
    @46
    @5
    @49
    c2
    cexp
    @4
    @45
    c1st
    fveq2
    oveq1d
    @46
    @8
    @52
    cD
    cmul
    @46
    @7
    @51
    c2
    cexp
    @4
    @45
    c2nd
    fveq2
    oveq1d
    oveq2d
    oveq12d
    @50
    @18
    @53
    @20
    cmin
    @49
    @13
    c2
    cexp
    @13
    @15
    vy
    vex
    #
    vz
    vex
    #
    op1st
    oveq1i
    @52
    @19
    cD
    cmul
    @51
    @15
    c2
    cexp
    @13
    @15
    @55
    @56
    op2nd
    oveq1i
    oveq2i
    oveq12i
    #
    syl6eq
    ad2antrl
    @48
    @21
    @34
    wcel
    #
    @22
    @21
    @36
    wcel
    @0
    @47
    @58
    @2
    @0
    @47
    wa
    @17
    @0
    @26
    @58
    @0
    @46
    @17
    @27
    simprrl
    @0
    @47
    simpl
    @28
    @26
    @0
    @46
    @17
    @22
    @26
    simprr
    ad2antll
    @17
    @0
    @26
    wa
    #
    wa
    #
    @21
    cz
    wcel
    #
    @33
    cz
    wcel
    #
    @32
    cz
    wcel
    #
    @33
    @21
    cle
    wbr
    @21
    @32
    cle
    wbr
    wa
    #
    @58
    @60
    @18
    @20
    @60
    @13
    cz
    wcel
    #
    @18
    cz
    wcel
    @14
    @65
    @16
    @59
    @13
    nnz
    ad2antrr
    @13
    zsqcl
    syl
    @60
    cD
    @19
    @0
    cD
    cz
    wcel
    @17
    @26
    cD
    nnz
    ad2antrl
    @60
    @15
    cz
    wcel
    @19
    cz
    wcel
    @60
    @15
    @14
    @16
    @59
    simplr
    nnzd
    @15
    zsqcl
    syl
    zmulcld
    zsubcld
    #
    @60
    @32
    @60
    @25
    @60
    c1
    cr
    wcel
    @24
    cr
    wcel
    #
    @25
    cr
    wcel
    #
    1re
    @60
    c2
    cr
    wcel
    @1
    cr
    wcel
    @67
    2re
    @60
    cD
    @0
    cD
    cr
    wcel
    @17
    @26
    cD
    nnre
    ad2antrl
    @60
    cD
    @0
    cD
    cn0
    wcel
    @17
    @26
    cD
    nnnn0
    ad2antrl
    nn0ge0d
    resqrtcld
    c2
    @1
    remulcl
    sylancr
    c1
    @24
    readdcl
    sylancr
    #
    flcld
    #
    znegcld
    @70
    @60
    @21
    cr
    wcel
    #
    @32
    cr
    wcel
    #
    @23
    @32
    cle
    wbr
    #
    @64
    @60
    @21
    @66
    zred
    @60
    @32
    @70
    zred
    #
    @60
    @73
    @23
    @32
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @60
    @23
    @25
    @75
    @60
    @23
    @60
    @23
    @60
    @61
    @23
    cn0
    wcel
    @66
    @21
    nn0abscl
    syl
    nn0zd
    #
    zred
    @69
    @60
    @72
    @75
    cr
    wcel
    @74
    @32
    peano2re
    syl
    @17
    @0
    @26
    simprr
    @60
    @68
    @25
    @75
    clt
    wbr
    @69
    @25
    flltp1
    syl
    lttrd
    @60
    @23
    cz
    wcel
    @63
    @73
    @76
    wb
    @77
    @70
    @23
    @32
    zleltp1
    syl2anc
    mpbird
    @71
    @72
    wa
    @73
    @64
    @21
    @32
    absle
    biimpa
    syl21anc
    @61
    @62
    @63
    w3a
    @58
    @64
    @21
    @33
    @32
    elfz
    biimpar
    syl31anc
    syl12anc
    adantlr
    @28
    @22
    @3
    @46
    @17
    @22
    @26
    simprl
    ad2antll
    @21
    @34
    cc0
    eldifsn
    sylanbrc
    eqeltrd
    ex
    exlimdvv
    syl5bi
    imp
    fiphp3d
    @3
    @31
    @42
    vx
    @36
    cz
    @3
    @11
    @36
    wcel
    #
    @31
    @11
    cz
    wcel
    #
    @42
    wa
    #
    @3
    @78
    @79
    @37
    wa
    #
    @31
    @80
    wi
    @78
    @11
    @34
    wcel
    #
    @11
    @35
    wcel
    #
    wn
    #
    wa
    @3
    @81
    @11
    @34
    @35
    eldif
    @3
    @82
    @84
    @81
    @82
    @79
    @3
    @84
    @81
    wi
    @11
    @33
    @32
    elfzelz
    @3
    @79
    @84
    @81
    @3
    @79
    @84
    w3a
    @79
    @37
    @3
    @79
    @84
    simp2
    @84
    @3
    @37
    @79
    @83
    @11
    cc0
    @83
    @11
    cc0
    wceq
    vx
    cc0
    velsn
    biimpri
    necon3bi
    3ad2ant3
    jca
    3exp
    syl5
    impd
    syl5bi
    @3
    @81
    @31
    @80
    @3
    @81
    @31
    w3a
    #
    @79
    @37
    @41
    @3
    @79
    @37
    @31
    simp2l
    @3
    @79
    @37
    @31
    simp2r
    @85
    @40
    cn
    cdom
    wbr
    #
    cn
    @40
    cdom
    wbr
    #
    @41
    @40
    cn
    cn
    cxp
    #
    cdom
    wbr
    #
    @88
    cn
    cen
    wbr
    @86
    @88
    cvv
    wcel
    @40
    @88
    wss
    @89
    cn
    cn
    nnex
    nnex
    xpex
    #
    @38
    vy
    vz
    cn
    cn
    opabssxp
    #
    @40
    @88
    cvv
    ssdomg
    mp2
    xpnnen
    @40
    @88
    cn
    domentr
    mp2an
    @85
    cn
    @30
    cen
    wbr
    #
    @30
    @40
    cdom
    wbr
    #
    @87
    @31
    @3
    @92
    @81
    @30
    cn
    ensym
    3ad2ant3
    @40
    cvv
    wcel
    @85
    @30
    @40
    wss
    #
    @93
    @40
    @88
    @90
    @91
    ssexi
    @3
    @81
    @94
    @31
    @3
    @81
    wa
    #
    vb
    @30
    @40
    vb
    cv
    #
    @30
    wcel
    @96
    @29
    wcel
    #
    @96
    c1st
    cfv
    #
    c2
    cexp
    co
    #
    cD
    @96
    c2nd
    cfv
    #
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
    @11
    wceq
    #
    wa
    @95
    @96
    @40
    wcel
    #
    @12
    @104
    va
    @96
    @29
    @4
    @96
    wceq
    #
    @10
    @103
    @11
    @106
    @6
    @99
    @9
    @102
    cmin
    @106
    @5
    @98
    c2
    cexp
    @4
    @96
    c1st
    fveq2
    oveq1d
    @106
    @8
    @101
    cD
    cmul
    @106
    @7
    @100
    c2
    cexp
    @4
    @96
    c2nd
    fveq2
    oveq1d
    oveq2d
    oveq12d
    eqeq1d
    elrab
    @95
    @104
    @97
    @105
    @95
    @104
    @97
    @105
    @95
    @104
    wa
    #
    @96
    @45
    wceq
    #
    @28
    wa
    #
    vz
    wex
    vy
    wex
    @108
    @39
    wa
    #
    vz
    wex
    vy
    wex
    @97
    @105
    @107
    @109
    @110
    vy
    vz
    @107
    @109
    @110
    @107
    @109
    wa
    #
    @108
    @17
    @38
    @107
    @108
    @28
    simprl
    @107
    @108
    @17
    @27
    simprrl
    @111
    @21
    @103
    @11
    @108
    @21
    @103
    wceq
    @107
    @28
    @108
    @103
    @54
    @21
    @108
    @99
    @50
    @102
    @53
    cmin
    @108
    @98
    @49
    c2
    cexp
    @96
    @45
    c1st
    fveq2
    oveq1d
    @108
    @101
    @52
    cD
    cmul
    @108
    @100
    @51
    c2
    cexp
    @96
    @45
    c2nd
    fveq2
    oveq1d
    oveq2d
    oveq12d
    @57
    syl6req
    ad2antrl
    @95
    @104
    @109
    simplr
    eqtrd
    jca32
    ex
    2eximdv
    @28
    vy
    vz
    @96
    elopab
    @39
    vy
    vz
    @96
    elopab
    3imtr4g
    expimpd
    ancomsd
    syl5bi
    ssrdv
    3adant3
    @30
    @40
    cvv
    ssdomg
    mpsyl
    cn
    @30
    @40
    endomtr
    syl2anc
    @40
    cn
    sbth
    sylancr
    jca32
    3exp
    syld
    impd
    reximdv2
    mpd
end
