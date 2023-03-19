include "wa.mm"
include "cv.mm"
include "cprod.mm"
include "csn.mm"
include "cmul.mm"
include "co.mm"
include "cxp.mm"
include "ciun.mm"
include "csb.mm"
include "cun.mm"
include "wceq.mm"
include "simpr.mm"
include "sylib.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfcprod.mm"
include "weq.mm"
include "csbeq1a.mm"
include "wcel.mm"
include "adantr.mm"
include "prodeq12dv.mm"
include "cbvprodi.mm"
include "cc.mm"
include "wss.mm"
include "unssbd.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "cfn.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "ralrimivva.mm"
include "nfral.mm"
include "raleqbidv.mm"
include "r19.21bi.mm"
include "fprodcl.mm"
include "csbeq1.mm"
include "prodsn.mm"
include "syl2anc.mm"
include "c2nd.mm"
include "cfv.mm"
include "cres.mm"
include "snfi.mm"
include "xpfi.mm"
include "sylancr.mm"
include "wf1o.mm"
include "2ndconst.mm"
include "syl.mm"
include "fvres.mm"
include "adantl.mm"
include "mpan9.mm"
include "fprodf1o.mm"
include "cop.mm"
include "wex.mm"
include "elxp.mm"
include "nfv.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfex.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "eleq1.mm"
include "velsn.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "eleq2d.mm"
include "pm5.32i.mm"
include "syl6bbr.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "cbvex.mm"
include "bitri.mm"
include "nfcsb.mm"
include "nfeq2.mm"
include "ad2antlr.mm"
include "ad2antrl.mm"
include "fveq2.mm"
include "op2nd.mm"
include "syl6req.mm"
include "3eqtrd.mm"
include "expl.mm"
include "exlimd.mm"
include "syl5bi.mm"
include "imp.mm"
include "prodeq2dv.mm"
include "eqtr4d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "wel.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "disjsn.mm"
include "eqidd.mm"
include "ssfi.mm"
include "sselda.mm"
include "anassrs.mm"
include "syldan.mm"
include "fprodsplit.mm"
include "c1st.mm"
include "wrex.mm"
include "eliun.mm"
include "xp1st.mm"
include "elsni.mm"
include "biimparc.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "anim12i.mm"
include "elin.mm"
include "3imtr4i.mm"
include "noel.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "syl5.mm"
include "ssrdv.mm"
include "ss0.mm"
include "iunxun.mm"
include "nfxp.mm"
include "sneq.mm"
include "xpeq12d.mm"
include "cbviun.mm"
include "iunxsn.mm"
include "eqtri.mm"
include "uneq2i.mm"
include "a1i.mm"
include "iunfi.mm"
include "simprl.mm"
include "simprrl.mm"
include "opeq1d.mm"
include "simpll.mm"
include "simprrr.mm"
include "syl12anc.mm"
include "eqeltrd.mm"
include "ex.mm"
include "exlimdvv.mm"
include "rexlimdva.mm"
include "3eqtr4d.mm"

theorem fprod2dlem
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  assume fprod2d.1: |- ( z = <. j , k >. -> D = C )
  assume fprod2d.2: |- ( ph -> A e. Fin )
  assume fprod2d.3: |- ( ( ph /\ j e. A ) -> B e. Fin )
  assume fprod2d.4: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. CC )
  assume fprod2d.5: |- ( ph -> -. y e. x )
  assume fprod2d.6: |- ( ph -> ( x u. { y } ) C_ A )
  assume fprod2d.7: |- ( ps <-> prod_ j e. x prod_ k e. B C = prod_ z e. U_ j e. x ( { j } X. B ) D )

  disjoint A j
  disjoint A k
  disjoint B k
  disjoint B z
  disjoint C z
  disjoint D j
  disjoint D k
  disjoint j k
  disjoint j ph
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint ph z
  disjoint x z
  disjoint y z
  disjoint A m
  disjoint B m
  disjoint C m
  disjoint D m
  disjoint j m
  disjoint k m
  disjoint m ph
  disjoint m x
  disjoint m y
  disjoint m z
  assert |- ( ( ph /\ ps ) -> prod_ j e. ( x u. { y } ) prod_ k e. B C = prod_ z e. U_ j e. ( x u. { y } ) ( { j } X. B ) D )

  proof
    wph
    wps
    wa
    #
    vx
    cv
    #
    cB
    cC
    vk
    cprod
    #
    vj
    cprod
    #
    vy
    cv
    #
    csn
    #
    @2
    vj
    cprod
    #
    cmul
    co
    #
    vj
    @1
    vj
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    cD
    vz
    cprod
    #
    @5
    vj
    @4
    cB
    csb
    #
    cxp
    #
    cD
    vz
    cprod
    #
    cmul
    co
    #
    @1
    @5
    cun
    #
    @2
    vj
    cprod
    #
    vj
    @17
    @10
    ciun
    #
    cD
    vz
    cprod
    #
    @0
    @3
    @12
    @6
    @15
    cmul
    @0
    wps
    @3
    @12
    wceq
    wph
    wps
    simpr
    fprod2d.7
    sylib
    wph
    @6
    @15
    wceq
    wps
    wph
    @6
    @5
    vj
    vm
    cv
    #
    cB
    csb
    #
    vj
    @21
    cC
    csb
    #
    vk
    cprod
    #
    vm
    cprod
    #
    @15
    @5
    @2
    @24
    vj
    vm
    vm
    @2
    nfcv
    vj
    @22
    @23
    vk
    vj
    @21
    cB
    nfcsb1v
    #
    vj
    @21
    cC
    nfcsb1v
    nfcprod
    vj
    vm
    weq
    #
    cB
    @22
    cC
    @23
    vk
    vj
    @21
    cB
    csbeq1a
    #
    @27
    cC
    @23
    wceq
    vk
    cv
    #
    cB
    wcel
    #
    vj
    @21
    cC
    csbeq1a
    adantr
    prodeq12dv
    cbvprodi
    wph
    @25
    @13
    vj
    @4
    cC
    csb
    #
    vk
    cprod
    #
    @15
    wph
    @4
    cA
    wcel
    #
    @32
    cc
    wcel
    @25
    @32
    wceq
    wph
    @5
    cA
    wss
    @33
    wph
    @1
    @5
    cA
    fprod2d.6
    unssbd
    @4
    cA
    vy
    vex
    #
    snss
    sylibr
    #
    wph
    @13
    @31
    vk
    wph
    @33
    cB
    cfn
    wcel
    #
    vj
    cA
    wral
    @13
    cfn
    wcel
    #
    @35
    wph
    @36
    vj
    cA
    fprod2d.3
    ralrimiva
    @36
    @37
    vj
    @4
    cA
    vj
    @13
    cfn
    vj
    @4
    cB
    nfcsb1v
    #
    nfel1
    vj
    vy
    weq
    #
    cB
    @13
    cfn
    vj
    @4
    cB
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    #
    wph
    @31
    cc
    wcel
    #
    vk
    @13
    wph
    @33
    cC
    cc
    wcel
    #
    vk
    cB
    wral
    #
    vj
    cA
    wral
    @42
    vk
    @13
    wral
    #
    @35
    wph
    @43
    vj
    vk
    cA
    cB
    fprod2d.4
    ralrimivva
    @44
    @45
    vj
    @4
    cA
    @42
    vj
    vk
    @13
    @38
    vj
    @31
    cc
    vj
    @4
    cC
    nfcsb1v
    #
    nfel1
    nfral
    @39
    @43
    @42
    vk
    cB
    @13
    @40
    @39
    cC
    @31
    cc
    vj
    @4
    cC
    csbeq1a
    #
    eleq1d
    raleqbidv
    rspc
    sylc
    #
    r19.21bi
    fprodcl
    @24
    @32
    vm
    @4
    cA
    vm
    vy
    weq
    #
    @22
    @13
    @23
    @31
    vk
    vj
    @21
    @4
    cB
    csbeq1
    #
    @49
    @23
    @31
    wceq
    @29
    @22
    wcel
    vj
    @21
    @4
    cC
    csbeq1
    adantr
    prodeq12dv
    prodsn
    syl2anc
    wph
    @32
    @13
    vk
    @21
    @31
    csb
    #
    vm
    cprod
    #
    @15
    @13
    @31
    @51
    vk
    vm
    vm
    @31
    nfcv
    vk
    @21
    @31
    nfcsb1v
    #
    vk
    @21
    @31
    csbeq1a
    #
    cbvprodi
    wph
    @52
    @14
    vk
    vz
    cv
    #
    c2nd
    cfv
    #
    @31
    csb
    #
    vz
    cprod
    @15
    wph
    @13
    @51
    @14
    @57
    vm
    vz
    c2nd
    @14
    cres
    #
    @56
    vk
    @21
    @56
    @31
    csbeq1
    wph
    @5
    cfn
    wcel
    @37
    @14
    cfn
    wcel
    @4
    snfi
    @41
    @5
    @13
    xpfi
    sylancr
    wph
    @33
    @14
    @13
    @58
    wf1o
    @35
    @4
    @13
    cA
    2ndconst
    syl
    @55
    @14
    wcel
    #
    @55
    @58
    cfv
    @56
    wceq
    wph
    @55
    @14
    c2nd
    fvres
    adantl
    wph
    @45
    @21
    @13
    wcel
    @51
    cc
    wcel
    #
    @48
    @42
    @60
    vk
    @21
    @13
    vk
    @51
    cc
    @53
    nfel1
    vk
    vm
    weq
    @31
    @51
    cc
    @54
    eleq1d
    rspc
    mpan9
    fprodf1o
    wph
    @14
    cD
    @57
    vz
    wph
    @59
    cD
    @57
    wceq
    #
    @59
    @55
    @8
    @29
    cop
    #
    wceq
    #
    @39
    @30
    wa
    #
    wa
    #
    vk
    wex
    #
    vj
    wex
    #
    wph
    @61
    @59
    @55
    @21
    @29
    cop
    #
    wceq
    #
    @21
    @5
    wcel
    #
    @29
    @13
    wcel
    #
    wa
    #
    wa
    #
    vk
    wex
    #
    vm
    wex
    @67
    vm
    vk
    @55
    @5
    @13
    elxp
    @74
    @66
    vm
    vj
    @73
    vj
    vk
    @69
    @72
    vj
    @69
    vj
    nfv
    @70
    @71
    vj
    @70
    vj
    nfv
    vj
    vk
    @13
    @38
    nfcri
    nfan
    nfan
    nfex
    @66
    vm
    nfv
    vm
    vj
    weq
    #
    @73
    @65
    vk
    @75
    @69
    @63
    @72
    @64
    @75
    @68
    @62
    @55
    @21
    @8
    @29
    opeq1
    eqeq2d
    @75
    @72
    @39
    @71
    wa
    @64
    @75
    @70
    @39
    @71
    @75
    @70
    @8
    @5
    wcel
    @39
    @21
    @8
    @5
    eleq1
    vj
    @4
    velsn
    syl6bb
    anbi1d
    @39
    @30
    @71
    @39
    cB
    @13
    @29
    @40
    eleq2d
    pm5.32i
    syl6bbr
    anbi12d
    exbidv
    cbvex
    bitri
    wph
    @66
    @61
    vj
    wph
    vj
    nfv
    vj
    cD
    @57
    vj
    vk
    @56
    @31
    vj
    @56
    nfcv
    @46
    nfcsb
    nfeq2
    wph
    @65
    @61
    vk
    wph
    vk
    nfv
    vk
    cD
    @57
    vk
    @56
    @31
    nfcsb1v
    nfeq2
    wph
    @63
    @64
    @61
    wph
    @63
    wa
    #
    @64
    wa
    #
    cD
    cC
    @31
    @57
    @63
    cD
    cC
    wceq
    #
    wph
    @64
    fprod2d.1
    ad2antlr
    @39
    cC
    @31
    wceq
    @76
    @30
    @47
    ad2antrl
    @77
    @29
    @56
    wceq
    #
    @31
    @57
    wceq
    @63
    @79
    wph
    @64
    @63
    @56
    @62
    c2nd
    cfv
    @29
    @55
    @62
    c2nd
    fveq2
    @8
    @29
    vj
    vex
    vk
    vex
    op2nd
    syl6req
    ad2antlr
    vk
    @56
    @31
    csbeq1a
    syl
    3eqtrd
    expl
    exlimd
    exlimd
    syl5bi
    imp
    prodeq2dv
    eqtr4d
    syl5eq
    eqtrd
    syl5eq
    adantr
    oveq12d
    wph
    @18
    @7
    wceq
    wps
    wph
    @1
    @5
    @2
    @17
    vj
    wph
    vy
    vx
    wel
    wn
    @1
    @5
    cin
    #
    c0
    wceq
    fprod2d.5
    @1
    @4
    disjsn
    sylibr
    #
    wph
    @17
    eqidd
    wph
    cA
    cfn
    wcel
    @17
    cA
    wss
    @17
    cfn
    wcel
    #
    fprod2d.2
    fprod2d.6
    cA
    @17
    ssfi
    syl2anc
    #
    wph
    @8
    @17
    wcel
    #
    @8
    cA
    wcel
    #
    @2
    cc
    wcel
    wph
    @17
    cA
    @8
    fprod2d.6
    sselda
    #
    wph
    @85
    wa
    cB
    cC
    vk
    fprod2d.3
    wph
    @85
    @30
    @43
    fprod2d.4
    anassrs
    fprodcl
    syldan
    fprodsplit
    adantr
    wph
    @20
    @16
    wceq
    wps
    wph
    @11
    @14
    cD
    @19
    vz
    wph
    @11
    @14
    cin
    #
    c0
    wss
    @87
    c0
    wceq
    wph
    vz
    @87
    c0
    @55
    @87
    wcel
    #
    @55
    c1st
    cfv
    #
    @80
    wcel
    #
    wph
    @55
    c0
    wcel
    #
    @55
    @11
    wcel
    #
    @59
    wa
    @89
    @1
    wcel
    #
    @89
    @5
    wcel
    #
    wa
    @88
    @90
    @92
    @93
    @59
    @94
    @92
    @55
    @10
    wcel
    #
    vj
    @1
    wrex
    @93
    vj
    @55
    @1
    @10
    eliun
    @95
    @93
    vj
    @1
    @95
    @93
    vj
    vx
    wel
    @95
    @89
    @8
    @1
    @95
    @89
    @9
    wcel
    @89
    @8
    wceq
    @55
    @9
    cB
    xp1st
    @89
    @8
    elsni
    syl
    eleq1d
    biimparc
    rexlimiva
    sylbi
    @55
    @5
    @13
    xp1st
    anim12i
    @55
    @11
    @14
    elin
    @89
    @1
    @5
    elin
    3imtr4i
    wph
    @90
    @89
    c0
    wcel
    #
    @91
    wph
    @80
    c0
    @89
    @81
    eleq2d
    @96
    @91
    @89
    noel
    pm2.21i
    syl6bi
    syl5
    ssrdv
    @87
    ss0
    syl
    @19
    @11
    @14
    cun
    #
    wceq
    wph
    @19
    @11
    vj
    @5
    @10
    ciun
    #
    cun
    @97
    vj
    @1
    @5
    @10
    iunxun
    @98
    @14
    @11
    @98
    vm
    @5
    @21
    csn
    #
    @22
    cxp
    #
    ciun
    @14
    vj
    vm
    @5
    @10
    @100
    vm
    @10
    nfcv
    vj
    @99
    @22
    vj
    @99
    nfcv
    @26
    nfxp
    @27
    @9
    @99
    cB
    @22
    @8
    @21
    sneq
    @28
    xpeq12d
    cbviun
    vm
    @4
    @100
    @14
    @34
    @49
    @99
    @5
    @22
    @13
    @21
    @4
    sneq
    @50
    xpeq12d
    iunxsn
    eqtri
    uneq2i
    eqtri
    a1i
    wph
    @82
    @10
    cfn
    wcel
    #
    vj
    @17
    wral
    @19
    cfn
    wcel
    @83
    wph
    @101
    vj
    @17
    wph
    @84
    wa
    #
    @9
    cfn
    wcel
    @36
    @101
    @8
    snfi
    wph
    @84
    @85
    @36
    @86
    fprod2d.3
    syldan
    @9
    cB
    xpfi
    sylancr
    ralrimiva
    vj
    @17
    @10
    iunfi
    syl2anc
    wph
    @55
    @19
    wcel
    #
    cD
    cc
    wcel
    #
    @103
    @95
    vj
    @17
    wrex
    wph
    @104
    vj
    @55
    @17
    @10
    eliun
    wph
    @95
    @104
    vj
    @17
    @95
    @69
    @21
    @9
    wcel
    #
    @30
    wa
    #
    wa
    #
    vk
    wex
    vm
    wex
    @102
    @104
    vm
    vk
    @55
    @9
    cB
    elxp
    @102
    @107
    @104
    vm
    vk
    @102
    @107
    @104
    @102
    @107
    wa
    #
    cD
    cC
    cc
    @108
    @63
    @78
    @108
    @55
    @68
    @62
    @102
    @69
    @106
    simprl
    @108
    @21
    @8
    @29
    @108
    @105
    @75
    @102
    @69
    @105
    @30
    simprrl
    @21
    @8
    elsni
    syl
    opeq1d
    eqtrd
    fprod2d.1
    syl
    @108
    wph
    @85
    @30
    @43
    wph
    @84
    @107
    simpll
    @102
    @85
    @107
    @86
    adantr
    @102
    @69
    @105
    @30
    simprrr
    fprod2d.4
    syl12anc
    eqeltrd
    ex
    exlimdvv
    syl5bi
    rexlimdva
    syl5bi
    imp
    fprodsplit
    adantr
    3eqtr4d
end
