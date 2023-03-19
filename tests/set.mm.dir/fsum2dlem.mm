include "wa.mm"
include "cv.mm"
include "csu.mm"
include "csn.mm"
include "caddc.mm"
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
include "nfsum.mm"
include "weq.mm"
include "csbeq1a.mm"
include "wcel.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "cbvsumi.mm"
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
include "fsumcl.mm"
include "csbeq1.mm"
include "sumsn.mm"
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
include "fsumf1o.mm"
include "cop.mm"
include "wex.mm"
include "elxp.mm"
include "nfv.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfex.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "eqtr2.mm"
include "eleq2d.mm"
include "pm5.32da.mm"
include "velsn.mm"
include "anbi1i.mm"
include "syl6rbbr.mm"
include "equequ1.mm"
include "anbi1d.mm"
include "bitrd.mm"
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
include "sumeq2dv.mm"
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
include "fsumsplit.mm"
include "c1st.mm"
include "wrex.mm"
include "eliun.mm"
include "xp1st.mm"
include "elsni.mm"
include "simpl.mm"
include "eqeltrd.mm"
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
include "ex.mm"
include "exlimdvv.mm"
include "rexlimdva.mm"
include "3eqtr4d.mm"

theorem fsum2dlem
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
  let vw: setvar w
  assume fsum2d.1: |- ( z = <. j , k >. -> D = C )
  assume fsum2d.2: |- ( ph -> A e. Fin )
  assume fsum2d.3: |- ( ( ph /\ j e. A ) -> B e. Fin )
  assume fsum2d.4: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. CC )
  assume fsum2d.5: |- ( ph -> -. y e. x )
  assume fsum2d.6: |- ( ph -> ( x u. { y } ) C_ A )
  assume fsum2d.7: |- ( ps <-> sum_ j e. x sum_ k e. B C = sum_ z e. U_ j e. x ( { j } X. B ) D )

  disjoint j k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D j
  disjoint D k
  disjoint D x
  disjoint D y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint j m
  disjoint j w
  disjoint k m
  disjoint k w
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B m
  disjoint B w
  disjoint D m
  disjoint D w
  disjoint C m
  disjoint C w
  disjoint m ph
  disjoint ph w
  assert |- ( ( ph /\ ps ) -> sum_ j e. ( x u. { y } ) sum_ k e. B C = sum_ z e. U_ j e. ( x u. { y } ) ( { j } X. B ) D )

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
    csu
    #
    vj
    csu
    #
    vy
    cv
    #
    csn
    #
    @2
    vj
    csu
    #
    caddc
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
    csu
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
    csu
    #
    caddc
    co
    #
    @1
    @5
    cun
    #
    @2
    vj
    csu
    #
    vj
    @17
    @10
    ciun
    #
    cD
    vz
    csu
    #
    @0
    @3
    @12
    @6
    @15
    caddc
    @0
    wps
    @3
    @12
    wceq
    wph
    wps
    simpr
    fsum2d.7
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
    csu
    #
    vm
    csu
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
    nfsum
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
    sumeq12dv
    cbvsumi
    wph
    @25
    @13
    vj
    @4
    cC
    csb
    #
    vk
    csu
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
    fsum2d.6
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
    fsum2d.3
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
    fsum2d.4
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
    fsumcl
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
    sumeq12dv
    sumsn
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
    csu
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
    cbvsumi
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
    csu
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
    fsumf1o
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
    @49
    @30
    wa
    #
    @64
    @75
    @76
    @49
    @71
    wa
    @72
    @75
    @49
    @30
    @71
    @75
    @49
    wa
    #
    cB
    @13
    @29
    @77
    @39
    cB
    @13
    wceq
    @21
    @8
    @4
    eqtr2
    @40
    syl
    eleq2d
    pm5.32da
    @70
    @49
    @71
    vm
    @4
    velsn
    anbi1i
    syl6rbbr
    @75
    @49
    @39
    @30
    vm
    vj
    vy
    equequ1
    anbi1d
    bitrd
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
    fsum2d.1
    ad2antlr
    @39
    cC
    @31
    wceq
    @78
    @30
    @47
    ad2antrl
    @79
    @29
    @56
    wceq
    #
    @31
    @57
    wceq
    @63
    @81
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
    sumeq2dv
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
    fsum2d.5
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
    fsum2d.2
    fsum2d.6
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
    fsum2d.6
    sselda
    #
    wph
    @87
    wa
    cB
    cC
    vk
    fsum2d.3
    wph
    @87
    @30
    @43
    fsum2d.4
    anassrs
    fsumcl
    syldan
    fsumsplit
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
    @89
    c0
    wceq
    wph
    vz
    @89
    c0
    @55
    @89
    wcel
    #
    @55
    c1st
    cfv
    #
    @82
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
    @91
    @1
    wcel
    #
    @91
    @5
    wcel
    #
    wa
    @90
    @92
    @94
    @95
    @59
    @96
    @94
    @55
    @10
    wcel
    #
    vj
    @1
    wrex
    @95
    vj
    @55
    @1
    @10
    eliun
    @97
    @95
    vj
    @1
    vj
    vx
    wel
    #
    @97
    wa
    @91
    @8
    @1
    @97
    @91
    @8
    wceq
    #
    @98
    @97
    @91
    @9
    wcel
    @99
    @55
    @9
    cB
    xp1st
    @91
    @8
    elsni
    syl
    adantl
    @98
    @97
    simpl
    eqeltrd
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
    @91
    @1
    @5
    elin
    3imtr4i
    wph
    @92
    @91
    c0
    wcel
    #
    @93
    wph
    @82
    c0
    @91
    @83
    eleq2d
    @100
    @93
    @91
    noel
    pm2.21i
    syl6bi
    syl5
    ssrdv
    @89
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
    @101
    vj
    @1
    @5
    @10
    iunxun
    @102
    @14
    @11
    @102
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
    @104
    vm
    @10
    nfcv
    vj
    @103
    @22
    vj
    @103
    nfcv
    @26
    nfxp
    @27
    @9
    @103
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
    @104
    @14
    @34
    @49
    @103
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
    @84
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
    @85
    wph
    @105
    vj
    @17
    wph
    @86
    wa
    #
    @9
    cfn
    wcel
    @36
    @105
    @8
    snfi
    wph
    @86
    @87
    @36
    @88
    fsum2d.3
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
    @107
    @97
    vj
    @17
    wrex
    wph
    @108
    vj
    @55
    @17
    @10
    eliun
    wph
    @97
    @108
    vj
    @17
    @97
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
    @106
    @108
    vm
    vk
    @55
    @9
    cB
    elxp
    @106
    @111
    @108
    vm
    vk
    @106
    @111
    @108
    @106
    @111
    wa
    #
    cD
    cC
    cc
    @112
    @63
    @80
    @112
    @55
    @68
    @62
    @106
    @69
    @110
    simprl
    @112
    @21
    @8
    @29
    @112
    @109
    @75
    @106
    @69
    @109
    @30
    simprrl
    @21
    @8
    elsni
    syl
    opeq1d
    eqtrd
    fsum2d.1
    syl
    @112
    wph
    @87
    @30
    @43
    wph
    @86
    @111
    simpll
    @106
    @87
    @111
    @88
    adantr
    @106
    @69
    @109
    @30
    simprrr
    fsum2d.4
    syl12anc
    eqeltrd
    ex
    exlimdvv
    syl5bi
    rexlimdva
    syl5bi
    imp
    fsumsplit
    adantr
    3eqtr4d
end
