include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "csu.mm"
include "csb.mm"
include "cdiv.mm"
include "co.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfsum.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "wcel.mm"
include "csbeq1a.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "cbvsumi.mm"
include "cmpt.mm"
include "csbeq1.mm"
include "c1.mm"
include "cfz.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "syl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "wf1o.mm"
include "eqid.mm"
include "dvdsflip.mm"
include "cfv.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "adantl.mm"
include "wa.mm"
include "ssrab2.mm"
include "simpr.mm"
include "sseldi.mm"
include "cc.mm"
include "wral.mm"
include "ralrimivva.mm"
include "nfv.mm"
include "nfel1.mm"
include "nfral.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "fsumcl.mm"
include "fsumf1o.mm"
include "dvdsdivcl.mm"
include "sylan.mm"
include "rspcv.mm"
include "sylc.mm"
include "anasss.mm"
include "fsumdvdsdiag.mm"
include "csbeq1d.mm"
include "fsumdvdsdiaglem.mm"
include "ex.mm"
include "syld.mm"
include "impl.mm"
include "cvv.mm"
include "ovexd.mm"
include "cmul.mm"
include "cc0.mm"
include "wne.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "ad2antrr.mm"
include "simpld.mm"
include "elrabi.mm"
include "divdiv1.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "nnmulcl.mm"
include "syl2an.mm"
include "ddcan.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "biimpa.mm"
include "csbied.mm"
include "sumeq2dv.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem fsumdvdscom
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cN: class N
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  assume fsumdvdscom.1: |- ( ph -> N e. NN )
  assume fsumdvdscom.2: |- ( j = ( k x. m ) -> A = B )
  assume fsumdvdscom.3: |- ( ( ph /\ ( j e. { x e. NN | x || N } /\ k e. { x e. NN | x || j } ) ) -> A e. CC )

  disjoint A m
  disjoint B j
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint N j
  disjoint k m
  disjoint k x
  disjoint N k
  disjoint m x
  disjoint N m
  disjoint N x
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint m u
  disjoint m v
  disjoint m z
  disjoint u v
  disjoint u z
  disjoint A u
  disjoint v z
  disjoint A v
  disjoint A z
  disjoint j u
  disjoint j v
  disjoint j z
  disjoint k u
  disjoint k v
  disjoint k z
  disjoint u x
  disjoint N u
  disjoint v x
  disjoint N v
  disjoint x z
  disjoint N z
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> sum_ j e. { x e. NN | x || N } sum_ k e. { x e. NN | x || j } A = sum_ k e. { x e. NN | x || N } sum_ m e. { x e. NN | x || ( N / k ) } B )

  proof
    wph
    vx
    cv
    #
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @0
    vj
    cv
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    cA
    vk
    csu
    #
    vj
    csu
    @2
    @0
    vu
    cv
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vj
    @7
    cA
    csb
    #
    vk
    csu
    #
    vu
    csu
    #
    @2
    @0
    cN
    vk
    cv
    #
    cdiv
    co
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    cB
    vm
    csu
    #
    vk
    csu
    #
    @2
    @6
    @11
    vj
    vu
    vu
    @6
    nfcv
    vj
    @9
    @10
    vk
    vj
    @9
    nfcv
    #
    vj
    @7
    cA
    nfcsb1v
    #
    nfsum
    @3
    @7
    wceq
    #
    @5
    @9
    cA
    @10
    vk
    @21
    @4
    @8
    vx
    cn
    @3
    @7
    @0
    cdvds
    breq2
    rabbidv
    #
    @21
    cA
    @10
    wceq
    @13
    @5
    wcel
    vj
    @7
    cA
    csbeq1a
    #
    adantr
    sumeq12dv
    cbvsumi
    wph
    @12
    @2
    @0
    cN
    vv
    cv
    #
    cdiv
    co
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vj
    @25
    cA
    csb
    #
    vk
    csu
    #
    vv
    csu
    @2
    @16
    @28
    vv
    csu
    #
    vk
    csu
    @18
    wph
    @2
    @11
    @2
    @29
    vu
    vv
    vz
    @2
    cN
    vz
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    @25
    @7
    @25
    wceq
    #
    @9
    @27
    @10
    @28
    vk
    @34
    @8
    @26
    vx
    cn
    @7
    @25
    @0
    cdvds
    breq2
    rabbidv
    #
    @34
    @10
    @28
    wceq
    @13
    @9
    wcel
    vj
    @7
    @25
    cA
    csbeq1
    #
    adantr
    sumeq12dv
    wph
    c1
    cN
    cfz
    co
    #
    cfn
    wcel
    @2
    @37
    wss
    #
    @2
    cfn
    wcel
    wph
    c1
    cN
    fzfid
    wph
    cN
    cn
    wcel
    #
    @38
    fsumdvdscom.1
    cN
    vx
    dvdsssfz1
    syl
    @37
    @2
    ssfi
    syl2anc
    wph
    @39
    @2
    @2
    @33
    wf1o
    fsumdvdscom.1
    vx
    vz
    @2
    @33
    cN
    @2
    eqid
    @33
    eqid
    #
    dvdsflip
    syl
    @24
    @2
    wcel
    #
    @24
    @33
    cfv
    @25
    wceq
    wph
    vz
    @24
    @32
    @25
    @2
    @33
    @31
    @24
    cN
    cdiv
    oveq2
    @40
    cN
    @31
    cdiv
    ovex
    fvmpt3i
    adantl
    wph
    @7
    @2
    wcel
    #
    wa
    #
    @9
    @10
    vk
    @43
    c1
    @7
    cfz
    co
    #
    cfn
    wcel
    @9
    @44
    wss
    #
    @9
    cfn
    wcel
    @43
    c1
    @7
    fzfid
    @43
    @7
    cn
    wcel
    @45
    @43
    @2
    cn
    @7
    @1
    vx
    cn
    ssrab2
    #
    wph
    @42
    simpr
    sseldi
    @7
    vx
    dvdsssfz1
    syl
    @44
    @9
    ssfi
    syl2anc
    @43
    @10
    cc
    wcel
    #
    vk
    @9
    wph
    @47
    vk
    @9
    wral
    #
    vu
    @2
    wph
    cA
    cc
    wcel
    #
    vk
    @5
    wral
    #
    vj
    @2
    wral
    @48
    vu
    @2
    wral
    #
    wph
    @49
    vj
    vk
    @2
    @5
    fsumdvdscom.3
    ralrimivva
    @50
    @48
    vj
    vu
    @2
    @50
    vu
    nfv
    @47
    vj
    vk
    @9
    @19
    vj
    @10
    cc
    @20
    nfel1
    nfral
    @21
    @49
    @47
    vk
    @5
    @9
    @22
    @21
    cA
    @10
    cc
    @23
    eleq1d
    raleqbidv
    cbvral
    sylib
    #
    r19.21bi
    r19.21bi
    fsumcl
    fsumf1o
    wph
    vx
    @28
    vv
    vk
    cN
    fsumdvdscom.1
    wph
    @41
    @13
    @27
    wcel
    #
    @28
    cc
    wcel
    #
    wph
    @41
    wa
    #
    @54
    vk
    @27
    @55
    @25
    @2
    wcel
    #
    @51
    @54
    vk
    @27
    wral
    #
    wph
    @39
    @41
    @56
    fsumdvdscom.1
    vx
    @24
    cN
    dvdsdivcl
    sylan
    wph
    @51
    @41
    @52
    adantr
    @48
    @57
    vu
    @25
    @2
    @34
    @47
    @54
    vk
    @9
    @27
    @35
    @34
    @10
    @28
    cc
    @36
    eleq1d
    raleqbidv
    rspcv
    sylc
    r19.21bi
    anasss
    #
    fsumdvdsdiag
    wph
    @2
    @30
    @17
    vk
    wph
    @13
    @2
    wcel
    #
    wa
    #
    @30
    @16
    vj
    cN
    @14
    vm
    cv
    #
    cdiv
    co
    #
    cdiv
    co
    #
    cA
    csb
    #
    vm
    csu
    @17
    @60
    @16
    @28
    @16
    @64
    vv
    vm
    vz
    @16
    @14
    @31
    cdiv
    co
    #
    cmpt
    #
    @62
    @24
    @62
    wceq
    vj
    @25
    @63
    cA
    @24
    @62
    cN
    cdiv
    oveq2
    csbeq1d
    @60
    c1
    @14
    cfz
    co
    #
    cfn
    wcel
    @16
    @67
    wss
    #
    @16
    cfn
    wcel
    @60
    c1
    @14
    fzfid
    @60
    @14
    cn
    wcel
    #
    @68
    wph
    @39
    @59
    @69
    fsumdvdscom.1
    @39
    @59
    wa
    @2
    cn
    @14
    @46
    vx
    @13
    cN
    dvdsdivcl
    sseldi
    sylan
    #
    @14
    vx
    dvdsssfz1
    syl
    @67
    @16
    ssfi
    syl2anc
    @60
    @69
    @16
    @16
    @66
    wf1o
    @70
    vx
    vz
    @16
    @66
    @14
    @16
    eqid
    @66
    eqid
    #
    dvdsflip
    syl
    @61
    @16
    wcel
    #
    @61
    @66
    cfv
    @62
    wceq
    @60
    vz
    @61
    @65
    @62
    @16
    @66
    @31
    @61
    @14
    cdiv
    oveq2
    @71
    @14
    @31
    cdiv
    ovex
    fvmpt3i
    adantl
    wph
    @59
    @24
    @16
    wcel
    #
    @54
    wph
    @59
    @73
    wa
    @41
    @53
    wa
    #
    @54
    wph
    vx
    vk
    vv
    cN
    fsumdvdscom.1
    fsumdvdsdiaglem
    wph
    @74
    @54
    @58
    ex
    syld
    impl
    fsumf1o
    @60
    @16
    @64
    cB
    vm
    @60
    @72
    wa
    #
    vj
    @63
    cA
    cB
    cvv
    @75
    cN
    @62
    cdiv
    ovexd
    @75
    @3
    @63
    wceq
    #
    wa
    @3
    @13
    @61
    cmul
    co
    #
    wceq
    #
    cA
    cB
    wceq
    @75
    @76
    @78
    @75
    @63
    @77
    @3
    @75
    @63
    cN
    cN
    @77
    cdiv
    co
    #
    cdiv
    co
    #
    @77
    @75
    @62
    @79
    cN
    cdiv
    @75
    cN
    cc
    wcel
    #
    @13
    cc
    wcel
    #
    @13
    cc0
    wne
    #
    wa
    #
    @61
    cc
    wcel
    #
    @61
    cc0
    wne
    #
    wa
    #
    @62
    @79
    wceq
    @75
    @81
    cN
    cc0
    wne
    #
    wph
    @81
    @88
    wa
    #
    @59
    @72
    wph
    @39
    @89
    fsumdvdscom.1
    @39
    @81
    @88
    cN
    nncn
    cN
    nnne0
    jca
    syl
    ad2antrr
    #
    simpld
    @75
    @13
    cn
    wcel
    #
    @84
    @60
    @91
    @72
    @59
    @91
    wph
    @1
    vx
    @13
    cn
    elrabi
    adantl
    #
    adantr
    @91
    @82
    @83
    @13
    nncn
    @13
    nnne0
    jca
    syl
    @75
    @61
    cn
    wcel
    #
    @87
    @72
    @93
    @60
    @15
    vx
    @61
    cn
    elrabi
    #
    adantl
    @93
    @85
    @86
    @61
    nncn
    @61
    nnne0
    jca
    syl
    cN
    @13
    @61
    divdiv1
    syl3anc
    oveq2d
    @75
    @89
    @77
    cc
    wcel
    #
    @77
    cc0
    wne
    #
    wa
    #
    @80
    @77
    wceq
    @90
    @75
    @77
    cn
    wcel
    #
    @97
    @60
    @91
    @93
    @98
    @72
    @92
    @94
    @13
    @61
    nnmulcl
    syl2an
    @98
    @95
    @96
    @77
    nncn
    @77
    nnne0
    jca
    syl
    cN
    @77
    ddcan
    syl2anc
    eqtrd
    eqeq2d
    biimpa
    fsumdvdscom.2
    syl
    csbied
    sumeq2dv
    eqtrd
    sumeq2dv
    3eqtrd
    syl5eq
end
