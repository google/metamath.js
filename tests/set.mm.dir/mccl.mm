include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cfa.mm"
include "cprod.mm"
include "cdiv.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "wral.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sumeq1.mm"
include "fveq2d.mm"
include "prodeq1.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "bitrd.mm"
include "wa.mm"
include "c1.mm"
include "cc0.mm"
include "sum0.mm"
include "fveq2i.mm"
include "fac0.mm"
include "eqtri.mm"
include "prod0.mm"
include "oveq12i.mm"
include "1div1e1.mm"
include "1nn.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ralrimiva.mm"
include "wss.mm"
include "cdif.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simpll.mm"
include "fveq2.mm"
include "cbvsumv.mm"
include "fveq1.mm"
include "sumeq2ad.mm"
include "eqtrd.mm"
include "cbvprodv.mm"
include "prodeq2ad.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "cfn.mm"
include "ad3antrrr.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "eleq1i.mm"
include "ralbii.mm"
include "mccllem.mm"
include "syl21anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "findcard2d.mm"
include "nfcv.mm"
include "nfeq.mm"
include "a1d.mm"
include "sumeq2d.mm"
include "prodeq2d.mm"
include "rspccva.mm"
include "syl2anc.mm"

theorem mccl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vj: setvar j
  assume mccl.kb: |- F/_ k B
  assume mccl.a: |- ( ph -> A e. Fin )
  assume mccl.b: |- ( ph -> B e. ( NN0 ^m A ) )

  disjoint A k
  disjoint k ph
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a k
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint c d
  disjoint c k
  disjoint d k
  disjoint B b
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint b e
  disjoint b j
  disjoint c e
  disjoint c j
  disjoint e j
  disjoint e k
  disjoint j k
  assert |- ( ph -> ( ( ! ` sum_ k e. A ( B ` k ) ) / prod_ k e. A ( ! ` ( B ` k ) ) ) e. NN )

  proof
    wph
    cA
    vk
    cv
    #
    vb
    cv
    #
    cfv
    #
    vk
    csu
    #
    cfa
    cfv
    #
    cA
    @2
    cfa
    cfv
    #
    vk
    cprod
    #
    cdiv
    co
    #
    cn
    wcel
    #
    vb
    cn0
    cA
    cmap
    co
    #
    wral
    #
    cB
    @9
    wcel
    cA
    @0
    cB
    cfv
    #
    vk
    csu
    #
    cfa
    cfv
    #
    cA
    @11
    cfa
    cfv
    #
    vk
    cprod
    #
    cdiv
    co
    #
    cn
    wcel
    #
    wph
    va
    cv
    #
    @2
    vk
    csu
    #
    cfa
    cfv
    #
    @18
    @5
    vk
    cprod
    #
    cdiv
    co
    #
    cn
    wcel
    #
    vb
    cn0
    @18
    cmap
    co
    #
    wral
    #
    c0
    @2
    vk
    csu
    #
    cfa
    cfv
    #
    c0
    @5
    vk
    cprod
    #
    cdiv
    co
    #
    cn
    wcel
    #
    vb
    cn0
    c0
    cmap
    co
    #
    wral
    #
    vc
    cv
    #
    @2
    vk
    csu
    #
    cfa
    cfv
    #
    @33
    @5
    vk
    cprod
    #
    cdiv
    co
    #
    cn
    wcel
    #
    vb
    cn0
    @33
    cmap
    co
    #
    wral
    #
    @33
    vd
    cv
    #
    csn
    cun
    #
    @2
    vk
    csu
    #
    cfa
    cfv
    #
    @42
    @5
    vk
    cprod
    #
    cdiv
    co
    #
    cn
    wcel
    #
    vb
    cn0
    @42
    cmap
    co
    #
    wral
    #
    @10
    va
    vc
    vd
    cA
    @18
    c0
    wceq
    #
    @25
    @30
    vb
    @24
    wral
    @32
    @50
    @23
    @30
    vb
    @24
    @50
    @22
    @29
    cn
    @50
    @20
    @27
    @21
    @28
    cdiv
    @50
    @19
    @26
    cfa
    @18
    c0
    @2
    vk
    sumeq1
    fveq2d
    @18
    c0
    @5
    vk
    prodeq1
    oveq12d
    eleq1d
    ralbidv
    @50
    @30
    vb
    @24
    @31
    @18
    c0
    cn0
    cmap
    oveq2
    raleqdv
    bitrd
    @18
    @33
    wceq
    #
    @25
    @38
    vb
    @24
    wral
    @40
    @51
    @23
    @38
    vb
    @24
    @51
    @22
    @37
    cn
    @51
    @20
    @35
    @21
    @36
    cdiv
    @51
    @19
    @34
    cfa
    @18
    @33
    @2
    vk
    sumeq1
    fveq2d
    @18
    @33
    @5
    vk
    prodeq1
    oveq12d
    eleq1d
    ralbidv
    @51
    @38
    vb
    @24
    @39
    @18
    @33
    cn0
    cmap
    oveq2
    raleqdv
    bitrd
    @18
    @42
    wceq
    #
    @25
    @47
    vb
    @24
    wral
    @49
    @52
    @23
    @47
    vb
    @24
    @52
    @22
    @46
    cn
    @52
    @20
    @44
    @21
    @45
    cdiv
    @52
    @19
    @43
    cfa
    @18
    @42
    @2
    vk
    sumeq1
    fveq2d
    @18
    @42
    @5
    vk
    prodeq1
    oveq12d
    eleq1d
    ralbidv
    @52
    @47
    vb
    @24
    @48
    @18
    @42
    cn0
    cmap
    oveq2
    raleqdv
    bitrd
    @18
    cA
    wceq
    #
    @25
    @8
    vb
    @24
    wral
    @10
    @53
    @23
    @8
    vb
    @24
    @53
    @22
    @7
    cn
    @53
    @20
    @4
    @21
    @6
    cdiv
    @53
    @19
    @3
    cfa
    @18
    cA
    @2
    vk
    sumeq1
    fveq2d
    @18
    cA
    @5
    vk
    prodeq1
    oveq12d
    eleq1d
    ralbidv
    @53
    @8
    vb
    @24
    @9
    @18
    cA
    cn0
    cmap
    oveq2
    raleqdv
    bitrd
    wph
    @30
    vb
    @31
    @30
    wph
    @1
    @31
    wcel
    wa
    @29
    c1
    cn
    @29
    c1
    c1
    cdiv
    co
    c1
    @27
    c1
    @28
    c1
    cdiv
    @27
    cc0
    cfa
    cfv
    c1
    @26
    cc0
    cfa
    @2
    vk
    sum0
    fveq2i
    fac0
    eqtri
    @5
    vk
    prod0
    oveq12i
    1div1e1
    eqtri
    1nn
    eqeltri
    a1i
    ralrimiva
    wph
    @33
    cA
    wss
    #
    @41
    cA
    @33
    cdif
    wcel
    #
    wa
    #
    wa
    #
    @40
    @49
    @57
    @40
    wa
    #
    @47
    vb
    @48
    @57
    @40
    vb
    @57
    vb
    nfv
    @38
    vb
    @39
    nfra1
    nfan
    @58
    @1
    @48
    wcel
    #
    @47
    @58
    @59
    wa
    @57
    @33
    vj
    cv
    #
    ve
    cv
    #
    cfv
    #
    vj
    csu
    #
    cfa
    cfv
    #
    @33
    @62
    cfa
    cfv
    #
    vj
    cprod
    #
    cdiv
    co
    #
    cn
    wcel
    #
    ve
    @39
    wral
    #
    @59
    @47
    @57
    @40
    @59
    simpll
    @40
    @69
    @57
    @59
    @40
    @69
    @38
    @68
    vb
    ve
    @39
    @1
    @61
    wceq
    #
    @37
    @67
    cn
    @70
    @35
    @64
    @36
    @66
    cdiv
    @70
    @34
    @63
    cfa
    @70
    @34
    @33
    @60
    @1
    cfv
    #
    vj
    csu
    #
    @63
    @34
    @72
    wceq
    @70
    @33
    @2
    @71
    vk
    vj
    @0
    @60
    @1
    fveq2
    #
    cbvsumv
    a1i
    @70
    @33
    @71
    @62
    vj
    @60
    @1
    @61
    fveq1
    #
    sumeq2ad
    eqtrd
    fveq2d
    @70
    @36
    @33
    @71
    cfa
    cfv
    #
    vj
    cprod
    #
    @66
    @36
    @76
    wceq
    @70
    @33
    @5
    @75
    vk
    vj
    @0
    @60
    wceq
    @2
    @71
    cfa
    @73
    fveq2d
    cbvprodv
    a1i
    @70
    @33
    @75
    @65
    vj
    @70
    @71
    @62
    cfa
    @74
    fveq2d
    prodeq2ad
    eqtrd
    oveq12d
    eleq1d
    cbvralv
    biimpi
    ad2antlr
    @58
    @59
    simpr
    @57
    @69
    wa
    #
    @59
    wa
    cA
    @1
    @33
    @41
    vk
    ve
    wph
    cA
    cfn
    wcel
    @56
    @69
    @59
    mccl.a
    ad3antrrr
    @57
    @54
    @69
    @59
    wph
    @54
    @55
    simprl
    ad2antrr
    @57
    @55
    @69
    @59
    wph
    @54
    @55
    simprr
    ad2antrr
    @77
    @59
    simpr
    @69
    @33
    @0
    @61
    cfv
    #
    vk
    csu
    #
    cfa
    cfv
    #
    @33
    @78
    cfa
    cfv
    #
    vk
    cprod
    #
    cdiv
    co
    #
    cn
    wcel
    #
    ve
    @39
    wral
    #
    @57
    @59
    @69
    @85
    @68
    @84
    ve
    @39
    @67
    @83
    cn
    @64
    @80
    @66
    @82
    cdiv
    @63
    @79
    cfa
    @33
    @62
    @78
    vj
    vk
    @60
    @0
    @61
    fveq2
    #
    cbvsumv
    fveq2i
    @33
    @65
    @81
    vj
    vk
    @60
    @0
    wceq
    @62
    @78
    cfa
    @86
    fveq2d
    cbvprodv
    oveq12i
    eleq1i
    ralbii
    biimpi
    ad2antlr
    mccllem
    syl21anc
    ex
    ralrimi
    ex
    mccl.a
    findcard2d
    mccl.b
    @8
    @17
    vb
    cB
    @9
    @1
    cB
    wceq
    #
    @7
    @16
    cn
    @87
    @4
    @13
    @6
    @15
    cdiv
    @87
    @3
    @12
    cfa
    @87
    cA
    @2
    @11
    vk
    @87
    @2
    @11
    wceq
    #
    vk
    cA
    vk
    @1
    cB
    vk
    @1
    nfcv
    mccl.kb
    nfeq
    #
    @87
    @88
    @0
    cA
    wcel
    #
    @0
    @1
    cB
    fveq1
    #
    a1d
    ralrimi
    sumeq2d
    fveq2d
    @87
    cA
    @5
    @14
    vk
    @87
    @5
    @14
    wceq
    #
    vk
    cA
    @89
    @87
    @92
    @90
    @87
    @2
    @11
    cfa
    @91
    fveq2d
    a1d
    ralrimi
    prodeq2d
    oveq12d
    eleq1d
    rspccva
    syl2anc
end
