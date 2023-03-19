include "cfz.mm"
include "co.mm"
include "cv.mm"
include "ce.mm"
include "cfv.mm"
include "cmpt.mm"
include "cprod.mm"
include "csu.mm"
include "cuz.mm"
include "wcel.mm"
include "wceq.mm"
include "syl6eleq.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "prodeq1d.mm"
include "sumeq1d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cz.mm"
include "wa.mm"
include "csb.mm"
include "csn.mm"
include "fzsn.mm"
include "adantl.mm"
include "cc.mm"
include "simpr.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "efcl.mm"
include "syl.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "sylan2.mm"
include "fveq2.mm"
include "prodsn.mm"
include "syl2anc.mm"
include "cvv.mm"
include "fvex.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nffv.mm"
include "csbeq1a.mm"
include "fvmptf.mm"
include "sylancl.mm"
include "3eqtrd.mm"
include "sumsn.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "impcom.mm"
include "syl2an.mm"
include "fvmpts.mm"
include "eqtr4d.mm"
include "expcom.mm"
include "w3a.mm"
include "cmul.mm"
include "simp3.mm"
include "peano2uzs.mm"
include "mpan9.mm"
include "3adant3.mm"
include "oveq12d.mm"
include "elfzuz.mm"
include "adantlr.mm"
include "fprodp1.mm"
include "fsump1.mm"
include "fzfid.mm"
include "fsumcl.mm"
include "efadd.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "3exp.mm"
include "com12.mm"
include "a2d.mm"
include "eqcomi.mm"
include "eleq2s.mm"
include "uzind4.mm"
include "mpcom.mm"
include "cres.mm"
include "wss.mm"
include "fzssuz.mm"
include "sseqtr4i.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5reqr.mm"
include "prodeq2i.mm"
include "prodfc.mm"
include "eqtri.mm"
include "sumeq2i.mm"
include "sumfc.mm"
include "fveq2i.mm"
include "3eqtr3g.mm"

theorem fprodefsum
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cZ: class Z
  let va: setvar a
  let vm: setvar m
  let vn: setvar n
  assume fprodefsum.1: |- Z = ( ZZ>= ` M )
  assume fprodefsum.2: |- ( ph -> N e. Z )
  assume fprodefsum.3: |- ( ( ph /\ k e. Z ) -> A e. CC )

  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint Z k
  disjoint A a
  disjoint a k
  disjoint a m
  disjoint A m
  disjoint a n
  disjoint A n
  disjoint a ph
  disjoint k m
  disjoint k n
  disjoint M a
  disjoint M m
  disjoint m n
  disjoint M n
  disjoint m ph
  disjoint N a
  disjoint N m
  disjoint n ph
  disjoint Z a
  disjoint Z m
  disjoint Z n
  assert |- ( ph -> prod_ k e. ( M ... N ) ( exp ` A ) = ( exp ` sum_ k e. ( M ... N ) A ) )

  proof
    wph
    cM
    cN
    cfz
    co
    #
    vm
    cv
    #
    vk
    cZ
    cA
    ce
    cfv
    #
    cmpt
    #
    cfv
    #
    vm
    cprod
    #
    @0
    @1
    vk
    cZ
    cA
    cmpt
    #
    cfv
    #
    vm
    csu
    #
    ce
    cfv
    #
    @0
    @2
    vk
    cprod
    #
    @0
    cA
    vk
    csu
    #
    ce
    cfv
    cN
    cM
    cuz
    cfv
    #
    wcel
    wph
    @5
    @9
    wceq
    #
    wph
    cN
    cZ
    @12
    fprodefsum.2
    fprodefsum.1
    syl6eleq
    wph
    cM
    va
    cv
    #
    cfz
    co
    #
    @4
    vm
    cprod
    #
    @15
    @7
    vm
    csu
    #
    ce
    cfv
    #
    wceq
    #
    wi
    wph
    cM
    cM
    cfz
    co
    #
    @4
    vm
    cprod
    #
    @20
    @7
    vm
    csu
    #
    ce
    cfv
    #
    wceq
    #
    wi
    wph
    cM
    vn
    cv
    #
    cfz
    co
    #
    @4
    vm
    cprod
    #
    @26
    @7
    vm
    csu
    #
    ce
    cfv
    #
    wceq
    #
    wi
    #
    wph
    cM
    @25
    c1
    caddc
    co
    #
    cfz
    co
    #
    @4
    vm
    cprod
    #
    @33
    @7
    vm
    csu
    #
    ce
    cfv
    #
    wceq
    #
    wi
    #
    wph
    @13
    wi
    va
    vn
    cM
    cN
    @14
    cM
    wceq
    #
    @19
    @24
    wph
    @39
    @16
    @21
    @18
    @23
    @39
    @15
    @20
    @4
    vm
    @14
    cM
    cM
    cfz
    oveq2
    #
    prodeq1d
    @39
    @17
    @22
    ce
    @39
    @15
    @20
    @7
    vm
    @40
    sumeq1d
    fveq2d
    eqeq12d
    imbi2d
    va
    vn
    weq
    #
    @19
    @30
    wph
    @41
    @16
    @27
    @18
    @29
    @41
    @15
    @26
    @4
    vm
    @14
    @25
    cM
    cfz
    oveq2
    #
    prodeq1d
    @41
    @17
    @28
    ce
    @41
    @15
    @26
    @7
    vm
    @42
    sumeq1d
    fveq2d
    eqeq12d
    imbi2d
    @14
    @32
    wceq
    #
    @19
    @37
    wph
    @43
    @16
    @34
    @18
    @36
    @43
    @15
    @33
    @4
    vm
    @14
    @32
    cM
    cfz
    oveq2
    #
    prodeq1d
    @43
    @17
    @35
    ce
    @43
    @15
    @33
    @7
    vm
    @44
    sumeq1d
    fveq2d
    eqeq12d
    imbi2d
    @14
    cN
    wceq
    #
    @19
    @13
    wph
    @45
    @16
    @5
    @18
    @9
    @45
    @15
    @0
    @4
    vm
    @14
    cN
    cM
    cfz
    oveq2
    #
    prodeq1d
    @45
    @17
    @8
    ce
    @45
    @15
    @0
    @7
    vm
    @46
    sumeq1d
    fveq2d
    eqeq12d
    imbi2d
    wph
    cM
    cz
    wcel
    #
    @24
    wph
    @47
    wa
    #
    @21
    vk
    cM
    cA
    csb
    #
    ce
    cfv
    #
    @23
    @48
    @21
    cM
    csn
    #
    @4
    vm
    cprod
    #
    cM
    @3
    cfv
    #
    @50
    @48
    @20
    @51
    @4
    vm
    @47
    @20
    @51
    wceq
    wph
    cM
    fzsn
    adantl
    #
    prodeq1d
    @48
    @47
    @53
    cc
    wcel
    #
    @52
    @53
    wceq
    wph
    @47
    simpr
    #
    @47
    wph
    cM
    cZ
    wcel
    #
    @55
    @47
    cM
    @12
    cZ
    cM
    uzid
    fprodefsum.1
    syl6eleqr
    #
    wph
    cZ
    cc
    cM
    @3
    wph
    vk
    cZ
    @2
    cc
    @3
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    cA
    cc
    wcel
    #
    @2
    cc
    wcel
    fprodefsum.3
    cA
    efcl
    syl
    @3
    eqid
    #
    fmptd
    #
    ffvelrnda
    sylan2
    @4
    @53
    vm
    cM
    cz
    @1
    cM
    @3
    fveq2
    prodsn
    syl2anc
    @48
    @57
    @50
    cvv
    wcel
    @53
    @50
    wceq
    @47
    @57
    wph
    @58
    adantl
    #
    @49
    ce
    fvex
    vk
    cM
    @2
    @50
    cZ
    @3
    cvv
    vk
    cM
    nfcv
    vk
    @49
    ce
    vk
    ce
    nfcv
    #
    vk
    cM
    cA
    nfcsb1v
    #
    nffv
    @59
    cM
    wceq
    #
    cA
    @49
    ce
    vk
    cM
    cA
    csbeq1a
    #
    fveq2d
    @61
    fvmptf
    sylancl
    3eqtrd
    @48
    @22
    @49
    ce
    @48
    @22
    @51
    @7
    vm
    csu
    #
    cM
    @6
    cfv
    #
    @49
    @48
    @20
    @51
    @7
    vm
    @54
    sumeq1d
    @48
    @47
    @69
    cc
    wcel
    #
    @68
    @69
    wceq
    @56
    @47
    wph
    @57
    @70
    @58
    wph
    cZ
    cc
    cM
    @6
    wph
    vk
    cZ
    cA
    cc
    @6
    fprodefsum.3
    @6
    eqid
    #
    fmptd
    #
    ffvelrnda
    sylan2
    @7
    @69
    vm
    cM
    cz
    @1
    cM
    @6
    fveq2
    sumsn
    syl2anc
    @48
    @57
    @49
    cc
    wcel
    #
    @69
    @49
    wceq
    @63
    wph
    @60
    vk
    cZ
    wral
    #
    @57
    @73
    @47
    wph
    @60
    vk
    cZ
    fprodefsum.3
    ralrimiva
    #
    @58
    @57
    @74
    @73
    @60
    @73
    vk
    cM
    cZ
    vk
    @49
    cc
    @65
    nfel1
    @66
    cA
    @49
    cc
    @67
    eleq1d
    rspc
    impcom
    syl2an
    vk
    cM
    cA
    cZ
    @6
    cc
    @71
    fvmpts
    syl2anc
    3eqtrd
    fveq2d
    eqtr4d
    expcom
    @31
    @38
    wi
    @25
    cZ
    @12
    @25
    cZ
    wcel
    #
    wph
    @30
    @37
    wph
    @76
    @30
    @37
    wi
    wph
    @76
    @30
    @37
    wph
    @76
    @30
    w3a
    #
    @27
    @32
    @3
    cfv
    #
    cmul
    co
    #
    @29
    @32
    @6
    cfv
    #
    ce
    cfv
    #
    cmul
    co
    #
    @34
    @36
    @77
    @27
    @29
    @78
    @81
    cmul
    wph
    @76
    @30
    simp3
    wph
    @76
    @78
    @81
    wceq
    #
    @30
    @76
    wph
    @32
    cZ
    wcel
    #
    @83
    cM
    @25
    cZ
    fprodefsum.1
    peano2uzs
    #
    wph
    @84
    wa
    #
    @78
    vk
    @32
    cA
    csb
    #
    ce
    cfv
    #
    @81
    @86
    @84
    @88
    cc
    wcel
    #
    @78
    @88
    wceq
    wph
    @84
    simpr
    #
    @86
    @87
    cc
    wcel
    #
    @89
    wph
    @74
    @84
    @91
    @75
    @60
    @91
    vk
    @32
    cZ
    vk
    @87
    cc
    vk
    @32
    cA
    nfcsb1v
    #
    nfel1
    @59
    @32
    wceq
    #
    cA
    @87
    cc
    vk
    @32
    cA
    csbeq1a
    #
    eleq1d
    rspc
    mpan9
    #
    @87
    efcl
    syl
    vk
    @32
    @2
    @88
    cZ
    @3
    cc
    vk
    @32
    nfcv
    vk
    @87
    ce
    @64
    @92
    nffv
    @93
    cA
    @87
    ce
    @94
    fveq2d
    @61
    fvmptf
    syl2anc
    @86
    @80
    @87
    ce
    @86
    @84
    @91
    @80
    @87
    wceq
    @90
    @95
    vk
    @32
    cA
    cZ
    @6
    cc
    @71
    fvmpts
    syl2anc
    fveq2d
    eqtr4d
    sylan2
    3adant3
    oveq12d
    wph
    @76
    @34
    @79
    wceq
    @30
    wph
    @76
    wa
    #
    @4
    @78
    vm
    cM
    @25
    @96
    @25
    cZ
    @12
    wph
    @76
    simpr
    fprodefsum.1
    syl6eleq
    #
    wph
    @1
    @33
    wcel
    #
    @4
    cc
    wcel
    #
    @76
    @98
    wph
    @1
    cZ
    wcel
    #
    @99
    @98
    @1
    @12
    cZ
    @1
    cM
    @32
    elfzuz
    fprodefsum.1
    syl6eleqr
    #
    wph
    cZ
    cc
    @1
    @3
    @62
    ffvelrnda
    sylan2
    adantlr
    @1
    @32
    @3
    fveq2
    fprodp1
    3adant3
    wph
    @76
    @36
    @82
    wceq
    @30
    @96
    @36
    @28
    @80
    caddc
    co
    #
    ce
    cfv
    #
    @82
    @96
    @35
    @102
    ce
    @96
    @7
    @80
    vm
    cM
    @25
    @97
    wph
    @98
    @7
    cc
    wcel
    #
    @76
    @98
    wph
    @100
    @104
    @101
    wph
    cZ
    cc
    @1
    @6
    @72
    ffvelrnda
    #
    sylan2
    adantlr
    @1
    @32
    @6
    fveq2
    fsump1
    fveq2d
    @96
    @28
    cc
    wcel
    @80
    cc
    wcel
    #
    @103
    @82
    wceq
    @96
    @26
    @7
    vm
    @96
    cM
    @25
    fzfid
    wph
    @1
    @26
    wcel
    #
    @104
    @76
    @107
    wph
    @100
    @104
    @107
    @1
    @12
    cZ
    @1
    cM
    @25
    elfzuz
    fprodefsum.1
    syl6eleqr
    @105
    sylan2
    adantlr
    fsumcl
    @76
    wph
    @84
    @106
    @85
    wph
    cZ
    cc
    @32
    @6
    @72
    ffvelrnda
    sylan2
    @28
    @80
    efadd
    syl2anc
    eqtrd
    3adant3
    3eqtr4d
    3exp
    com12
    a2d
    cZ
    @12
    fprodefsum.1
    eqcomi
    eleq2s
    uzind4
    mpcom
    @5
    @0
    @1
    vk
    @0
    @2
    cmpt
    #
    cfv
    #
    vm
    cprod
    @10
    @0
    @4
    @109
    vm
    @1
    @0
    wcel
    #
    @109
    @1
    @3
    @0
    cres
    #
    cfv
    @4
    @1
    @111
    @108
    @0
    cZ
    wss
    #
    @111
    @108
    wceq
    @0
    @12
    cZ
    cM
    cN
    fzssuz
    fprodefsum.1
    sseqtr4i
    #
    vk
    cZ
    @0
    @2
    resmpt
    ax-mp
    fveq1i
    @1
    @0
    @3
    fvres
    syl5reqr
    prodeq2i
    @0
    @2
    vm
    vk
    prodfc
    eqtri
    @8
    @11
    ce
    @8
    @0
    @1
    vk
    @0
    cA
    cmpt
    #
    cfv
    #
    vm
    csu
    @11
    @0
    @7
    @115
    vm
    @110
    @115
    @1
    @6
    @0
    cres
    #
    cfv
    @7
    @1
    @116
    @114
    @112
    @116
    @114
    wceq
    @113
    vk
    cZ
    @0
    cA
    resmpt
    ax-mp
    fveq1i
    @1
    @0
    @6
    fvres
    syl5reqr
    sumeq2i
    @0
    cA
    vm
    vk
    sumfc
    eqtri
    fveq2i
    3eqtr3g
end
