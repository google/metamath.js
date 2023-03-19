include "cfn.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "wa.mm"
include "wral.mm"
include "ciun.mm"
include "csu.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "raleq.mm"
include "iuneq1.mm"
include "fveq2d.mm"
include "sumeq1.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "cc0.mm"
include "0le0.mm"
include "0iun.mm"
include "fveq2i.mm"
include "ovol0.mm"
include "eqtri.mm"
include "sum0.mm"
include "3brtr4i.mm"
include "a1i.mm"
include "wn.mm"
include "ssun1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "imim1i.mm"
include "csb.mm"
include "caddc.mm"
include "co.mm"
include "simprl.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfss.mm"
include "nffv.mm"
include "nfel1.mm"
include "nfan.mm"
include "csbeq1a.mm"
include "sseq1d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspc.mm"
include "mpan9.mm"
include "simpld.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "iunss1.mm"
include "syl5ss.mm"
include "simpll.mm"
include "elun1.mm"
include "simprd.mm"
include "sylan2.mm"
include "fsumrecl.mm"
include "simprr.mm"
include "cbviun.mm"
include "cbvsumi.mm"
include "3brtr3g.mm"
include "ovollecl.mm"
include "syl3anc.mm"
include "ssun2.mm"
include "vsnid.mm"
include "sselii.mm"
include "mpsyl.mm"
include "readdcld.mm"
include "iunxun.mm"
include "vex.mm"
include "csbeq1.mm"
include "iunxsn.mm"
include "uneq2i.mm"
include "ovolun.mm"
include "syl21anc.mm"
include "syl5eqbr.mm"
include "snfi.mm"
include "unfi.mm"
include "mpan2.mm"
include "ad2antrr.mm"
include "leadd1dd.mm"
include "cin.mm"
include "simplr.mm"
include "disjsn.mm"
include "eqidd.mm"
include "recnd.mm"
include "fsumsplit.mm"
include "cvv.mm"
include "cc.mm"
include "sumsn.mm"
include "sylancr.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "letrd.mm"
include "3brtr4g.mm"
include "exp32.mm"
include "a2d.mm"
include "syl5.mm"
include "findcard2s.mm"
include "imp.mm"

theorem ovolfiniun
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A k
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
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( ( A e. Fin /\ A. k e. A ( B C_ RR /\ ( vol* ` B ) e. RR ) ) -> ( vol* ` U_ k e. A B ) <_ sum_ k e. A ( vol* ` B ) )

  proof
    cA
    cfn
    wcel
    cB
    cr
    wss
    #
    cB
    covol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vk
    cA
    wral
    #
    vk
    cA
    cB
    ciun
    #
    covol
    cfv
    #
    cA
    @1
    vk
    csu
    #
    cle
    wbr
    #
    @3
    vk
    vx
    cv
    #
    wral
    #
    vk
    @9
    cB
    ciun
    #
    covol
    cfv
    #
    @9
    @1
    vk
    csu
    #
    cle
    wbr
    #
    wi
    @3
    vk
    c0
    wral
    #
    vk
    c0
    cB
    ciun
    #
    covol
    cfv
    #
    c0
    @1
    vk
    csu
    #
    cle
    wbr
    #
    wi
    @3
    vk
    vy
    cv
    #
    wral
    #
    vk
    @20
    cB
    ciun
    #
    covol
    cfv
    #
    @20
    @1
    vk
    csu
    #
    cle
    wbr
    #
    wi
    #
    @3
    vk
    @20
    vz
    cv
    #
    csn
    #
    cun
    #
    wral
    #
    vk
    @29
    cB
    ciun
    #
    covol
    cfv
    #
    @29
    @1
    vk
    csu
    #
    cle
    wbr
    #
    wi
    #
    @4
    @8
    wi
    vx
    vy
    vz
    cA
    @9
    c0
    wceq
    #
    @10
    @15
    @14
    @19
    @3
    vk
    @9
    c0
    raleq
    @36
    @12
    @17
    @13
    @18
    cle
    @36
    @11
    @16
    covol
    vk
    @9
    c0
    cB
    iuneq1
    fveq2d
    @9
    c0
    @1
    vk
    sumeq1
    breq12d
    imbi12d
    @9
    @20
    wceq
    #
    @10
    @21
    @14
    @25
    @3
    vk
    @9
    @20
    raleq
    @37
    @12
    @23
    @13
    @24
    cle
    @37
    @11
    @22
    covol
    vk
    @9
    @20
    cB
    iuneq1
    fveq2d
    @9
    @20
    @1
    vk
    sumeq1
    breq12d
    imbi12d
    @9
    @29
    wceq
    #
    @10
    @30
    @14
    @34
    @3
    vk
    @9
    @29
    raleq
    @38
    @12
    @32
    @13
    @33
    cle
    @38
    @11
    @31
    covol
    vk
    @9
    @29
    cB
    iuneq1
    fveq2d
    @9
    @29
    @1
    vk
    sumeq1
    breq12d
    imbi12d
    @9
    cA
    wceq
    #
    @10
    @4
    @14
    @8
    @3
    vk
    @9
    cA
    raleq
    @39
    @12
    @6
    @13
    @7
    cle
    @39
    @11
    @5
    covol
    vk
    @9
    cA
    cB
    iuneq1
    fveq2d
    @9
    cA
    @1
    vk
    sumeq1
    breq12d
    imbi12d
    @19
    @15
    cc0
    cc0
    @17
    @18
    cle
    0le0
    @17
    c0
    covol
    cfv
    cc0
    @16
    c0
    covol
    vk
    cB
    0iun
    fveq2i
    ovol0
    eqtri
    @1
    vk
    sum0
    3brtr4i
    a1i
    @26
    @30
    @25
    wi
    @20
    cfn
    wcel
    #
    @27
    @20
    wcel
    wn
    #
    wa
    #
    @35
    @30
    @21
    @25
    @20
    @29
    wss
    #
    @30
    @21
    wi
    @20
    @28
    ssun1
    #
    @3
    vk
    @20
    @29
    ssralv
    ax-mp
    imim1i
    @42
    @30
    @25
    @34
    @42
    @30
    @25
    @34
    @42
    @30
    @25
    wa
    #
    wa
    #
    vm
    @29
    vk
    vm
    cv
    #
    cB
    csb
    #
    ciun
    #
    covol
    cfv
    #
    @29
    @48
    covol
    cfv
    #
    vm
    csu
    #
    @32
    @33
    cle
    @46
    @50
    vm
    @20
    @48
    ciun
    #
    covol
    cfv
    #
    vk
    @27
    cB
    csb
    #
    covol
    cfv
    #
    caddc
    co
    #
    @52
    @46
    @49
    cr
    wss
    #
    @57
    cr
    wcel
    @50
    @57
    cle
    wbr
    @50
    cr
    wcel
    @46
    @48
    cr
    wss
    #
    vm
    @29
    wral
    @58
    @46
    @59
    vm
    @29
    @46
    @47
    @29
    wcel
    #
    wa
    #
    @59
    @51
    cr
    wcel
    #
    @46
    @30
    @60
    @59
    @62
    wa
    #
    @42
    @30
    @25
    simprl
    #
    @3
    @63
    vk
    @47
    @29
    @59
    @62
    vk
    vk
    @48
    cr
    vk
    @47
    cB
    nfcsb1v
    #
    vk
    cr
    nfcv
    #
    nfss
    vk
    @51
    cr
    vk
    @48
    covol
    vk
    covol
    nfcv
    #
    @65
    nffv
    #
    nfel1
    nfan
    vk
    cv
    #
    @47
    wceq
    #
    @0
    @59
    @2
    @62
    @70
    cB
    @48
    cr
    vk
    @47
    cB
    csbeq1a
    #
    sseq1d
    @70
    @1
    @51
    cr
    @70
    cB
    @48
    covol
    @71
    fveq2d
    #
    eleq1d
    anbi12d
    rspc
    mpan9
    #
    simpld
    ralrimiva
    vm
    @29
    @48
    cr
    iunss
    sylibr
    #
    @46
    @54
    @56
    @46
    @53
    cr
    wss
    #
    @20
    @51
    vm
    csu
    #
    cr
    wcel
    @54
    @76
    cle
    wbr
    @54
    cr
    wcel
    #
    @46
    @53
    @49
    cr
    @43
    @53
    @49
    wss
    @44
    vm
    @20
    @29
    @48
    iunss1
    ax-mp
    @74
    syl5ss
    #
    @46
    @20
    @51
    vm
    @40
    @41
    @45
    simpll
    @47
    @20
    wcel
    @46
    @60
    @62
    @47
    @20
    @28
    elun1
    @61
    @59
    @62
    @73
    simprd
    #
    sylan2
    fsumrecl
    #
    @46
    @23
    @24
    @54
    @76
    cle
    @42
    @30
    @25
    simprr
    @22
    @53
    covol
    vk
    vm
    @20
    cB
    @48
    vm
    cB
    nfcv
    #
    @65
    @71
    cbviun
    fveq2i
    @20
    @1
    @51
    vk
    vm
    vm
    @1
    nfcv
    #
    @68
    @72
    cbvsumi
    3brtr3g
    #
    @53
    @76
    ovollecl
    syl3anc
    #
    @46
    @55
    cr
    wss
    #
    @56
    cr
    wcel
    #
    @27
    @29
    wcel
    @46
    @30
    @85
    @86
    wa
    #
    @28
    @29
    @27
    @28
    @20
    ssun2
    vz
    vsnid
    sselii
    @64
    @3
    @87
    vk
    @27
    @29
    @85
    @86
    vk
    vk
    @55
    cr
    vk
    @27
    cB
    nfcsb1v
    #
    @66
    nfss
    vk
    @56
    cr
    vk
    @55
    covol
    @67
    @88
    nffv
    nfel1
    nfan
    @69
    @27
    wceq
    #
    @0
    @85
    @2
    @86
    @89
    cB
    @55
    cr
    vk
    @27
    cB
    csbeq1a
    #
    sseq1d
    @89
    @1
    @56
    cr
    @89
    cB
    @55
    covol
    @90
    fveq2d
    eleq1d
    anbi12d
    rspc
    mpsyl
    #
    simprd
    #
    readdcld
    #
    @46
    @50
    @53
    @55
    cun
    #
    covol
    cfv
    #
    @57
    cle
    @49
    @94
    covol
    @49
    @53
    vm
    @28
    @48
    ciun
    #
    cun
    @94
    vm
    @20
    @28
    @48
    iunxun
    @96
    @55
    @53
    vm
    @27
    @48
    @55
    vz
    vex
    #
    vk
    @47
    @27
    cB
    csbeq1
    #
    iunxsn
    uneq2i
    eqtri
    fveq2i
    @46
    @75
    @77
    @87
    @95
    @57
    cle
    wbr
    @78
    @84
    @91
    @53
    @55
    ovolun
    syl21anc
    syl5eqbr
    #
    @49
    @57
    ovollecl
    syl3anc
    @93
    @46
    @29
    @51
    vm
    @40
    @29
    cfn
    wcel
    #
    @41
    @45
    @40
    @28
    cfn
    wcel
    @100
    @27
    snfi
    @20
    @28
    unfi
    mpan2
    ad2antrr
    #
    @79
    fsumrecl
    @99
    @46
    @57
    @76
    @56
    caddc
    co
    #
    @52
    cle
    @46
    @54
    @76
    @56
    @84
    @80
    @92
    @83
    leadd1dd
    @46
    @52
    @76
    @28
    @51
    vm
    csu
    #
    caddc
    co
    @102
    @46
    @20
    @28
    @51
    @29
    vm
    @46
    @41
    @20
    @28
    cin
    c0
    wceq
    @40
    @41
    @45
    simplr
    @20
    @27
    disjsn
    sylibr
    @46
    @29
    eqidd
    @101
    @61
    @51
    @79
    recnd
    fsumsplit
    @46
    @103
    @56
    @76
    caddc
    @46
    @27
    cvv
    wcel
    @56
    cc
    wcel
    @103
    @56
    wceq
    @97
    @46
    @56
    @92
    recnd
    @51
    @56
    vm
    @27
    cvv
    @47
    @27
    wceq
    @48
    @55
    covol
    @98
    fveq2d
    sumsn
    sylancr
    oveq2d
    eqtrd
    breqtrrd
    letrd
    @31
    @49
    covol
    vk
    vm
    @29
    cB
    @48
    @81
    @65
    @71
    cbviun
    fveq2i
    @29
    @1
    @51
    vk
    vm
    @82
    @68
    @72
    cbvsumi
    3brtr4g
    exp32
    a2d
    syl5
    findcard2s
    imp
end
