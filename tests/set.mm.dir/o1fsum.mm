include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "wi.mm"
include "cn.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "c1.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "crp.mm"
include "cfl.mm"
include "cfz.mm"
include "csu.mm"
include "cdiv.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wss.mm"
include "nnssre.mm"
include "a1i.mm"
include "o1mptrcl.mm"
include "1red.mm"
include "elo1mpt2.mm"
include "mpbid.mm"
include "wa.mm"
include "csb.mm"
include "caddc.mm"
include "rpssre.mm"
include "cc.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "fzfid.mm"
include "wf.mm"
include "cdm.mm"
include "o1f.mm"
include "syl.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "feq2d.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "ad3antrrr.mm"
include "elfznn.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "impcom.mm"
include "syl2an.mm"
include "fsumcl.mm"
include "syl5eqel.mm"
include "rpcn.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "rpne0.mm"
include "divcld.mm"
include "simplrl.mm"
include "wb.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "sylib.mm"
include "simpld.mm"
include "ad2antrr.mm"
include "abscld.mm"
include "fsumrecl.mm"
include "simplrr.mm"
include "readdcld.mm"
include "absdivd.mm"
include "adantrr.mm"
include "rprege0.mm"
include "ad2antrl.mm"
include "absid.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "cmul.mm"
include "adantlr.mm"
include "adantr.mm"
include "remulcld.mm"
include "fveq2i.mm"
include "fsumabs.mm"
include "syl5eqbr.mm"
include "cun.mm"
include "ssun2.mm"
include "flge1nn.mm"
include "nnred.mm"
include "flle.mm"
include "simprr.mm"
include "letrd.mm"
include "fznnfl.mm"
include "mpbir2and.mm"
include "fzsplit.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "syldan.mm"
include "recnd.mm"
include "mulid2d.mm"
include "absge0d.mm"
include "fsumge0.mm"
include "jca.mm"
include "simprd.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "eqbrtrrd.mm"
include "chash.mm"
include "cfn.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0re.mm"
include "3syl.mm"
include "cuz.mm"
include "elfzuz.mm"
include "peano2nnd.mm"
include "eluznn.mm"
include "sylan.mm"
include "simpllr.mm"
include "reflcl.mm"
include "peano2re.mm"
include "fllep1.mm"
include "eluzle.mm"
include "nfv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfim.mm"
include "breq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "syl3c.mm"
include "sylan2.mm"
include "fsumle.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "breqtrd.mm"
include "cz.mm"
include "nnzd.mm"
include "uzid.mm"
include "0red.mm"
include "mpan9.mm"
include "biidd.mm"
include "rspcv.mm"
include "sylc.mm"
include "cdom.mm"
include "ssdomg.mm"
include "hashdomi.mm"
include "flge0nn0.mm"
include "hashfz1.mm"
include "lemul1ad.mm"
include "le2addd.mm"
include "clt.mm"
include "cin.mm"
include "c0.mm"
include "ltp1.mm"
include "fzdisj.mm"
include "fsumsplit.mm"
include "adddid.mm"
include "3brtr4d.mm"
include "rpregt0.mm"
include "ledivmul.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "elo1d.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem o1fsum
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  let cV: class V
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  assume o1fsum.1: |- ( ( ph /\ k e. NN ) -> A e. V )
  assume o1fsum.2: |- ( ph -> ( k e. NN |-> A ) e. O(1) )

  disjoint A x
  disjoint k x
  disjoint k ph
  disjoint ph x
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint A c
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint c k
  disjoint c ph
  disjoint k m
  disjoint k n
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> ( x e. RR+ |-> ( sum_ k e. ( 1 ... ( |_ ` x ) ) A / x ) ) e. O(1) )

  proof
    wph
    vc
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    cA
    cabs
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    wi
    #
    vk
    cn
    wral
    #
    vm
    cr
    wrex
    vc
    c1
    cpnf
    cico
    co
    #
    wrex
    #
    vx
    crp
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    cA
    vk
    csu
    #
    @10
    cdiv
    co
    #
    cmpt
    co1
    wcel
    #
    wph
    vk
    cn
    cA
    cmpt
    #
    co1
    wcel
    #
    @9
    o1fsum.2
    wph
    vk
    vc
    cn
    cA
    c1
    vm
    cn
    cr
    wss
    wph
    nnssre
    a1i
    wph
    vk
    cn
    cA
    cV
    o1fsum.1
    o1fsum.2
    o1mptrcl
    wph
    1red
    elo1mpt2
    mpbid
    wph
    @7
    @15
    vc
    vm
    @8
    cr
    wph
    @0
    @8
    wcel
    #
    @4
    cr
    wcel
    #
    wa
    #
    wa
    #
    @7
    @15
    @21
    @7
    wa
    #
    vx
    crp
    @14
    @0
    c1
    @0
    cfl
    cfv
    #
    cfz
    co
    #
    vk
    vn
    cv
    #
    cA
    csb
    #
    cabs
    cfv
    #
    vn
    csu
    #
    @4
    caddc
    co
    #
    crp
    cr
    wss
    @22
    rpssre
    a1i
    @22
    @10
    crp
    wcel
    #
    wa
    #
    @13
    @10
    @31
    @13
    @12
    @26
    vn
    csu
    #
    cc
    @12
    cA
    @26
    vk
    vn
    vn
    cA
    nfcv
    vk
    @25
    cA
    nfcsb1v
    #
    vk
    @25
    cA
    csbeq1a
    #
    cbvsumi
    #
    @31
    @12
    @26
    vn
    @31
    c1
    @11
    fzfid
    @31
    cA
    cc
    wcel
    #
    vk
    cn
    wral
    #
    @25
    cn
    wcel
    #
    @26
    cc
    wcel
    #
    @25
    @12
    wcel
    #
    wph
    @37
    @20
    @7
    @30
    wph
    cn
    cc
    @16
    wf
    #
    @37
    wph
    @16
    cdm
    #
    cc
    @16
    wf
    #
    @41
    wph
    @17
    @43
    o1fsum.2
    @16
    o1f
    syl
    wph
    @42
    cn
    cc
    @16
    wph
    cA
    cV
    wcel
    #
    vk
    cn
    wral
    @42
    cn
    wceq
    wph
    @44
    vk
    cn
    o1fsum.1
    ralrimiva
    vk
    cn
    cA
    cV
    dmmptg
    syl
    feq2d
    mpbid
    vk
    cn
    cc
    cA
    @16
    @16
    eqid
    fmpt
    sylibr
    #
    ad3antrrr
    @25
    @11
    elfznn
    #
    @38
    @37
    @39
    @36
    @39
    vk
    @25
    cn
    vk
    @26
    cc
    @33
    nfel1
    @1
    @25
    wceq
    #
    cA
    @26
    cc
    @34
    eleq1d
    rspc
    #
    impcom
    #
    syl2an
    fsumcl
    syl5eqel
    #
    @30
    @10
    cc
    wcel
    #
    @22
    @10
    rpcn
    adantl
    #
    @30
    @10
    cc0
    wne
    @22
    @10
    rpne0
    adantl
    #
    divcld
    @22
    @0
    cr
    wcel
    #
    c1
    @0
    cle
    wbr
    #
    @22
    @18
    @54
    @55
    wa
    #
    wph
    @18
    @19
    @7
    simplrl
    c1
    cr
    wcel
    #
    @18
    @56
    wb
    1re
    c1
    @0
    elicopnf
    ax-mp
    sylib
    #
    simpld
    #
    @22
    @28
    @4
    @22
    @24
    @27
    vn
    @22
    c1
    @23
    fzfid
    #
    @22
    @25
    @24
    wcel
    #
    wa
    #
    @26
    @22
    @37
    @38
    @39
    @61
    wph
    @37
    @20
    @7
    @45
    ad2antrr
    #
    @25
    @23
    elfznn
    @49
    syl2an
    #
    abscld
    #
    fsumrecl
    #
    wph
    @18
    @19
    @7
    simplrr
    #
    readdcld
    @22
    @30
    @0
    @10
    cle
    wbr
    #
    wa
    #
    wa
    #
    @14
    cabs
    cfv
    #
    @13
    cabs
    cfv
    #
    @10
    cdiv
    co
    #
    @29
    cle
    @70
    @71
    @72
    @10
    cabs
    cfv
    #
    cdiv
    co
    #
    @73
    @22
    @30
    @71
    @75
    wceq
    @68
    @31
    @13
    @10
    @50
    @52
    @53
    absdivd
    adantrr
    @70
    @74
    @10
    @72
    cdiv
    @70
    @10
    cr
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    wa
    #
    @74
    @10
    wceq
    @30
    @78
    @22
    @68
    @10
    rprege0
    ad2antrl
    #
    @10
    absid
    syl
    oveq2d
    eqtrd
    @70
    @73
    @29
    cle
    wbr
    #
    @72
    @10
    @29
    cmul
    co
    #
    cle
    wbr
    #
    @70
    @72
    @12
    @27
    vn
    csu
    #
    @81
    @70
    @13
    @22
    @30
    @13
    cc
    wcel
    @68
    @50
    adantrr
    abscld
    #
    @70
    @12
    @27
    vn
    @70
    c1
    @11
    fzfid
    #
    @70
    @40
    wa
    #
    @26
    @22
    @40
    @39
    @69
    @22
    @37
    @38
    @39
    @40
    @63
    @46
    @49
    syl2an
    #
    adantlr
    #
    abscld
    fsumrecl
    @70
    @10
    @29
    @70
    @76
    @77
    @79
    simpld
    #
    @70
    @28
    @4
    @22
    @28
    cr
    wcel
    #
    @69
    @66
    adantr
    #
    @22
    @19
    @69
    @67
    adantr
    #
    readdcld
    #
    remulcld
    @70
    @72
    @32
    cabs
    cfv
    @83
    cle
    @13
    @32
    cabs
    @35
    fveq2i
    @70
    @12
    @26
    vn
    @85
    @88
    fsumabs
    syl5eqbr
    @70
    @28
    @23
    c1
    caddc
    co
    #
    @11
    cfz
    co
    #
    @27
    vn
    csu
    #
    caddc
    co
    @10
    @28
    cmul
    co
    #
    @10
    @4
    cmul
    co
    #
    caddc
    co
    @83
    @81
    cle
    @70
    @28
    @96
    @97
    @98
    @91
    @70
    @95
    @27
    vn
    @70
    @94
    @11
    fzfid
    #
    @70
    @25
    @95
    wcel
    #
    @40
    @27
    cr
    wcel
    #
    @70
    @95
    @12
    @25
    @70
    @24
    @95
    cun
    #
    @95
    @12
    @95
    @24
    ssun2
    @70
    @23
    @12
    wcel
    #
    @12
    @102
    wceq
    @70
    @103
    @23
    cn
    wcel
    #
    @23
    @10
    cle
    wbr
    #
    @22
    @104
    @69
    @22
    @56
    @104
    @58
    @0
    flge1nn
    syl
    adantr
    #
    @70
    @23
    @0
    @10
    @70
    @23
    @106
    nnred
    #
    @22
    @54
    @69
    @59
    adantr
    #
    @89
    @70
    @54
    @23
    @0
    cle
    wbr
    @108
    @0
    flle
    syl
    @22
    @30
    @68
    simprr
    #
    letrd
    @70
    @76
    @103
    @104
    @105
    wa
    wb
    @89
    @23
    @10
    fznnfl
    syl
    mpbir2and
    @23
    c1
    @11
    fzsplit
    syl
    #
    syl5sseqr
    #
    sselda
    @22
    @40
    @101
    @69
    @22
    @40
    wa
    @26
    @87
    abscld
    adantlr
    #
    syldan
    #
    fsumrecl
    #
    @70
    @10
    @28
    @89
    @91
    remulcld
    @70
    @10
    @4
    @89
    @92
    remulcld
    #
    @70
    c1
    @28
    cmul
    co
    #
    @28
    @97
    cle
    @70
    @28
    @70
    @28
    @91
    recnd
    #
    mulid2d
    @70
    @57
    @76
    @90
    cc0
    @28
    cle
    wbr
    #
    wa
    #
    c1
    @10
    cle
    wbr
    @116
    @97
    cle
    wbr
    @70
    1red
    #
    @89
    @22
    @119
    @69
    @22
    @90
    @118
    @66
    @22
    @24
    @27
    vn
    @60
    @65
    @62
    @26
    @64
    absge0d
    fsumge0
    jca
    adantr
    @70
    c1
    @0
    @10
    @120
    @108
    @89
    @22
    @55
    @69
    @22
    @54
    @55
    @58
    simprd
    adantr
    @109
    letrd
    c1
    @10
    @28
    lemul1a
    syl31anc
    eqbrtrrd
    @70
    @96
    @95
    chash
    cfv
    #
    @4
    cmul
    co
    #
    @98
    @114
    @70
    @121
    @4
    @70
    @95
    cfn
    wcel
    #
    @121
    cn0
    wcel
    @121
    cr
    wcel
    @99
    @95
    hashcl
    @121
    nn0re
    3syl
    #
    @92
    remulcld
    @115
    @70
    @96
    @95
    @4
    vn
    csu
    #
    @122
    cle
    @70
    @95
    @27
    @4
    vn
    @99
    @113
    @70
    @19
    @100
    @92
    adantr
    @100
    @70
    @25
    @94
    cuz
    cfv
    #
    wcel
    #
    @27
    @4
    cle
    wbr
    #
    @25
    @94
    @11
    elfzuz
    @70
    @127
    wa
    #
    @38
    @7
    @0
    @25
    cle
    wbr
    #
    @128
    @70
    @94
    cn
    wcel
    @127
    @38
    @70
    @23
    @106
    peano2nnd
    #
    @25
    @94
    eluznn
    sylan
    #
    @21
    @7
    @69
    @127
    simpllr
    @129
    @0
    @94
    @25
    @70
    @54
    @127
    @108
    adantr
    #
    @129
    @54
    @23
    cr
    wcel
    #
    @94
    cr
    wcel
    @133
    @0
    reflcl
    @23
    peano2re
    3syl
    @129
    @25
    @132
    nnred
    @129
    @54
    @0
    @94
    cle
    wbr
    @133
    @0
    fllep1
    syl
    @127
    @94
    @25
    cle
    wbr
    @70
    @94
    @25
    eluzle
    adantl
    letrd
    @6
    @130
    @128
    wi
    vk
    @25
    cn
    @130
    @128
    vk
    @130
    vk
    nfv
    vk
    @27
    @4
    cle
    vk
    @26
    cabs
    vk
    cabs
    nfcv
    @33
    nffv
    vk
    cle
    nfcv
    vk
    @4
    nfcv
    nfbr
    nfim
    @47
    @2
    @130
    @5
    @128
    @1
    @25
    @0
    cle
    breq2
    @47
    @3
    @27
    @4
    cle
    @47
    cA
    @26
    cabs
    @34
    fveq2d
    breq1d
    imbi12d
    rspc
    syl3c
    #
    sylan2
    fsumle
    @70
    @123
    @4
    cc
    wcel
    @125
    @122
    wceq
    @99
    @70
    @4
    @92
    recnd
    #
    @95
    @4
    vn
    fsumconst
    syl2anc
    breqtrd
    @70
    @121
    @10
    @4
    @124
    @89
    @92
    @70
    @94
    @126
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    vn
    @126
    wral
    @138
    @70
    @94
    cz
    wcel
    @137
    @70
    @94
    @131
    nnzd
    @94
    uzid
    syl
    @70
    @138
    vn
    @126
    @129
    cc0
    @27
    @4
    @129
    0red
    @129
    @26
    @70
    @127
    @38
    @39
    @132
    @22
    @38
    @39
    @69
    @22
    @37
    @38
    @39
    @63
    @48
    mpan9
    adantlr
    syldan
    #
    abscld
    @70
    @19
    @127
    @92
    adantr
    @129
    @26
    @139
    absge0d
    @135
    letrd
    ralrimiva
    @138
    @138
    vn
    @94
    @126
    @25
    @94
    wceq
    @138
    biidd
    rspcv
    sylc
    @70
    @121
    @11
    @10
    @124
    @70
    @76
    @11
    cr
    wcel
    @89
    @10
    reflcl
    syl
    @89
    @70
    @121
    @12
    chash
    cfv
    #
    @11
    cle
    @70
    @95
    @12
    cdom
    wbr
    #
    @121
    @140
    cle
    wbr
    @70
    @12
    cfn
    wcel
    @95
    @12
    wss
    @141
    @85
    @111
    @95
    @12
    cfn
    ssdomg
    sylc
    @95
    @12
    hashdomi
    syl
    @70
    @78
    @11
    cn0
    wcel
    @140
    @11
    wceq
    @79
    @10
    flge0nn0
    @11
    hashfz1
    3syl
    breqtrd
    @70
    @76
    @11
    @10
    cle
    wbr
    @89
    @10
    flle
    syl
    letrd
    lemul1ad
    letrd
    le2addd
    @70
    @24
    @95
    @27
    @12
    vn
    @70
    @134
    @23
    @94
    clt
    wbr
    @24
    @95
    cin
    c0
    wceq
    @107
    @23
    ltp1
    c1
    @23
    @94
    @11
    fzdisj
    3syl
    @110
    @85
    @86
    @27
    @112
    recnd
    fsumsplit
    @70
    @10
    @28
    @4
    @22
    @30
    @51
    @68
    @52
    adantrr
    @117
    @136
    adddid
    3brtr4d
    letrd
    @70
    @72
    cr
    wcel
    @29
    cr
    wcel
    @76
    cc0
    @10
    clt
    wbr
    wa
    #
    @80
    @82
    wb
    @84
    @93
    @30
    @142
    @22
    @68
    @10
    rpregt0
    ad2antrl
    @72
    @29
    @10
    ledivmul
    syl3anc
    mpbird
    eqbrtrd
    elo1d
    ex
    rexlimdvva
    mpd
end
