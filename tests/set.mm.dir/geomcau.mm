include "cca.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmul.mm"
include "cabs.mm"
include "cmpt.mm"
include "cc0.mm"
include "cli.mm"
include "cn0.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "rpcnd.mm"
include "rpred.mm"
include "rpge0d.mm"
include "absidd.mm"
include "eqbrtrd.mm"
include "expcnv.mm"
include "cr.mm"
include "1re.mm"
include "resubcl.mm"
include "sylancr.mm"
include "wb.mm"
include "posdif.mm"
include "sylancl.mm"
include "mpbid.mm"
include "elrpd.mm"
include "rerpdivcld.mm"
include "recnd.mm"
include "nnex.mm"
include "mptex.mm"
include "a1i.mm"
include "wa.mm"
include "cc.mm"
include "wceq.mm"
include "nnnn0.mm"
include "adantl.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "cz.mm"
include "nnz.mm"
include "rpexpcl.mm"
include "syl2an.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "mulcomd.mm"
include "weq.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "climmulc2.mm"
include "mul01d.mm"
include "breqtrd.mm"
include "remulcld.mm"
include "clim0c.mm"
include "wi.mm"
include "uzid.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "3syl.mm"
include "cle.mm"
include "cme.mm"
include "wf.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "eluznn.mm"
include "metcl.mm"
include "syl3anc.mm"
include "csu.mm"
include "ad2antrl.mm"
include "nn0zd.mm"
include "ad2antrr.mm"
include "eluznn0.mm"
include "sylan.mm"
include "reexpcld.mm"
include "caddc.mm"
include "cseq.mm"
include "geolim2.mm"
include "eqtr4d.mm"
include "isermulc2.mm"
include "rpexpcld.mm"
include "wne.mm"
include "rpne0d.mm"
include "div12d.mm"
include "isumclim.mm"
include "cdm.mm"
include "seqex.mm"
include "breldm.mm"
include "isumrecl.mm"
include "eqeltrrd.mm"
include "abscld.mm"
include "cfz.mm"
include "fzfid.mm"
include "simpll.mm"
include "elfzuz.mm"
include "simprl.mm"
include "sylan2.mm"
include "ffvelrnda.mm"
include "peano2nn.mm"
include "syl2anc.mm"
include "fsumrecl.mm"
include "simprr.mm"
include "mettrifi.mm"
include "fsumle.mm"
include "wss.mm"
include "fzssuz.mm"
include "0red.mm"
include "metge0.mm"
include "divge0d.mm"
include "ledivmul2d.mm"
include "mpbird.mm"
include "letrd.mm"
include "mulge0d.mm"
include "isumless.mm"
include "leabsd.mm"
include "adantlr.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lelttr.mm"
include "mpand.mm"
include "anassrs.mm"
include "ralrimdva.mm"
include "syld.mm"
include "reximdva.mm"
include "ralimdva.mm"
include "mpd.mm"
include "cxmt.mm"
include "metxmet.mm"
include "eqidd.mm"
include "iscauf.mm"

theorem geomcau
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let vk: setvar k
  let cF: class F
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let cG: class G
  let cJ: class J
  let vm: setvar m
  let cY: class Y
  assume lmclim2.2: |- ( ph -> D e. ( Met ` X ) )
  assume lmclim2.3: |- ( ph -> F : NN --> X )
  assume geomcau.4: |- ( ph -> A e. RR )
  assume geomcau.5: |- ( ph -> B e. RR+ )
  assume geomcau.6: |- ( ph -> B < 1 )
  assume geomcau.7: |- ( ( ph /\ k e. NN ) -> ( ( F ` k ) D ( F ` ( k + 1 ) ) ) <_ ( A x. ( B ^ k ) ) )

  disjoint D k
  disjoint F k
  disjoint X k
  disjoint A k
  disjoint B k
  disjoint k ph
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint D j
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint D n
  disjoint D x
  disjoint F j
  disjoint F n
  disjoint F x
  disjoint G j
  disjoint G k
  disjoint G x
  disjoint J x
  disjoint X j
  disjoint X n
  disjoint X x
  disjoint j m
  disjoint A j
  disjoint k m
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint B j
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint j ph
  disjoint n ph
  disjoint ph x
  disjoint Y j
  disjoint Y k
  disjoint Y x
  assert |- ( ph -> F e. ( Cau ` D ) )

  proof
    wph
    cF
    cD
    cca
    cfv
    wcel
    vj
    cv
    #
    cF
    cfv
    #
    vn
    cv
    #
    cF
    cfv
    #
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vn
    @0
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    #
    wph
    cB
    @2
    cexp
    co
    #
    cA
    c1
    cB
    cmin
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    @5
    clt
    wbr
    #
    vn
    @7
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    #
    @10
    wph
    vm
    cn
    cB
    vm
    cv
    #
    cexp
    co
    #
    @13
    cmul
    co
    #
    cmpt
    #
    cc0
    cli
    wbr
    @19
    wph
    @23
    @13
    cc0
    cmul
    co
    cc0
    cli
    wph
    cc0
    @13
    vn
    vm
    cn0
    @21
    cmpt
    #
    @23
    c1
    cvv
    cn
    nnuz
    wph
    1zzd
    #
    wph
    cB
    vm
    wph
    cB
    geomcau.5
    rpcnd
    #
    wph
    cB
    cabs
    cfv
    #
    cB
    c1
    clt
    wph
    cB
    wph
    cB
    geomcau.5
    rpred
    #
    wph
    cB
    geomcau.5
    rpge0d
    absidd
    geomcau.6
    eqbrtrd
    #
    expcnv
    wph
    @13
    wph
    cA
    @12
    geomcau.4
    wph
    @12
    wph
    c1
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @12
    cr
    wcel
    1re
    @28
    c1
    cB
    resubcl
    sylancr
    #
    wph
    cB
    c1
    clt
    wbr
    #
    cc0
    @12
    clt
    wbr
    #
    geomcau.6
    wph
    @31
    @30
    @33
    @34
    wb
    @28
    1re
    cB
    c1
    posdif
    sylancl
    mpbid
    elrpd
    #
    rerpdivcld
    #
    recnd
    #
    @23
    cvv
    wcel
    wph
    vm
    cn
    @22
    nnex
    mptex
    a1i
    #
    wph
    @2
    cn
    wcel
    #
    wa
    #
    @2
    @24
    cfv
    #
    @11
    cc
    @40
    @2
    cn0
    wcel
    #
    @41
    @11
    wceq
    @39
    @42
    wph
    @2
    nnnn0
    adantl
    vm
    @2
    @21
    @11
    cn0
    @24
    @20
    @2
    cB
    cexp
    oveq2
    #
    @24
    eqid
    cB
    @2
    cexp
    ovex
    fvmpt
    syl
    #
    @40
    @11
    wph
    cB
    crp
    wcel
    #
    @2
    cz
    wcel
    @11
    crp
    wcel
    @39
    geomcau.5
    @2
    nnz
    cB
    @2
    rpexpcl
    syl2an
    #
    rpcnd
    #
    eqeltrd
    @40
    @14
    @13
    @11
    cmul
    co
    @2
    @23
    cfv
    #
    @13
    @41
    cmul
    co
    @40
    @11
    @13
    @47
    wph
    @13
    cc
    wcel
    @39
    @37
    adantr
    mulcomd
    @39
    @48
    @14
    wceq
    wph
    vm
    @2
    @22
    @14
    cn
    @23
    vm
    vn
    weq
    @21
    @11
    @13
    cmul
    @43
    oveq1d
    @23
    eqid
    @11
    @13
    cmul
    ovex
    fvmpt
    adantl
    #
    @40
    @41
    @11
    @13
    cmul
    @44
    oveq2d
    3eqtr4d
    climmulc2
    wph
    @13
    @37
    mul01d
    breqtrd
    wph
    vx
    @14
    vj
    vn
    @23
    c1
    cvv
    cn
    nnuz
    @25
    @38
    @49
    @40
    @14
    @40
    @11
    @13
    @40
    @11
    @46
    rpred
    wph
    @13
    cr
    wcel
    @39
    @36
    adantr
    remulcld
    recnd
    clim0c
    mpbid
    wph
    @18
    @9
    vx
    crp
    wph
    @5
    crp
    wcel
    #
    wa
    #
    @17
    @8
    vj
    cn
    @51
    @0
    cn
    wcel
    #
    wa
    #
    @17
    cB
    @0
    cexp
    co
    #
    @13
    cmul
    co
    #
    cabs
    cfv
    #
    @5
    clt
    wbr
    #
    @8
    @53
    @0
    cz
    wcel
    #
    @0
    @7
    wcel
    @17
    @57
    wi
    @52
    @58
    @51
    @0
    nnz
    adantl
    @0
    uzid
    @16
    @57
    vn
    @0
    @7
    vn
    vj
    weq
    #
    @15
    @56
    @5
    clt
    @59
    @14
    @55
    cabs
    @59
    @11
    @54
    @13
    cmul
    @2
    @0
    cB
    cexp
    oveq2
    oveq1d
    fveq2d
    breq1d
    rspcv
    3syl
    @53
    @57
    @6
    vn
    @7
    @51
    @52
    @2
    @7
    wcel
    #
    @57
    @6
    wi
    @51
    @52
    @60
    wa
    #
    wa
    #
    @4
    @56
    cle
    wbr
    #
    @57
    @6
    wph
    @61
    @63
    @50
    wph
    @61
    wa
    #
    @4
    @55
    @56
    @64
    cD
    cX
    cme
    cfv
    wcel
    #
    @1
    cX
    wcel
    #
    @3
    cX
    wcel
    #
    @4
    cr
    wcel
    #
    wph
    @65
    @61
    lmclim2.2
    adantr
    #
    wph
    cn
    cX
    cF
    wf
    #
    @52
    @66
    @61
    lmclim2.3
    @52
    @60
    simpl
    cn
    cX
    @0
    cF
    ffvelrn
    syl2an
    wph
    @70
    @39
    @67
    @61
    lmclim2.3
    @2
    @0
    eluznn
    cn
    cX
    @2
    cF
    ffvelrn
    syl2an
    @1
    @3
    cD
    cX
    metcl
    syl3anc
    #
    @64
    @7
    cA
    cB
    vk
    cv
    #
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @55
    cr
    @64
    @74
    @55
    vk
    vm
    @7
    cA
    @21
    cmul
    co
    #
    cmpt
    #
    @0
    @7
    @7
    eqid
    #
    @64
    @0
    @52
    @0
    cn0
    wcel
    #
    wph
    @60
    @0
    nnnn0
    ad2antrl
    #
    nn0zd
    #
    @72
    @7
    wcel
    #
    @72
    @77
    cfv
    #
    @74
    wceq
    @64
    vm
    @72
    @76
    @74
    @7
    @77
    vm
    vk
    weq
    @21
    @73
    cA
    cmul
    @20
    @72
    cB
    cexp
    oveq2
    #
    oveq2d
    @77
    eqid
    cA
    @73
    cmul
    ovex
    fvmpt
    adantl
    #
    @64
    @82
    wa
    #
    @74
    @86
    cA
    @73
    wph
    cA
    cr
    wcel
    #
    @61
    @82
    geomcau.4
    ad2antrr
    #
    @86
    cB
    @72
    wph
    @31
    @61
    @82
    @28
    ad2antrr
    @64
    @79
    @82
    @72
    cn0
    wcel
    @80
    @72
    @0
    eluznn0
    sylan
    reexpcld
    #
    remulcld
    #
    recnd
    @64
    caddc
    @77
    @0
    cseq
    #
    cA
    @54
    @12
    cdiv
    co
    #
    cmul
    co
    #
    @55
    cli
    @64
    @92
    cA
    vk
    vm
    @7
    @21
    cmpt
    #
    @77
    @0
    @7
    @78
    @81
    wph
    cA
    cc
    wcel
    @61
    wph
    cA
    geomcau.4
    recnd
    adantr
    #
    @64
    cB
    vk
    @94
    @0
    wph
    cB
    cc
    wcel
    @61
    @26
    adantr
    wph
    @27
    c1
    clt
    wbr
    @61
    @29
    adantr
    @80
    @82
    @72
    @94
    cfv
    #
    @73
    wceq
    @64
    vm
    @72
    @21
    @73
    @7
    @94
    @84
    @94
    eqid
    cB
    @72
    cexp
    ovex
    fvmpt
    adantl
    #
    geolim2
    @86
    @96
    @73
    cc
    @97
    @86
    @73
    @89
    recnd
    eqeltrd
    @86
    @83
    @74
    cA
    @96
    cmul
    co
    @85
    @86
    @96
    @73
    cA
    cmul
    @97
    oveq2d
    eqtr4d
    isermulc2
    #
    @64
    cA
    @54
    @12
    @95
    @64
    @54
    @64
    cB
    @0
    wph
    @45
    @61
    geomcau.5
    adantr
    @81
    rpexpcld
    rpcnd
    wph
    @12
    cc
    wcel
    @61
    wph
    @12
    @32
    recnd
    adantr
    wph
    @12
    cc0
    wne
    @61
    wph
    @12
    @35
    rpne0d
    adantr
    div12d
    breqtrd
    isumclim
    #
    @64
    @74
    vk
    @77
    @0
    @7
    @78
    @81
    @85
    @90
    @64
    @91
    @93
    cli
    wbr
    @91
    cli
    cdm
    wcel
    @98
    @91
    @93
    cli
    caddc
    @77
    @0
    seqex
    cA
    @92
    cmul
    ovex
    breldm
    syl
    #
    isumrecl
    #
    eqeltrrd
    #
    @64
    @55
    @64
    @55
    @102
    recnd
    abscld
    #
    @64
    @4
    @75
    @55
    cle
    @64
    @4
    @0
    @2
    c1
    cmin
    co
    #
    cfz
    co
    #
    @72
    cF
    cfv
    #
    @72
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cD
    co
    #
    vk
    csu
    #
    @75
    @71
    @64
    @105
    @109
    vk
    @64
    @0
    @104
    fzfid
    #
    @64
    @72
    @105
    wcel
    #
    wa
    #
    wph
    @72
    cn
    wcel
    #
    @109
    cr
    wcel
    #
    wph
    @61
    @112
    simpll
    #
    @112
    @64
    @82
    @114
    @72
    @0
    @104
    elfzuz
    #
    @64
    @52
    @82
    @114
    wph
    @52
    @60
    simprl
    @72
    @0
    eluznn
    sylan
    #
    sylan2
    #
    wph
    @114
    wa
    #
    @65
    @106
    cX
    wcel
    #
    @108
    cX
    wcel
    #
    @115
    wph
    @65
    @114
    lmclim2.2
    adantr
    #
    wph
    cn
    cX
    @72
    cF
    lmclim2.3
    ffvelrnda
    #
    wph
    @70
    @107
    cn
    wcel
    @122
    @114
    lmclim2.3
    @72
    peano2nn
    cn
    cX
    @107
    cF
    ffvelrn
    syl2an
    #
    @106
    @108
    cD
    cX
    metcl
    syl3anc
    #
    syl2anc
    #
    fsumrecl
    #
    @101
    @64
    cD
    vk
    cF
    @0
    @2
    cX
    @69
    wph
    @52
    @60
    simprr
    @72
    @0
    @2
    cfz
    co
    wcel
    @64
    @82
    @121
    @72
    @0
    @2
    elfzuz
    @86
    wph
    @114
    @121
    wph
    @61
    @82
    simpll
    #
    @118
    @124
    syl2anc
    sylan2
    mettrifi
    @64
    @110
    @105
    @74
    vk
    csu
    @75
    @128
    @64
    @105
    @74
    vk
    @111
    @112
    @64
    @82
    @74
    cr
    wcel
    @117
    @90
    sylan2
    #
    fsumrecl
    @101
    @64
    @105
    @109
    @74
    vk
    @111
    @127
    @130
    @113
    wph
    @114
    @109
    @74
    cle
    wbr
    #
    @116
    @119
    geomcau.7
    syl2anc
    fsumle
    @64
    @105
    @74
    vk
    @77
    @0
    @7
    @78
    @81
    @111
    @105
    @7
    wss
    @64
    @0
    @104
    fzssuz
    a1i
    @85
    @90
    @86
    cA
    @73
    @88
    @89
    @86
    wph
    @114
    cc0
    cA
    cle
    wbr
    @129
    @118
    @120
    cc0
    @109
    @73
    cdiv
    co
    #
    cA
    @120
    0red
    @120
    @109
    @73
    @126
    wph
    @45
    @72
    cz
    wcel
    @73
    crp
    wcel
    #
    @114
    geomcau.5
    @72
    nnz
    cB
    @72
    rpexpcl
    syl2an
    #
    rerpdivcld
    wph
    @87
    @114
    geomcau.4
    adantr
    #
    @120
    @109
    @73
    @126
    @134
    @120
    @65
    @121
    @122
    cc0
    @109
    cle
    wbr
    @123
    @124
    @125
    @106
    @108
    cD
    cX
    metge0
    syl3anc
    divge0d
    @120
    @132
    cA
    cle
    wbr
    @131
    geomcau.7
    @120
    @109
    cA
    @73
    @126
    @135
    @134
    ledivmul2d
    mpbird
    letrd
    syl2anc
    @86
    @73
    @86
    wph
    @114
    @133
    @129
    @118
    @134
    syl2anc
    rpge0d
    mulge0d
    @100
    isumless
    letrd
    letrd
    @99
    breqtrd
    @64
    @55
    @102
    leabsd
    letrd
    adantlr
    @62
    @68
    @56
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @63
    @57
    wa
    @6
    wi
    wph
    @61
    @68
    @50
    @71
    adantlr
    wph
    @61
    @136
    @50
    @103
    adantlr
    @50
    @137
    wph
    @61
    @5
    rpre
    ad2antlr
    @4
    @56
    @5
    lelttr
    syl3anc
    mpand
    anassrs
    ralrimdva
    syld
    reximdva
    ralimdva
    mpd
    wph
    vx
    @3
    @1
    cD
    vj
    vn
    cF
    c1
    cX
    cn
    nnuz
    wph
    @65
    cD
    cX
    cxmt
    cfv
    wcel
    lmclim2.2
    cD
    cX
    metxmet
    syl
    @25
    @40
    @3
    eqidd
    wph
    @52
    wa
    @1
    eqidd
    lmclim2.3
    iscauf
    mpbird
end
