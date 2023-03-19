include "cn.mm"
include "cv.mm"
include "cre.mm"
include "cfv.mm"
include "cneg.mm"
include "ccxp.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "wceq.mm"
include "oveq1.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "clog.mm"
include "cmul.mm"
include "ce.mm"
include "cc.mm"
include "nncn.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "negcld.mm"
include "adantr.mm"
include "cxpefd.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "nnrp.mm"
include "relogcld.mm"
include "recnd.mm"
include "mulcl.mm"
include "syl2an.mm"
include "absef.mm"
include "syl.mm"
include "cim.mm"
include "cmin.mm"
include "remul.mm"
include "renegd.mm"
include "rered.mm"
include "oveqan12d.mm"
include "reim0d.mm"
include "oveq2d.mm"
include "imcl.mm"
include "mul01d.mm"
include "sylan9eqr.mm"
include "oveq12d.mm"
include "recld.mm"
include "renegcld.mm"
include "subid1d.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "cxpcld.mm"
include "eqeltrd.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "cn0.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "wbr.mm"
include "crp.mm"
include "cr.mm"
include "2rp.mm"
include "1re.mm"
include "resubcl.mm"
include "sylancr.mm"
include "rpcxpcl.mm"
include "rpcnd.mm"
include "clt.mm"
include "recl.mm"
include "addid2d.mm"
include "breqtrrd.mm"
include "wb.mm"
include "0re.mm"
include "ltsubadd.mm"
include "mp3an13.mm"
include "mpbird.mm"
include "2re.mm"
include "1lt2.mm"
include "cxplt.mm"
include "mpanl12.mm"
include "sylancl.mm"
include "mpbid.mm"
include "cle.mm"
include "rprege0d.mm"
include "absid.mm"
include "2cn.mm"
include "cxp0.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "a1i.mm"
include "3brtr4d.mm"
include "oveq2.mm"
include "geolim.mm"
include "seqex.mm"
include "breldm.mm"
include "syl2anr.mm"
include "rpred.mm"
include "rpge0d.mm"
include "nnre.mm"
include "lep1d.mm"
include "reeflogd.mm"
include "peano2nn.mm"
include "nnrpd.mm"
include "efle.mm"
include "syl2anc.mm"
include "0lt1.mm"
include "lttrd.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "remulcl.mm"
include "lenegd.mm"
include "mulneg1.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "nn0re.mm"
include "mulcomd.mm"
include "cxpmuld.mm"
include "simpr.mm"
include "cxpexp.mm"
include "ax-1cn.mm"
include "negsub.mm"
include "eqcomd.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "mpan.mm"
include "1cnd.mm"
include "cxpaddd.mm"
include "3eqtr3d.mm"
include "sylan.mm"
include "cxp1d.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "climcnds.mm"
include "abscvgcvg.mm"

theorem zetacvg
  let wph: wff ph
  let cS: class S
  let vk: setvar k
  let cF: class F
  let vm: setvar m
  let vn: setvar n
  assume zetacvg.1: |- ( ph -> S e. CC )
  assume zetacvg.2: |- ( ph -> 1 < ( Re ` S ) )
  assume zetacvg.3: |- ( ( ph /\ k e. NN ) -> ( F ` k ) = ( k ^c -u S ) )

  disjoint S k
  disjoint F k
  disjoint k ph
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint S m
  disjoint S n
  disjoint m ph
  assert |- ( ph -> seq 1 ( + , F ) e. dom ~~> )

  proof
    wph
    vk
    vn
    cn
    vn
    cv
    #
    cS
    cre
    cfv
    #
    cneg
    #
    ccxp
    co
    #
    cmpt
    #
    cF
    c1
    cn
    nnuz
    wph
    1zzd
    wph
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    @5
    @4
    cfv
    #
    @5
    @2
    ccxp
    co
    #
    @5
    cF
    cfv
    #
    cabs
    cfv
    #
    @6
    @8
    @9
    wceq
    wph
    vn
    @5
    @3
    @9
    cn
    @4
    @0
    @5
    @2
    ccxp
    oveq1
    @4
    eqid
    #
    @5
    @2
    ccxp
    ovex
    fvmpt
    adantl
    #
    @7
    @11
    cS
    cneg
    #
    @5
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cabs
    cfv
    #
    @16
    cre
    cfv
    #
    ce
    cfv
    #
    @9
    @7
    @10
    @17
    cabs
    @7
    @10
    @5
    @14
    ccxp
    co
    #
    @17
    zetacvg.3
    @7
    @5
    @14
    @6
    @5
    cc
    wcel
    wph
    @5
    nncn
    adantl
    #
    @6
    @5
    cc0
    wne
    wph
    @5
    nnne0
    adantl
    #
    wph
    @14
    cc
    wcel
    #
    @6
    wph
    cS
    zetacvg.1
    negcld
    #
    adantr
    #
    cxpefd
    eqtrd
    fveq2d
    @7
    @16
    cc
    wcel
    #
    @18
    @20
    wceq
    wph
    @24
    @15
    cc
    wcel
    #
    @27
    @6
    @25
    @6
    @15
    @6
    @5
    @5
    nnrp
    #
    relogcld
    #
    recnd
    #
    @14
    @15
    mulcl
    syl2an
    @16
    absef
    syl
    @7
    @20
    @2
    @15
    cmul
    co
    #
    ce
    cfv
    #
    @9
    @7
    @19
    @32
    ce
    @7
    @19
    @14
    cre
    cfv
    #
    @15
    cre
    cfv
    #
    cmul
    co
    #
    @14
    cim
    cfv
    #
    @15
    cim
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @32
    cc0
    cmin
    co
    @32
    wph
    @24
    @28
    @19
    @40
    wceq
    @6
    @25
    @31
    @14
    @15
    remul
    syl2an
    @7
    @36
    @32
    @39
    cc0
    cmin
    wph
    @6
    @34
    @2
    @35
    @15
    cmul
    wph
    cS
    zetacvg.1
    renegd
    @6
    @15
    @30
    rered
    oveqan12d
    @6
    wph
    @39
    @37
    cc0
    cmul
    co
    cc0
    @6
    @38
    cc0
    @37
    cmul
    @6
    @15
    @30
    reim0d
    oveq2d
    wph
    @37
    wph
    @24
    @37
    cc
    wcel
    @25
    @24
    @37
    @14
    imcl
    recnd
    syl
    mul01d
    sylan9eqr
    oveq12d
    @7
    @32
    wph
    @2
    cc
    wcel
    #
    @28
    @32
    cc
    wcel
    @6
    wph
    @2
    wph
    @1
    wph
    cS
    zetacvg.1
    recld
    #
    renegcld
    #
    recnd
    #
    @31
    @2
    @15
    mulcl
    syl2an
    subid1d
    3eqtrd
    fveq2d
    @7
    @5
    @2
    @22
    @23
    wph
    @41
    @6
    @44
    adantr
    #
    cxpefd
    #
    eqtr4d
    3eqtrd
    eqtr4d
    @7
    @10
    @21
    cc
    zetacvg.3
    @7
    @5
    @14
    @22
    @26
    cxpcld
    eqeltrd
    wph
    caddc
    @4
    c1
    cseq
    cli
    cdm
    #
    wcel
    caddc
    vn
    cn0
    c2
    c1
    @1
    cmin
    co
    #
    ccxp
    co
    #
    @0
    cexp
    co
    #
    cmpt
    #
    cc0
    cseq
    #
    @47
    wcel
    #
    wph
    @52
    c1
    c1
    @49
    cmin
    co
    #
    cdiv
    co
    #
    cli
    wbr
    @53
    wph
    @49
    vm
    @51
    wph
    @49
    wph
    c2
    crp
    wcel
    #
    @48
    cr
    wcel
    #
    @49
    crp
    wcel
    2rp
    wph
    c1
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @57
    1re
    @42
    c1
    @1
    resubcl
    sylancr
    #
    c2
    @48
    rpcxpcl
    sylancr
    #
    rpcnd
    #
    wph
    @49
    c2
    cc0
    ccxp
    co
    #
    @49
    cabs
    cfv
    #
    c1
    clt
    wph
    @48
    cc0
    clt
    wbr
    #
    @49
    @63
    clt
    wbr
    #
    wph
    @65
    c1
    cc0
    @1
    caddc
    co
    #
    clt
    wbr
    #
    wph
    c1
    @1
    @67
    clt
    zetacvg.2
    wph
    @1
    wph
    cS
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    zetacvg.1
    @69
    @1
    cS
    recl
    recnd
    syl
    #
    addid2d
    breqtrrd
    wph
    @59
    @65
    @68
    wb
    #
    @42
    @58
    @59
    cc0
    cr
    wcel
    #
    @72
    1re
    0re
    c1
    @1
    cc0
    ltsubadd
    mp3an13
    syl
    mpbird
    wph
    @57
    @73
    @65
    @66
    wb
    #
    @60
    0re
    c2
    cr
    wcel
    c1
    c2
    clt
    wbr
    @57
    @73
    wa
    @74
    2re
    1lt2
    c2
    @48
    cc0
    cxplt
    mpanl12
    sylancl
    mpbid
    wph
    @49
    cr
    wcel
    cc0
    @49
    cle
    wbr
    wa
    @64
    @49
    wceq
    wph
    @49
    @61
    rprege0d
    @49
    absid
    syl
    c1
    @63
    wceq
    wph
    @63
    c1
    c2
    cc
    wcel
    #
    @63
    c1
    wceq
    2cn
    c2
    cxp0
    ax-mp
    eqcomi
    a1i
    3brtr4d
    vm
    cv
    #
    cn0
    wcel
    #
    @76
    @51
    cfv
    #
    @49
    @76
    cexp
    co
    #
    wceq
    wph
    vn
    @76
    @50
    @79
    cn0
    @51
    @0
    @76
    @49
    cexp
    oveq2
    @51
    eqid
    @49
    @76
    cexp
    ovex
    fvmpt
    adantl
    #
    geolim
    @52
    @55
    cli
    caddc
    @51
    cc0
    seqex
    c1
    @54
    cdiv
    ovex
    breldm
    syl
    wph
    vk
    vm
    @4
    @51
    @7
    @8
    @9
    cr
    @13
    @7
    @9
    @6
    @5
    crp
    wcel
    @2
    cr
    wcel
    #
    @9
    crp
    wcel
    wph
    @29
    @43
    @5
    @2
    rpcxpcl
    syl2anr
    #
    rpred
    eqeltrd
    @7
    cc0
    @9
    @8
    cle
    @7
    @9
    @82
    rpge0d
    @13
    breqtrrd
    @7
    @2
    @5
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @33
    @83
    @4
    cfv
    #
    @8
    cle
    @7
    @85
    @32
    cle
    wbr
    #
    @86
    @33
    cle
    wbr
    #
    @7
    @1
    @84
    cmul
    co
    #
    cneg
    #
    @1
    @15
    cmul
    co
    #
    cneg
    #
    @85
    @32
    cle
    @7
    @92
    @90
    cle
    wbr
    #
    @91
    @93
    cle
    wbr
    @7
    @15
    @84
    cle
    wbr
    #
    @94
    @6
    @95
    wph
    @6
    @95
    @15
    ce
    cfv
    #
    @84
    ce
    cfv
    #
    cle
    wbr
    #
    @6
    @5
    @83
    @96
    @97
    cle
    @6
    @5
    @5
    nnre
    lep1d
    @6
    @5
    @29
    reeflogd
    @6
    @83
    @6
    @83
    @5
    peano2nn
    #
    nnrpd
    #
    reeflogd
    3brtr4d
    @6
    @15
    cr
    wcel
    #
    @84
    cr
    wcel
    #
    @95
    @98
    wb
    @30
    @6
    @83
    @100
    relogcld
    #
    @15
    @84
    efle
    syl2anc
    mpbird
    adantl
    @7
    @101
    @102
    @59
    cc0
    @1
    clt
    wbr
    #
    @95
    @94
    wb
    @6
    @101
    wph
    @30
    adantl
    @7
    @83
    @7
    @83
    @6
    @83
    cn
    wcel
    #
    wph
    @99
    adantl
    #
    nnrpd
    relogcld
    wph
    @59
    @6
    @42
    adantr
    wph
    @104
    @6
    wph
    cc0
    c1
    @1
    @73
    wph
    0re
    a1i
    @58
    wph
    1re
    a1i
    @42
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    zetacvg.2
    lttrd
    adantr
    @15
    @84
    @1
    lemul2
    syl112anc
    mpbid
    @7
    @92
    @90
    wph
    @59
    @101
    @92
    cr
    wcel
    @6
    @42
    @30
    @1
    @15
    remulcl
    syl2an
    wph
    @59
    @102
    @90
    cr
    wcel
    @6
    @42
    @103
    @1
    @84
    remulcl
    syl2an
    lenegd
    mpbid
    wph
    @70
    @84
    cc
    wcel
    @85
    @91
    wceq
    @6
    @71
    @6
    @84
    @103
    recnd
    @1
    @84
    mulneg1
    syl2an
    wph
    @70
    @28
    @32
    @93
    wceq
    @6
    @71
    @31
    @1
    @15
    mulneg1
    syl2an
    3brtr4d
    @7
    @85
    cr
    wcel
    #
    @32
    cr
    wcel
    #
    @88
    @89
    wb
    wph
    @81
    @102
    @107
    @6
    @43
    @103
    @2
    @84
    remulcl
    syl2an
    wph
    @81
    @101
    @108
    @6
    @43
    @30
    @2
    @15
    remulcl
    syl2an
    @85
    @32
    efle
    syl2anc
    mpbid
    @7
    @87
    @83
    @2
    ccxp
    co
    #
    @86
    @7
    @105
    @87
    @109
    wceq
    @106
    vn
    @83
    @3
    @109
    cn
    @4
    @0
    @83
    @2
    ccxp
    oveq1
    @12
    @83
    @2
    ccxp
    ovex
    fvmpt
    syl
    @7
    @83
    @2
    @7
    @83
    @106
    nncnd
    @7
    @83
    @106
    nnne0d
    @45
    cxpefd
    eqtrd
    @7
    @8
    @9
    @33
    @13
    @46
    eqtrd
    3brtr4d
    wph
    @77
    wa
    #
    @79
    c2
    @76
    cexp
    co
    #
    @111
    @2
    ccxp
    co
    #
    cmul
    co
    #
    @78
    @111
    @111
    @4
    cfv
    #
    cmul
    co
    @110
    @49
    @76
    ccxp
    co
    #
    @111
    c1
    ccxp
    co
    #
    @112
    cmul
    co
    #
    @79
    @113
    @110
    c2
    @48
    @76
    cmul
    co
    #
    ccxp
    co
    #
    @111
    c1
    @2
    caddc
    co
    #
    ccxp
    co
    #
    @115
    @117
    @110
    @119
    c2
    @76
    @48
    cmul
    co
    #
    ccxp
    co
    c2
    @76
    ccxp
    co
    #
    @48
    ccxp
    co
    @121
    @110
    @118
    @122
    c2
    ccxp
    @110
    @48
    @76
    wph
    @48
    cc
    wcel
    @77
    wph
    @48
    @60
    recnd
    adantr
    #
    @110
    @76
    @77
    @76
    cr
    wcel
    wph
    @76
    nn0re
    adantl
    #
    recnd
    #
    mulcomd
    oveq2d
    @110
    c2
    @76
    @48
    @56
    @110
    2rp
    a1i
    #
    @125
    @124
    cxpmuld
    @110
    @123
    @111
    @48
    @120
    ccxp
    @110
    @75
    @77
    @123
    @111
    wceq
    2cn
    wph
    @77
    simpr
    #
    c2
    @76
    cxpexp
    sylancr
    @110
    @120
    @48
    @110
    c1
    cc
    wcel
    @70
    @120
    @48
    wceq
    ax-1cn
    wph
    @70
    @77
    @71
    adantr
    c1
    @1
    negsub
    sylancr
    eqcomd
    oveq12d
    3eqtrd
    @110
    c2
    @48
    @76
    @127
    wph
    @57
    @77
    @60
    adantr
    @126
    cxpmuld
    @110
    @111
    c1
    @2
    @110
    @111
    @77
    @111
    cn
    wcel
    #
    wph
    c2
    cn
    wcel
    #
    @77
    @129
    2nn
    c2
    @76
    nnexpcl
    #
    mpan
    adantl
    #
    nncnd
    #
    @110
    @111
    @132
    nnne0d
    @110
    1cnd
    wph
    @41
    @77
    @44
    adantr
    cxpaddd
    3eqtr3d
    wph
    @49
    cc
    wcel
    @77
    @115
    @79
    wceq
    @62
    @49
    @76
    cxpexp
    sylan
    @110
    @116
    @111
    @112
    cmul
    @110
    @111
    @133
    cxp1d
    oveq1d
    3eqtr3d
    @80
    @110
    @114
    @112
    @111
    cmul
    @110
    @129
    @114
    @112
    wceq
    @110
    @130
    @77
    @129
    2nn
    @128
    @131
    sylancr
    vn
    @111
    @3
    @112
    cn
    @4
    @0
    @111
    @2
    ccxp
    oveq1
    @12
    @111
    @2
    ccxp
    ovex
    fvmpt
    syl
    oveq2d
    3eqtr4d
    climcnds
    mpbird
    abscvgcvg
end
