include "c7.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbo.mm"
include "wcel.mm"
include "wi.mm"
include "codd.mm"
include "wral.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "cuz.mm"
include "cfv.mm"
include "ceven.mm"
include "wa.mm"
include "c4.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "wceq.mm"
include "cprime.mm"
include "cmap.mm"
include "wrex.mm"
include "c3.mm"
include "caddc.mm"
include "cmin.mm"
include "c8.mm"
include "simplll.mm"
include "cz.mm"
include "8nn.mm"
include "nnzi.mm"
include "a1i.mm"
include "3z.mm"
include "cle.mm"
include "zaddcld.mm"
include "eluzelz.mm"
include "w3a.mm"
include "eluz2.mm"
include "8p4e12.mm"
include "breq1i.mm"
include "1nn0.mm"
include "2nn.mm"
include "1lt2.mm"
include "declt.mm"
include "8p3e11.mm"
include "3brtr4i.mm"
include "cr.mm"
include "8re.mm"
include "3re.mm"
include "readdcld.mm"
include "4re.mm"
include "zre.mm"
include "ltleletr.mm"
include "syl3anc.mm"
include "mpani.mm"
include "syl5bir.mm"
include "imp.mm"
include "3adant1.mm"
include "sylbi.mm"
include "syl3anbrc.mm"
include "eluzsub.mm"
include "adantr.mm"
include "ad3antlr.mm"
include "3odd.mm"
include "anim1i.mm"
include "adantl.mm"
include "ancomd.mm"
include "emoo.mm"
include "syl.mm"
include "nnsum4primesoddALTV.mm"
include "syl12anc.mm"
include "wf.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wn.mm"
include "simpr.mm"
include "4z.mm"
include "cfzo.mm"
include "fzonel.mm"
include "fzoval.mm"
include "ax-mp.mm"
include "cc.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "3cn.mm"
include "3p1e4.mm"
include "subadd2.mm"
include "mpbiri.mm"
include "mp3an.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "mtbir.mm"
include "pm3.2i.mm"
include "3prm.mm"
include "fsnunf.mm"
include "fzval3.mm"
include "1z.mm"
include "1re.mm"
include "1lt4.mm"
include "ltleii.mm"
include "mpbir3an.mm"
include "fzosplitsn.mm"
include "uneq1i.mm"
include "3eqtri.mm"
include "feq2i.mm"
include "sylibr.mm"
include "cvv.mm"
include "wb.mm"
include "prmex.mm"
include "ovex.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "fveq1.mm"
include "sumeq2sdv.mm"
include "eqeq2d.mm"
include "wo.mm"
include "elun.mm"
include "velsn.mm"
include "orbi2i.mm"
include "3bitri.mm"
include "wne.mm"
include "elfz2.mm"
include "3lt4.mm"
include "ltnle.mm"
include "mpbii.mm"
include "breq1.mm"
include "eqcoms.mm"
include "mtbiri.mm"
include "necon2ad.mm"
include "adantld.mm"
include "3ad2ant3.mm"
include "fvunsn.mm"
include "ffvelrn.mm"
include "ancoms.mm"
include "prmz.mm"
include "zcnd.mm"
include "eqeltrd.mm"
include "ex.mm"
include "fveq2.mm"
include "cdm.mm"
include "fdm.mm"
include "eleq2.mm"
include "fsnunfv.mm"
include "sylan9eq.mm"
include "syl6eqel.mm"
include "jaoi.mm"
include "com12.mm"
include "syl5bi.mm"
include "fsumm1.mm"
include "eqcomd.mm"
include "sumeq12dv.mm"
include "biimpa.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eluzelcn.mm"
include "npcand.mm"
include "eqtrd.mm"
include "3eqtrrd.mm"
include "rspcedvd.mm"
include "expcom.mm"
include "elmapi.mm"
include "syl11.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "evengpoap3.mm"
include "r19.29a.mm"

theorem nnsum4primesevenALTV
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let cN: class N
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vo: setvar o
  let vg: setvar g
  let vx: setvar x

  disjoint N f
  disjoint N k
  disjoint N m
  disjoint f k
  disjoint f m
  disjoint k m
  disjoint N p
  disjoint N q
  disjoint N r
  disjoint f p
  disjoint f q
  disjoint f r
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint N o
  disjoint N g
  disjoint f g
  disjoint f o
  disjoint g k
  disjoint g m
  disjoint g o
  disjoint k o
  disjoint m o
  disjoint k x
  assert |- ( A. m e. Odd ( 7 < m -> m e. GoldbachOdd ) -> ( ( N e. ( ZZ>= ` ; 1 2 ) /\ N e. Even ) -> E. f e. ( Prime ^m ( 1 ... 4 ) ) N = sum_ k e. ( 1 ... 4 ) ( f ` k ) ) )

  proof
    c7
    vm
    cv
    #
    clt
    wbr
    @0
    cgbo
    wcel
    wi
    vm
    codd
    wral
    #
    cN
    c1
    c2
    cdc
    #
    cuz
    cfv
    wcel
    #
    cN
    ceven
    wcel
    #
    wa
    #
    cN
    c1
    c4
    cfz
    co
    #
    vk
    cv
    #
    vf
    cv
    #
    cfv
    #
    vk
    csu
    #
    wceq
    #
    vf
    cprime
    @6
    cmap
    co
    #
    wrex
    #
    @1
    @5
    wa
    #
    cN
    vo
    cv
    #
    c3
    caddc
    co
    wceq
    #
    @13
    vo
    cgbo
    @14
    @15
    cgbo
    wcel
    #
    wa
    #
    @16
    wa
    #
    cN
    c3
    cmin
    co
    #
    c1
    c3
    cfz
    co
    #
    @7
    vg
    cv
    #
    cfv
    #
    vk
    csu
    #
    wceq
    #
    vg
    cprime
    @21
    cmap
    co
    #
    wrex
    #
    @13
    @19
    @1
    @20
    c8
    cuz
    cfv
    wcel
    #
    @20
    codd
    wcel
    #
    @27
    @1
    @5
    @17
    @16
    simplll
    @5
    @28
    @1
    @17
    @16
    @3
    @28
    @4
    @3
    c8
    cz
    wcel
    #
    c3
    cz
    wcel
    #
    cN
    c8
    c3
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    @28
    @30
    @3
    c8
    8nn
    nnzi
    a1i
    #
    @31
    @3
    3z
    a1i
    #
    @3
    @32
    cz
    wcel
    cN
    cz
    wcel
    #
    @32
    cN
    cle
    wbr
    #
    @33
    @3
    c8
    c3
    @34
    @35
    zaddcld
    @2
    cN
    eluzelz
    @3
    @2
    cz
    wcel
    #
    @36
    @2
    cN
    cle
    wbr
    #
    w3a
    @37
    @2
    cN
    eluz2
    @36
    @39
    @37
    @38
    @36
    @39
    @37
    @39
    c8
    c4
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @36
    @37
    @40
    @2
    cN
    cle
    8p4e12
    breq1i
    @36
    @32
    @40
    clt
    wbr
    #
    @41
    @37
    c1
    c1
    cdc
    @2
    @32
    @40
    clt
    c1
    c1
    c2
    1nn0
    1nn0
    2nn
    1lt2
    declt
    8p3e11
    8p4e12
    3brtr4i
    @36
    @32
    cr
    wcel
    @40
    cr
    wcel
    cN
    cr
    wcel
    @42
    @41
    wa
    @37
    wi
    @36
    c8
    c3
    c8
    cr
    wcel
    @36
    8re
    a1i
    #
    c3
    cr
    wcel
    #
    @36
    3re
    a1i
    readdcld
    @36
    c8
    c4
    @43
    c4
    cr
    wcel
    #
    @36
    4re
    a1i
    readdcld
    cN
    zre
    @32
    @40
    cN
    ltleletr
    syl3anc
    mpani
    syl5bir
    imp
    3adant1
    sylbi
    @32
    cN
    eluz2
    syl3anbrc
    c3
    c8
    cN
    eluzsub
    syl3anc
    adantr
    ad3antlr
    @19
    @4
    c3
    codd
    wcel
    #
    wa
    #
    @29
    @18
    @47
    @16
    @14
    @47
    @17
    @14
    @46
    @4
    @5
    @46
    @4
    wa
    @1
    @3
    @46
    @4
    @46
    @3
    3odd
    a1i
    anim1i
    adantl
    ancomd
    adantr
    adantr
    cN
    c3
    emoo
    syl
    @1
    @28
    @29
    wa
    @27
    vg
    vk
    vm
    @20
    nnsum4primesoddALTV
    imp
    syl12anc
    @5
    @27
    @13
    wi
    #
    @1
    @17
    @16
    @3
    @48
    @4
    @3
    @25
    @13
    vg
    @26
    @21
    cprime
    @22
    wf
    #
    @3
    @25
    @13
    wi
    #
    @22
    @26
    wcel
    @3
    @49
    @50
    @3
    @49
    wa
    #
    @25
    @13
    @51
    @25
    wa
    #
    @11
    cN
    @6
    @7
    @22
    c4
    c3
    cop
    csn
    cun
    #
    cfv
    #
    vk
    csu
    #
    wceq
    #
    vf
    @53
    @12
    @51
    @53
    @12
    wcel
    #
    @25
    @51
    @57
    @6
    cprime
    @53
    wf
    #
    @51
    @21
    c4
    csn
    #
    cun
    #
    cprime
    @53
    wf
    #
    @58
    @51
    @49
    c4
    cz
    wcel
    #
    c4
    @21
    wcel
    #
    wn
    #
    wa
    #
    c3
    cprime
    wcel
    #
    @61
    @3
    @49
    simpr
    @65
    @51
    @62
    @64
    4z
    @63
    c4
    c1
    c4
    cfzo
    co
    #
    wcel
    c1
    c4
    fzonel
    @21
    @67
    c4
    @67
    @21
    @67
    c1
    c4
    c1
    cmin
    co
    #
    cfz
    co
    #
    @21
    @62
    @67
    @69
    wceq
    4z
    c1
    c4
    fzoval
    ax-mp
    @68
    c3
    c1
    cfz
    c4
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    c3
    cc
    wcel
    #
    @68
    c3
    wceq
    #
    4cn
    ax-1cn
    3cn
    @70
    @71
    @72
    w3a
    @73
    c3
    c1
    caddc
    co
    c4
    wceq
    3p1e4
    c4
    c1
    c3
    subadd2
    mpbiri
    mp3an
    #
    oveq2i
    eqtri
    #
    eqcomi
    eleq2i
    mtbir
    #
    pm3.2i
    a1i
    @66
    @51
    3prm
    a1i
    @21
    cprime
    @22
    cz
    c4
    c3
    fsnunf
    syl3anc
    @6
    @60
    cprime
    @53
    @6
    c1
    c4
    c1
    caddc
    co
    cfzo
    co
    #
    @67
    @59
    cun
    #
    @60
    @62
    @6
    @77
    wceq
    4z
    c1
    c4
    fzval3
    ax-mp
    c4
    c1
    cuz
    cfv
    wcel
    #
    @77
    @78
    wceq
    @79
    c1
    cz
    wcel
    #
    @62
    c1
    c4
    cle
    wbr
    1z
    4z
    c1
    c4
    1re
    4re
    1lt4
    ltleii
    c1
    c4
    eluz2
    mpbir3an
    #
    c1
    c4
    fzosplitsn
    ax-mp
    @67
    @21
    @59
    @75
    uneq1i
    3eqtri
    #
    feq2i
    sylibr
    cprime
    cvv
    wcel
    #
    @6
    cvv
    wcel
    #
    wa
    @57
    @58
    wb
    @51
    @83
    @84
    prmex
    c1
    c4
    cfz
    ovex
    pm3.2i
    cprime
    @6
    @53
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    adantr
    @8
    @53
    wceq
    #
    @11
    @56
    wb
    @52
    @85
    @10
    @55
    cN
    @85
    @6
    @9
    @54
    vk
    @7
    @8
    @53
    fveq1
    sumeq2sdv
    eqeq2d
    adantl
    @52
    @55
    @69
    @54
    vk
    csu
    #
    c4
    @53
    cfv
    #
    caddc
    co
    #
    @20
    @87
    caddc
    co
    #
    cN
    @51
    @55
    @88
    wceq
    @25
    @51
    @54
    @87
    vk
    c1
    c4
    @79
    @51
    @81
    a1i
    @51
    @7
    @6
    wcel
    #
    @54
    cc
    wcel
    #
    @90
    @7
    @21
    wcel
    #
    @7
    c4
    wceq
    #
    wo
    #
    @51
    @91
    @90
    @7
    @60
    wcel
    @92
    @7
    @59
    wcel
    #
    wo
    @94
    @6
    @60
    @7
    @82
    eleq2i
    @7
    @21
    @59
    elun
    @95
    @93
    @92
    vk
    c4
    velsn
    orbi2i
    3bitri
    @94
    @51
    @91
    @92
    @51
    @91
    wi
    @93
    @92
    @49
    @91
    @3
    @92
    @49
    @91
    @92
    @49
    wa
    #
    @54
    @23
    cc
    @96
    c4
    @7
    wne
    #
    @54
    @23
    wceq
    #
    @92
    @97
    @49
    @92
    @80
    @31
    @7
    cz
    wcel
    #
    w3a
    #
    c1
    @7
    cle
    wbr
    #
    @7
    c3
    cle
    wbr
    #
    wa
    #
    wa
    @97
    @7
    c1
    c3
    elfz2
    @100
    @103
    @97
    @99
    @80
    @103
    @97
    wi
    @31
    @99
    @102
    @97
    @101
    @99
    @102
    c4
    @7
    c4
    @7
    wceq
    #
    @102
    wn
    wi
    @99
    @104
    @102
    c4
    c3
    cle
    wbr
    #
    @44
    @45
    wa
    #
    @105
    wn
    #
    @44
    @45
    3re
    4re
    pm3.2i
    @106
    c3
    c4
    clt
    wbr
    @107
    3lt4
    c3
    c4
    ltnle
    mpbii
    ax-mp
    @102
    @105
    wb
    @7
    c4
    @7
    c4
    c3
    cle
    breq1
    eqcoms
    mtbiri
    a1i
    necon2ad
    adantld
    3ad2ant3
    imp
    sylbi
    #
    adantr
    @22
    c4
    c3
    @7
    fvunsn
    #
    syl
    @96
    @23
    @96
    @23
    cprime
    wcel
    #
    @23
    cz
    wcel
    @49
    @92
    @110
    @21
    cprime
    @7
    @22
    ffvelrn
    ancoms
    @23
    prmz
    syl
    zcnd
    eqeltrd
    ex
    adantld
    @93
    @51
    @91
    @93
    @51
    wa
    @54
    c3
    cc
    @93
    @51
    @54
    @87
    c3
    @7
    c4
    @53
    fveq2
    #
    @49
    @87
    c3
    wceq
    #
    @3
    @49
    @62
    @31
    c4
    @22
    cdm
    #
    wcel
    #
    wn
    #
    @112
    @62
    @49
    4z
    a1i
    @31
    @49
    3z
    a1i
    @49
    @113
    @21
    wceq
    #
    @115
    @21
    cprime
    @22
    fdm
    @116
    @114
    @63
    @76
    @113
    @21
    c4
    eleq2
    mtbiri
    syl
    #
    @22
    cz
    cz
    c4
    c3
    fsnunfv
    #
    syl3anc
    adantl
    sylan9eq
    3cn
    syl6eqel
    ex
    jaoi
    com12
    syl5bi
    imp
    @111
    fsumm1
    adantr
    @52
    @86
    @20
    @87
    caddc
    @52
    @20
    @86
    @51
    @25
    @20
    @86
    wceq
    @51
    @24
    @86
    @20
    @51
    @21
    @69
    @23
    @54
    vk
    @21
    @69
    wceq
    @51
    c3
    @68
    c1
    cfz
    @68
    c3
    @74
    eqcomi
    oveq2i
    a1i
    @51
    @92
    wa
    #
    @54
    @23
    @119
    @97
    @98
    @92
    @97
    @51
    @108
    adantl
    @109
    syl
    eqcomd
    sumeq12dv
    eqeq2d
    biimpa
    eqcomd
    oveq1d
    @51
    @89
    cN
    wceq
    @25
    @51
    @89
    @20
    c3
    caddc
    co
    #
    cN
    @51
    @87
    c3
    @20
    caddc
    @51
    @62
    @31
    @115
    @112
    @62
    @51
    4z
    a1i
    @31
    @51
    3z
    a1i
    @49
    @115
    @3
    @117
    adantl
    @118
    syl3anc
    oveq2d
    @3
    @120
    cN
    wceq
    @49
    @3
    cN
    c3
    @2
    cN
    eluzelcn
    @72
    @3
    3cn
    a1i
    npcand
    adantr
    eqtrd
    adantr
    3eqtrrd
    rspcedvd
    ex
    expcom
    @22
    cprime
    @21
    elmapi
    syl11
    rexlimdv
    adantr
    ad3antlr
    mpd
    @1
    @5
    @16
    vo
    cgbo
    wrex
    vm
    vo
    cN
    evengpoap3
    imp
    r19.29a
    ex
end
