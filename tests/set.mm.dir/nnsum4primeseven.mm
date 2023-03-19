include "c5.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbow.mm"
include "wcel.mm"
include "wi.mm"
include "codd.mm"
include "wral.mm"
include "c9.mm"
include "cuz.mm"
include "cfv.mm"
include "ceven.mm"
include "wa.mm"
include "c1.mm"
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
include "evengpop3.mm"
include "imp.mm"
include "cmin.mm"
include "c6.mm"
include "simplll.mm"
include "cz.mm"
include "6nn.mm"
include "nnzi.mm"
include "a1i.mm"
include "3z.mm"
include "6p3e9.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eluzsub.mm"
include "syl3anc.mm"
include "adantr.mm"
include "ad3antlr.mm"
include "3odd.mm"
include "anim1i.mm"
include "adantl.mm"
include "ancomd.mm"
include "emoo.mm"
include "syl.mm"
include "nnsum4primesodd.mm"
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
include "w3a.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "3cn.mm"
include "3pm3.2i.mm"
include "3p1e4.mm"
include "subadd2.mm"
include "mpbiri.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "mtbir.mm"
include "pm3.2i.mm"
include "3prm.mm"
include "fsnunf.mm"
include "fzval3.mm"
include "cle.mm"
include "1z.mm"
include "1re.mm"
include "4re.mm"
include "1lt4.mm"
include "ltleii.mm"
include "eluz2.mm"
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
include "sumeq2dv.mm"
include "eqeq2d.mm"
include "wo.mm"
include "elun.mm"
include "velsn.mm"
include "orbi2i.mm"
include "3bitri.mm"
include "wne.mm"
include "elfz2.mm"
include "cr.mm"
include "3re.mm"
include "3lt4.mm"
include "ltnle.mm"
include "mpbii.mm"
include "breq1.mm"
include "eqcoms.mm"
include "mtbiri.mm"
include "necon2ad.mm"
include "adantld.mm"
include "3ad2ant3.mm"
include "sylbi.mm"
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
include "rexlimdva.mm"

theorem nnsum4primeseven
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
  assert |- ( A. m e. Odd ( 5 < m -> m e. GoldbachOddW ) -> ( ( N e. ( ZZ>= ` 9 ) /\ N e. Even ) -> E. f e. ( Prime ^m ( 1 ... 4 ) ) N = sum_ k e. ( 1 ... 4 ) ( f ` k ) ) )

  proof
    c5
    vm
    cv
    #
    clt
    wbr
    @0
    cgbow
    wcel
    wi
    vm
    codd
    wral
    #
    cN
    c9
    cuz
    cfv
    #
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
    vo
    cgbow
    wrex
    #
    @13
    @1
    @5
    @17
    vm
    vo
    cN
    evengpop3
    imp
    @14
    @16
    @13
    vo
    cgbow
    @14
    @15
    cgbow
    wcel
    #
    wa
    #
    @16
    @13
    @19
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
    @22
    cmap
    co
    #
    wrex
    #
    @13
    @20
    @1
    @21
    c6
    cuz
    cfv
    wcel
    #
    @21
    codd
    wcel
    #
    @28
    @1
    @5
    @18
    @16
    simplll
    @5
    @29
    @1
    @18
    @16
    @3
    @29
    @4
    @3
    c6
    cz
    wcel
    #
    c3
    cz
    wcel
    #
    cN
    c6
    c3
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @29
    @31
    @3
    c6
    6nn
    nnzi
    a1i
    @32
    @3
    3z
    a1i
    @3
    @35
    @2
    @34
    cN
    c9
    @33
    cuz
    @33
    c9
    6p3e9
    eqcomi
    fveq2i
    eleq2i
    biimpi
    c3
    c6
    cN
    eluzsub
    syl3anc
    adantr
    ad3antlr
    @20
    @4
    c3
    codd
    wcel
    #
    wa
    #
    @30
    @19
    @37
    @16
    @14
    @37
    @18
    @14
    @36
    @4
    @5
    @36
    @4
    wa
    @1
    @3
    @36
    @4
    @36
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
    @29
    @30
    wa
    @28
    vg
    vk
    vm
    @21
    nnsum4primesodd
    imp
    syl12anc
    @5
    @28
    @13
    wi
    #
    @1
    @18
    @16
    @3
    @38
    @4
    @3
    @26
    @13
    vg
    @27
    @22
    cprime
    @23
    wf
    #
    @3
    @26
    @13
    wi
    #
    @23
    @27
    wcel
    @3
    @39
    @40
    @3
    @39
    wa
    #
    @26
    @13
    @41
    @26
    wa
    #
    @11
    cN
    @6
    @7
    @23
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
    @43
    @12
    @41
    @43
    @12
    wcel
    #
    @26
    @41
    @47
    @6
    cprime
    @43
    wf
    #
    @41
    @22
    c4
    csn
    #
    cun
    #
    cprime
    @43
    wf
    #
    @48
    @41
    @39
    c4
    cz
    wcel
    #
    c4
    @22
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
    @51
    @3
    @39
    simpr
    @55
    @41
    @52
    @54
    4z
    @53
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
    @22
    @57
    c4
    @57
    @22
    @57
    c1
    c4
    c1
    cmin
    co
    #
    cfz
    co
    #
    @22
    @52
    @57
    @59
    wceq
    4z
    c1
    c4
    fzoval
    ax-mp
    @58
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
    w3a
    #
    @58
    c3
    wceq
    #
    @60
    @61
    @62
    4cn
    ax-1cn
    3cn
    3pm3.2i
    @63
    @64
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
    ax-mp
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
    @56
    @41
    3prm
    a1i
    @22
    cprime
    @23
    cz
    c4
    c3
    fsnunf
    syl3anc
    @6
    @50
    cprime
    @43
    @6
    c1
    c4
    c1
    caddc
    co
    cfzo
    co
    #
    @57
    @49
    cun
    #
    @50
    @52
    @6
    @68
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
    @68
    @69
    wceq
    @70
    c1
    cz
    wcel
    #
    @52
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
    @57
    @22
    @49
    @66
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
    @47
    @48
    wb
    @41
    @74
    @75
    prmex
    c1
    c4
    cfz
    ovex
    pm3.2i
    cprime
    @6
    @43
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    adantr
    @8
    @43
    wceq
    #
    @11
    @46
    wb
    @42
    @76
    @10
    @45
    cN
    @76
    @6
    @9
    @44
    vk
    @76
    @9
    @44
    wceq
    @7
    @6
    wcel
    #
    @7
    @8
    @43
    fveq1
    adantr
    sumeq2dv
    eqeq2d
    adantl
    @42
    @45
    @59
    @44
    vk
    csu
    #
    c4
    @43
    cfv
    #
    caddc
    co
    #
    @21
    @79
    caddc
    co
    #
    cN
    @41
    @45
    @80
    wceq
    @26
    @41
    @44
    @79
    vk
    c1
    c4
    @70
    @41
    @72
    a1i
    @41
    @77
    @44
    cc
    wcel
    #
    @77
    @7
    @22
    wcel
    #
    @7
    c4
    wceq
    #
    wo
    #
    @41
    @82
    @77
    @7
    @50
    wcel
    @83
    @7
    @49
    wcel
    #
    wo
    @85
    @6
    @50
    @7
    @73
    eleq2i
    @7
    @22
    @49
    elun
    @86
    @84
    @83
    vk
    c4
    velsn
    orbi2i
    3bitri
    @85
    @41
    @82
    @83
    @41
    @82
    wi
    @84
    @83
    @39
    @82
    @3
    @83
    @39
    @82
    @83
    @39
    wa
    #
    @44
    @24
    cc
    @87
    c4
    @7
    wne
    #
    @44
    @24
    wceq
    #
    @83
    @88
    @39
    @83
    @71
    @32
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
    @88
    @7
    c1
    c3
    elfz2
    @91
    @94
    @88
    @90
    @71
    @94
    @88
    wi
    @32
    @90
    @93
    @88
    @92
    @90
    @93
    c4
    @7
    c4
    @7
    wceq
    #
    @93
    wn
    wi
    @90
    @95
    @93
    c4
    c3
    cle
    wbr
    #
    c3
    cr
    wcel
    #
    c4
    cr
    wcel
    #
    wa
    #
    @96
    wn
    #
    @97
    @98
    3re
    4re
    pm3.2i
    @99
    c3
    c4
    clt
    wbr
    @100
    3lt4
    c3
    c4
    ltnle
    mpbii
    ax-mp
    @93
    @96
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
    @23
    c4
    c3
    @7
    fvunsn
    #
    syl
    @87
    @24
    @87
    @24
    cprime
    wcel
    #
    @24
    cz
    wcel
    @39
    @83
    @103
    @22
    cprime
    @7
    @23
    ffvelrn
    ancoms
    @24
    prmz
    syl
    zcnd
    eqeltrd
    ex
    adantld
    @84
    @41
    @82
    @84
    @41
    wa
    @44
    c3
    cc
    @84
    @41
    @44
    @79
    c3
    @7
    c4
    @43
    fveq2
    #
    @39
    @79
    c3
    wceq
    #
    @3
    @39
    @52
    @32
    c4
    @23
    cdm
    #
    wcel
    #
    wn
    #
    @105
    @52
    @39
    4z
    a1i
    @32
    @39
    3z
    a1i
    @39
    @106
    @22
    wceq
    #
    @108
    @22
    cprime
    @23
    fdm
    @109
    @107
    @53
    @67
    @106
    @22
    c4
    eleq2
    mtbiri
    syl
    #
    @23
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
    @104
    fsumm1
    adantr
    @42
    @78
    @21
    @79
    caddc
    @42
    @21
    @78
    @41
    @26
    @21
    @78
    wceq
    @41
    @25
    @78
    @21
    @41
    @22
    @59
    @24
    @44
    vk
    @22
    @59
    wceq
    @41
    c3
    @58
    c1
    cfz
    @58
    c3
    @65
    eqcomi
    oveq2i
    a1i
    @41
    @83
    wa
    #
    @44
    @24
    @112
    @88
    @89
    @83
    @88
    @41
    @101
    adantl
    @102
    syl
    eqcomd
    sumeq12dv
    eqeq2d
    biimpa
    eqcomd
    oveq1d
    @41
    @81
    cN
    wceq
    @26
    @41
    @81
    @21
    c3
    caddc
    co
    #
    cN
    @41
    @79
    c3
    @21
    caddc
    @41
    @52
    @32
    @108
    @105
    @52
    @41
    4z
    a1i
    @32
    @41
    3z
    a1i
    @39
    @108
    @3
    @110
    adantl
    @111
    syl3anc
    oveq2d
    @3
    @113
    cN
    wceq
    @39
    @3
    cN
    c3
    c9
    cN
    eluzelcn
    @62
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
    @23
    cprime
    @22
    elmapi
    syl11
    rexlimdv
    adantr
    ad3antlr
    mpd
    ex
    rexlimdva
    mpd
    ex
end
