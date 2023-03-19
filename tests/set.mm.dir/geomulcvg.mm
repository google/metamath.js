include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wceq.mm"
include "cuz.mm"
include "csn.mm"
include "cxp.mm"
include "cn0.mm"
include "cmpt.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cn.mm"
include "wo.mm"
include "elnn0.mm"
include "simpr.mm"
include "oveq1d.mm"
include "0exp.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "nncn.mm"
include "adantl.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "simplll.mm"
include "0nn0.mm"
include "syl6eqel.mm"
include "expcld.mm"
include "mul02d.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "fconstmpt.mm"
include "nn0uz.mm"
include "xpeq1i.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "seqeq3d.mm"
include "cz.mm"
include "0z.mm"
include "serclim0.mm"
include "ax-mp.mm"
include "syl6eqbr.mm"
include "seqex.mm"
include "c0ex.mm"
include "breldm.mm"
include "syl.mm"
include "wne.mm"
include "c2.mm"
include "cdiv.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "1red.mm"
include "abscl.mm"
include "adantr.mm"
include "peano2re.mm"
include "rehalfcld.mm"
include "crp.mm"
include "absrpcl.mm"
include "adantlr.mm"
include "rerpdivcld.mm"
include "recnd.mm"
include "mulid2d.mm"
include "wb.mm"
include "1re.mm"
include "avglt1.mm"
include "sylancl.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "ltmuldivd.mm"
include "expmulnbnd.mm"
include "syl3anc.mm"
include "eluznn0.mm"
include "nn0cn.mm"
include "ad2antrr.mm"
include "rpne0d.mm"
include "expdivd.mm"
include "breq12d.mm"
include "nn0re.mm"
include "reexpcl.mm"
include "sylan.mm"
include "nn0z.mm"
include "rpgt0d.mm"
include "expgt0.mm"
include "ltmuldiv.mm"
include "syl112anc.mm"
include "bitr4d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "wi.mm"
include "simprl.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "reexpcld.mm"
include "eqeltrd.mm"
include "id.mm"
include "oveq12d.mm"
include "simpll.mm"
include "expcl.mm"
include "mulcld.mm"
include "cmin.mm"
include "0red.mm"
include "cle.mm"
include "absge0.mm"
include "lelttrd.mm"
include "ltled.mm"
include "absidd.mm"
include "avglt2.mm"
include "geolim.mm"
include "nn0red.mm"
include "abscld.mm"
include "remulcld.mm"
include "syldan.mm"
include "simprr.mm"
include "rspccva.mm"
include "nn0cnd.mm"
include "absmuld.mm"
include "nn0ge0d.mm"
include "absexpd.mm"
include "3brtr4d.mm"
include "fveq2d.mm"
include "cvgcmpce.mm"
include "expr.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "pm2.61dane.mm"

theorem geomulcvg
  let cA: class A
  let vk: setvar k
  let cF: class F
  let vm: setvar m
  let vn: setvar n
  assume geomulcvg.1: |- F = ( k e. NN0 |-> ( k x. ( A ^ k ) ) )

  disjoint A k
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint A m
  disjoint A n
  disjoint F m
  disjoint F n
  assert |- ( ( A e. CC /\ ( abs ` A ) < 1 ) -> seq 0 ( + , F ) e. dom ~~> )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wa
    #
    caddc
    cF
    cc0
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    cA
    cc0
    @3
    cA
    cc0
    wceq
    #
    wa
    #
    @4
    cc0
    cli
    wbr
    @6
    @8
    @4
    caddc
    cc0
    cuz
    cfv
    #
    cc0
    csn
    #
    cxp
    #
    cc0
    cseq
    #
    cc0
    cli
    @8
    cF
    @11
    caddc
    cc0
    @8
    cF
    vk
    cn0
    cc0
    cmpt
    #
    @11
    @8
    cF
    vk
    cn0
    vk
    cv
    #
    cA
    @14
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    @13
    geomulcvg.1
    @8
    vk
    cn0
    @16
    cc0
    @14
    cn0
    wcel
    #
    @8
    @14
    cn
    wcel
    #
    @14
    cc0
    wceq
    #
    wo
    @16
    cc0
    wceq
    #
    @14
    elnn0
    @8
    @18
    @20
    @19
    @8
    @18
    wa
    #
    @16
    @14
    cc0
    cmul
    co
    cc0
    @21
    @15
    cc0
    @14
    cmul
    @8
    @18
    @15
    cc0
    @14
    cexp
    co
    cc0
    @8
    cA
    cc0
    @14
    cexp
    @3
    @7
    simpr
    oveq1d
    @14
    0exp
    sylan9eq
    oveq2d
    @21
    @14
    @18
    @14
    cc
    wcel
    #
    @8
    @14
    nncn
    adantl
    mul01d
    eqtrd
    @8
    @19
    wa
    #
    @16
    cc0
    @15
    cmul
    co
    cc0
    @23
    @14
    cc0
    @15
    cmul
    @8
    @19
    simpr
    #
    oveq1d
    @23
    @15
    @23
    cA
    @14
    @0
    @2
    @7
    @19
    simplll
    @23
    @14
    cc0
    cn0
    @24
    0nn0
    syl6eqel
    expcld
    mul02d
    eqtrd
    jaodan
    sylan2b
    mpteq2dva
    syl5eq
    cn0
    @10
    cxp
    @13
    @11
    vk
    cn0
    cc0
    fconstmpt
    cn0
    @9
    @10
    nn0uz
    xpeq1i
    eqtr3i
    syl6eq
    seqeq3d
    cc0
    cz
    wcel
    @12
    cc0
    cli
    wbr
    0z
    cc0
    serclim0
    ax-mp
    syl6eqbr
    @4
    cc0
    cli
    caddc
    cF
    cc0
    seqex
    c0ex
    breldm
    syl
    @3
    cA
    cc0
    wne
    #
    wa
    #
    c1
    @14
    cmul
    co
    #
    @1
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @1
    cdiv
    co
    #
    @14
    cexp
    co
    #
    clt
    wbr
    #
    vk
    vn
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vn
    cn0
    wrex
    #
    @6
    @26
    c1
    cr
    wcel
    #
    @30
    cr
    wcel
    c1
    @30
    clt
    wbr
    #
    @36
    @26
    1red
    #
    @26
    @29
    @1
    @3
    @29
    cr
    wcel
    #
    @25
    @3
    @28
    @3
    @1
    cr
    wcel
    #
    @28
    cr
    wcel
    @0
    @41
    @2
    cA
    abscl
    adantr
    #
    @1
    peano2re
    syl
    rehalfcld
    #
    adantr
    #
    @0
    @25
    @1
    crp
    wcel
    #
    @2
    cA
    absrpcl
    adantlr
    #
    rerpdivcld
    @26
    c1
    @1
    cmul
    co
    #
    @29
    clt
    wbr
    #
    @38
    @3
    @48
    @25
    @3
    @47
    @1
    @29
    clt
    @3
    @1
    @3
    @1
    @42
    recnd
    #
    mulid2d
    @3
    @2
    @1
    @29
    clt
    wbr
    #
    @0
    @2
    simpr
    #
    @3
    @41
    @37
    @2
    @50
    wb
    @42
    1re
    @1
    c1
    avglt1
    sylancl
    mpbid
    #
    eqbrtrd
    adantr
    @26
    c1
    @29
    @1
    @39
    @44
    @46
    ltmuldivd
    mpbid
    c1
    @30
    vn
    vk
    expmulnbnd
    syl3anc
    @26
    @35
    @6
    vn
    cn0
    @26
    @33
    cn0
    wcel
    #
    wa
    #
    @35
    @14
    @1
    @14
    cexp
    co
    #
    cmul
    co
    #
    @29
    @14
    cexp
    co
    #
    clt
    wbr
    #
    vk
    @34
    wral
    #
    @6
    @54
    @32
    @58
    vk
    @34
    @26
    @53
    @14
    @34
    wcel
    #
    @32
    @58
    wb
    #
    @53
    @60
    wa
    @26
    @17
    @61
    @14
    @33
    eluznn0
    @26
    @17
    wa
    #
    @32
    @14
    @57
    @55
    cdiv
    co
    #
    clt
    wbr
    #
    @58
    @62
    @27
    @14
    @31
    @63
    clt
    @62
    @14
    @17
    @22
    @26
    @14
    nn0cn
    adantl
    mulid2d
    @62
    @29
    @1
    @14
    @3
    @29
    cc
    wcel
    @25
    @17
    @3
    @29
    @43
    recnd
    #
    ad2antrr
    @3
    @1
    cc
    wcel
    @25
    @17
    @49
    ad2antrr
    @62
    @1
    @26
    @45
    @17
    @46
    adantr
    #
    rpne0d
    @26
    @17
    simpr
    expdivd
    breq12d
    @62
    @14
    cr
    wcel
    #
    @57
    cr
    wcel
    #
    @55
    cr
    wcel
    #
    cc0
    @55
    clt
    wbr
    #
    @58
    @64
    wb
    @17
    @67
    @26
    @14
    nn0re
    adantl
    @26
    @40
    @17
    @68
    @44
    @29
    @14
    reexpcl
    sylan
    @26
    @41
    @17
    @69
    @3
    @41
    @25
    @42
    adantr
    #
    @1
    @14
    reexpcl
    sylan
    @62
    @41
    @14
    cz
    wcel
    #
    cc0
    @1
    clt
    wbr
    @70
    @26
    @41
    @17
    @71
    adantr
    @17
    @72
    @26
    @14
    nn0z
    adantl
    @62
    @1
    @66
    rpgt0d
    @1
    @14
    expgt0
    syl3anc
    @14
    @57
    @55
    ltmuldiv
    syl112anc
    bitr4d
    sylan2
    anassrs
    ralbidva
    @3
    @53
    @59
    @6
    wi
    @25
    @3
    @53
    @59
    @6
    @3
    @53
    @59
    wa
    #
    wa
    #
    c1
    vm
    vk
    cn0
    @57
    cmpt
    #
    cF
    cc0
    @33
    cn0
    nn0uz
    @3
    @53
    @59
    simprl
    #
    @74
    vm
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @77
    @75
    cfv
    #
    @29
    @77
    cexp
    co
    #
    cr
    @78
    @80
    @81
    wceq
    #
    @74
    vk
    @77
    @57
    @81
    cn0
    @75
    @14
    @77
    @29
    cexp
    oveq2
    #
    @75
    eqid
    #
    @29
    @77
    cexp
    ovex
    fvmpt
    #
    adantl
    @79
    @29
    @77
    @3
    @40
    @73
    @78
    @43
    ad2antrr
    @74
    @78
    simpr
    reexpcld
    #
    eqeltrd
    @79
    @77
    cF
    cfv
    #
    @77
    cA
    @77
    cexp
    co
    #
    cmul
    co
    #
    cc
    @78
    @87
    @89
    wceq
    #
    @74
    vk
    @77
    @16
    @89
    cn0
    cF
    @14
    @77
    wceq
    #
    @14
    @77
    @15
    @88
    cmul
    @91
    id
    #
    @14
    @77
    cA
    cexp
    oveq2
    oveq12d
    geomulcvg.1
    @77
    @88
    cmul
    ovex
    fvmpt
    #
    adantl
    @79
    @77
    @88
    @78
    @77
    cc
    wcel
    @74
    @77
    nn0cn
    adantl
    @74
    @0
    @78
    @88
    cc
    wcel
    @0
    @2
    @73
    simpll
    cA
    @77
    expcl
    sylan
    mulcld
    eqeltrd
    @3
    caddc
    @75
    cc0
    cseq
    #
    @5
    wcel
    #
    @73
    @3
    @94
    c1
    c1
    @29
    cmin
    co
    #
    cdiv
    co
    #
    cli
    wbr
    @95
    @3
    @29
    vn
    @75
    @65
    @3
    @29
    cabs
    cfv
    @29
    c1
    clt
    @3
    @29
    @43
    @3
    cc0
    @29
    @3
    0red
    #
    @43
    @3
    cc0
    @1
    @29
    @98
    @42
    @43
    @0
    cc0
    @1
    cle
    wbr
    @2
    cA
    absge0
    adantr
    @52
    lelttrd
    ltled
    absidd
    @3
    @2
    @29
    c1
    clt
    wbr
    #
    @51
    @3
    @41
    @37
    @2
    @99
    wb
    @42
    1re
    @1
    c1
    avglt2
    sylancl
    mpbid
    eqbrtrd
    @53
    @33
    @75
    cfv
    @29
    @33
    cexp
    co
    #
    wceq
    @3
    vk
    @33
    @57
    @100
    cn0
    @75
    @14
    @33
    @29
    cexp
    oveq2
    @84
    @29
    @33
    cexp
    ovex
    fvmpt
    adantl
    geolim
    @94
    @97
    cli
    caddc
    @75
    cc0
    seqex
    c1
    @96
    cdiv
    ovex
    breldm
    syl
    adantr
    @74
    1red
    @74
    @77
    @34
    wcel
    #
    wa
    #
    @89
    cabs
    cfv
    #
    c1
    @81
    cmul
    co
    #
    @87
    cabs
    cfv
    c1
    @80
    cmul
    co
    cle
    @102
    @77
    @1
    @77
    cexp
    co
    #
    cmul
    co
    #
    @81
    @103
    @104
    cle
    @102
    @106
    @81
    @102
    @77
    @105
    @102
    @77
    @74
    @53
    @101
    @78
    @76
    @77
    @33
    eluznn0
    sylan
    #
    nn0red
    #
    @102
    @1
    @77
    @102
    cA
    @0
    @2
    @73
    @101
    simplll
    #
    abscld
    @107
    reexpcld
    remulcld
    @74
    @101
    @78
    @81
    cr
    wcel
    @107
    @86
    syldan
    #
    @74
    @59
    @101
    @106
    @81
    clt
    wbr
    #
    @3
    @53
    @59
    simprr
    @58
    @111
    vk
    @77
    @34
    @91
    @56
    @106
    @57
    @81
    clt
    @91
    @14
    @77
    @55
    @105
    cmul
    @92
    @14
    @77
    @1
    cexp
    oveq2
    oveq12d
    @83
    breq12d
    rspccva
    sylan
    ltled
    @102
    @103
    @77
    cabs
    cfv
    #
    @88
    cabs
    cfv
    #
    cmul
    co
    @106
    @102
    @77
    @88
    @102
    @77
    @107
    nn0cnd
    @102
    cA
    @77
    @109
    @107
    expcld
    absmuld
    @102
    @112
    @77
    @113
    @105
    cmul
    @102
    @77
    @108
    @102
    @77
    @107
    nn0ge0d
    absidd
    @102
    cA
    @77
    @109
    @107
    absexpd
    oveq12d
    eqtrd
    @102
    @81
    @102
    @81
    @110
    recnd
    mulid2d
    3brtr4d
    @102
    @87
    @89
    cabs
    @102
    @78
    @90
    @107
    @93
    syl
    fveq2d
    @102
    @80
    @81
    c1
    cmul
    @102
    @78
    @82
    @107
    @85
    syl
    oveq2d
    3brtr4d
    cvgcmpce
    expr
    adantlr
    sylbid
    rexlimdva
    mpd
    pm2.61dane
end
