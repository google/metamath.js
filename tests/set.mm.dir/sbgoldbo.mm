include "c4.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbe.mm"
include "wcel.mm"
include "wi.mm"
include "ceven.mm"
include "wral.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "nfra1.mm"
include "c6.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cun.mm"
include "wb.mm"
include "cz.mm"
include "cle.mm"
include "3z.mm"
include "6nn.mm"
include "nnzi.mm"
include "3re.mm"
include "6re.mm"
include "3lt6.mm"
include "ltleii.mm"
include "eluz2.mm"
include "mpbir3an.mm"
include "uzsplit.mm"
include "eleq2d.mm"
include "ax-mp.mm"
include "wo.mm"
include "elun.mm"
include "csn.mm"
include "c5.mm"
include "cfzo.mm"
include "6m1e5.mm"
include "oveq2i.mm"
include "5nn.mm"
include "5re.mm"
include "3lt5.mm"
include "fzopredsuc.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "elsni.mm"
include "cprime.mm"
include "1ex.mm"
include "snid.mm"
include "orci.mm"
include "mpbir.mm"
include "eleqtrri.mm"
include "a1i.mm"
include "wa.mm"
include "simpl.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "adantl.mm"
include "eqeq12d.mm"
include "2rexbidv.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "c2.mm"
include "df-3.mm"
include "df-2.mm"
include "oveq1i.mm"
include "syl6reqr.mm"
include "rspcedeq2vd.mm"
include "rspcedvd.mm"
include "syl.mm"
include "3p1e4.mm"
include "df-5.mm"
include "oveq12i.mm"
include "4z.mm"
include "fzval3.mm"
include "eqtr4i.mm"
include "fzsn.mm"
include "bitri.mm"
include "2prm.mm"
include "olci.mm"
include "df-4.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "sylbi.mm"
include "jaoi.mm"
include "3prm.mm"
include "a1d.mm"
include "sbgoldbm.mm"
include "rspa.mm"
include "wss.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "rexss.mm"
include "simpr.mm"
include "reximi.mm"
include "ex.mm"
include "com12.mm"
include "syl5bi.mm"
include "ralrimi.mm"

theorem sbgoldbo
  let cP: class P
  let vn: setvar n
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume sbgoldbo.p: |- P = ( { 1 } u. Prime )

  disjoint P p
  disjoint P q
  disjoint P r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint k x
  assert |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven ) -> A. n e. ( ZZ>= ` 3 ) E. p e. P E. q e. P E. r e. P n = ( ( p + q ) + r ) )

  proof
    c4
    vn
    cv
    #
    clt
    wbr
    @0
    cgbe
    wcel
    wi
    #
    vn
    ceven
    wral
    #
    @0
    vp
    cv
    #
    vq
    cv
    #
    caddc
    co
    #
    vr
    cv
    #
    caddc
    co
    #
    wceq
    #
    vr
    cP
    wrex
    #
    vq
    cP
    wrex
    #
    vp
    cP
    wrex
    #
    vn
    c3
    cuz
    cfv
    #
    @1
    vn
    ceven
    nfra1
    @0
    @12
    wcel
    #
    @0
    c3
    c6
    c1
    cmin
    co
    #
    cfz
    co
    #
    c6
    cuz
    cfv
    #
    cun
    #
    wcel
    #
    @2
    @11
    c6
    @12
    wcel
    #
    @13
    @18
    wb
    @19
    c3
    cz
    wcel
    #
    c6
    cz
    wcel
    c3
    c6
    cle
    wbr
    3z
    c6
    6nn
    nnzi
    c3
    c6
    3re
    6re
    3lt6
    ltleii
    c3
    c6
    eluz2
    mpbir3an
    @19
    @12
    @17
    @0
    c3
    c6
    uzsplit
    eleq2d
    ax-mp
    @18
    @2
    @11
    @18
    @0
    @15
    wcel
    #
    @0
    @16
    wcel
    #
    wo
    @2
    @11
    wi
    #
    @0
    @15
    @16
    elun
    @21
    @23
    @22
    @21
    @0
    c3
    csn
    #
    c3
    c1
    caddc
    co
    #
    c5
    cfzo
    co
    #
    cun
    #
    c5
    csn
    #
    cun
    #
    wcel
    #
    @23
    @15
    @29
    @0
    @15
    c3
    c5
    cfz
    co
    #
    @29
    @14
    c5
    c3
    cfz
    6m1e5
    oveq2i
    c5
    @12
    wcel
    #
    @31
    @29
    wceq
    @32
    @20
    c5
    cz
    wcel
    c3
    c5
    cle
    wbr
    3z
    c5
    5nn
    nnzi
    c3
    c5
    3re
    5re
    3lt5
    ltleii
    c3
    c5
    eluz2
    mpbir3an
    c3
    c5
    fzopredsuc
    ax-mp
    eqtri
    eleq2i
    @30
    @11
    @2
    @30
    @0
    @27
    wcel
    #
    @0
    @28
    wcel
    #
    wo
    @11
    @0
    @27
    @28
    elun
    @33
    @11
    @34
    @33
    @0
    @24
    wcel
    #
    @0
    @26
    wcel
    #
    wo
    @11
    @0
    @24
    @26
    elun
    @35
    @11
    @36
    @35
    @0
    c3
    wceq
    #
    @11
    @0
    c3
    elsni
    @37
    @10
    c3
    c1
    @4
    caddc
    co
    #
    @6
    caddc
    co
    #
    wceq
    #
    vr
    cP
    wrex
    #
    vq
    cP
    wrex
    vp
    c1
    cP
    c1
    cP
    wcel
    #
    @37
    c1
    c1
    csn
    #
    cprime
    cun
    #
    cP
    c1
    @44
    wcel
    c1
    @43
    wcel
    #
    c1
    cprime
    wcel
    #
    wo
    @45
    @46
    c1
    1ex
    snid
    orci
    c1
    @43
    cprime
    elun
    mpbir
    sbgoldbo.p
    eleqtrri
    #
    a1i
    #
    @37
    @3
    c1
    wceq
    #
    wa
    #
    @8
    @40
    vq
    vr
    cP
    cP
    @50
    @0
    c3
    @7
    @39
    @37
    @49
    simpl
    @49
    @7
    @39
    wceq
    @37
    @49
    @5
    @38
    @6
    caddc
    @3
    c1
    @4
    caddc
    oveq1
    oveq1d
    adantl
    eqeq12d
    2rexbidv
    @37
    @41
    c3
    c1
    c1
    caddc
    co
    #
    @6
    caddc
    co
    #
    wceq
    #
    vr
    cP
    wrex
    #
    vq
    c1
    cP
    @48
    @4
    c1
    wceq
    #
    @41
    @54
    wb
    @37
    @55
    @40
    @53
    vr
    cP
    @55
    @39
    @52
    c3
    @55
    @38
    @51
    @6
    caddc
    @4
    c1
    c1
    caddc
    oveq2
    oveq1d
    eqeq2d
    rexbidv
    adantl
    @37
    vr
    c1
    cP
    c3
    @52
    @48
    @6
    c1
    wceq
    #
    @53
    @37
    @56
    @52
    @51
    c1
    caddc
    co
    #
    c3
    @6
    c1
    @51
    caddc
    oveq2
    c3
    c2
    c1
    caddc
    co
    #
    @57
    df-3
    c2
    @51
    c1
    caddc
    df-2
    oveq1i
    eqtri
    syl6reqr
    adantl
    rspcedeq2vd
    rspcedvd
    rspcedvd
    syl
    @36
    @0
    c4
    csn
    #
    wcel
    #
    @11
    @36
    @0
    c4
    c4
    cfz
    co
    #
    wcel
    @60
    @26
    @61
    @0
    @26
    c4
    c4
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @61
    @25
    c4
    c5
    @62
    cfzo
    3p1e4
    df-5
    oveq12i
    c4
    cz
    wcel
    #
    @61
    @63
    wceq
    4z
    c4
    c4
    fzval3
    ax-mp
    eqtr4i
    eleq2i
    @61
    @59
    @0
    @64
    @61
    @59
    wceq
    4z
    c4
    fzsn
    ax-mp
    eleq2i
    bitri
    @60
    @0
    c4
    wceq
    #
    @11
    @0
    c4
    elsni
    @65
    @10
    @0
    c2
    @4
    caddc
    co
    #
    @6
    caddc
    co
    #
    wceq
    #
    vr
    cP
    wrex
    #
    vq
    cP
    wrex
    #
    vp
    c2
    cP
    c2
    cP
    wcel
    @65
    c2
    @44
    cP
    c2
    @44
    wcel
    c2
    @43
    wcel
    #
    c2
    cprime
    wcel
    #
    wo
    @72
    @71
    2prm
    olci
    c2
    @43
    cprime
    elun
    mpbir
    sbgoldbo.p
    eleqtrri
    a1i
    @3
    c2
    wceq
    #
    @10
    @70
    wb
    @65
    @73
    @8
    @68
    vq
    vr
    cP
    cP
    @73
    @7
    @67
    @0
    @73
    @5
    @66
    @6
    caddc
    @3
    c2
    @4
    caddc
    oveq1
    oveq1d
    eqeq2d
    2rexbidv
    adantl
    @65
    @69
    @0
    @58
    @6
    caddc
    co
    #
    wceq
    #
    vr
    cP
    wrex
    #
    vq
    c1
    cP
    @42
    @65
    @47
    a1i
    #
    @55
    @69
    @76
    wb
    @65
    @55
    @68
    @75
    vr
    cP
    @55
    @67
    @74
    @0
    @55
    @66
    @58
    @6
    caddc
    @4
    c1
    c2
    caddc
    oveq2
    oveq1d
    eqeq2d
    rexbidv
    adantl
    @65
    vr
    c1
    cP
    @0
    @74
    @77
    @65
    @56
    wa
    #
    @0
    c4
    @74
    @65
    @56
    simpl
    @78
    c4
    @58
    c1
    caddc
    co
    #
    @74
    c4
    @79
    wceq
    @78
    c4
    @25
    @79
    df-4
    c3
    @58
    c1
    caddc
    df-3
    oveq1i
    eqtri
    a1i
    @56
    @79
    @74
    wceq
    @65
    @56
    @74
    @79
    @6
    c1
    @58
    caddc
    oveq2
    eqcomd
    adantl
    eqtrd
    eqtrd
    rspcedeq2vd
    rspcedvd
    rspcedvd
    syl
    sylbi
    jaoi
    sylbi
    @34
    @0
    c5
    wceq
    #
    @11
    @0
    c5
    elsni
    @80
    @10
    @0
    c3
    @4
    caddc
    co
    #
    @6
    caddc
    co
    #
    wceq
    #
    vr
    cP
    wrex
    #
    vq
    cP
    wrex
    #
    vp
    c3
    cP
    c3
    cP
    wcel
    @80
    c3
    @44
    cP
    c3
    @44
    wcel
    c3
    @43
    wcel
    #
    c3
    cprime
    wcel
    #
    wo
    @87
    @86
    3prm
    olci
    c3
    @43
    cprime
    elun
    mpbir
    sbgoldbo.p
    eleqtrri
    a1i
    @3
    c3
    wceq
    #
    @10
    @85
    wb
    @80
    @88
    @8
    @83
    vq
    vr
    cP
    cP
    @88
    @7
    @82
    @0
    @88
    @5
    @81
    @6
    caddc
    @3
    c3
    @4
    caddc
    oveq1
    oveq1d
    eqeq2d
    2rexbidv
    adantl
    @80
    @84
    @0
    @25
    @6
    caddc
    co
    #
    wceq
    #
    vr
    cP
    wrex
    #
    vq
    c1
    cP
    @42
    @80
    @47
    a1i
    #
    @55
    @84
    @91
    wb
    @80
    @55
    @83
    @90
    vr
    cP
    @55
    @82
    @89
    @0
    @55
    @81
    @25
    @6
    caddc
    @4
    c1
    c3
    caddc
    oveq2
    oveq1d
    eqeq2d
    rexbidv
    adantl
    @80
    vr
    c1
    cP
    @0
    @89
    @92
    @80
    @56
    wa
    @0
    c5
    @89
    @80
    @56
    simpl
    @56
    c5
    @89
    wceq
    @80
    @56
    @89
    @25
    c1
    caddc
    co
    #
    c5
    @6
    c1
    @25
    caddc
    oveq2
    c5
    @62
    @93
    df-5
    c4
    @25
    c1
    caddc
    df-4
    oveq1i
    eqtri
    syl6reqr
    adantl
    eqtrd
    rspcedeq2vd
    rspcedvd
    rspcedvd
    syl
    jaoi
    sylbi
    a1d
    sylbi
    @2
    @22
    @11
    @2
    @8
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    vn
    @16
    wral
    #
    @22
    @11
    wi
    vn
    vr
    vq
    vp
    sbgoldbm
    @97
    @22
    @11
    @97
    @22
    wa
    @96
    @11
    @96
    vn
    @16
    rspa
    @96
    @3
    cprime
    wcel
    #
    @95
    wa
    #
    vp
    cP
    wrex
    #
    @11
    cprime
    cP
    wss
    #
    @96
    @100
    wb
    cprime
    @44
    cP
    cprime
    @43
    ssun2
    sbgoldbo.p
    sseqtr4i
    #
    @95
    vp
    cprime
    cP
    rexss
    ax-mp
    @99
    @10
    vp
    cP
    @95
    @10
    @98
    @95
    @4
    cprime
    wcel
    #
    @94
    wa
    #
    vq
    cP
    wrex
    #
    @10
    @101
    @95
    @105
    wb
    @102
    @94
    vq
    cprime
    cP
    rexss
    ax-mp
    @104
    @9
    vq
    cP
    @94
    @9
    @103
    @94
    @6
    cprime
    wcel
    #
    @8
    wa
    #
    vr
    cP
    wrex
    #
    @9
    @101
    @94
    @108
    wb
    @102
    @8
    vr
    cprime
    cP
    rexss
    ax-mp
    @107
    @8
    vr
    cP
    @106
    @8
    simpr
    reximi
    sylbi
    adantl
    reximi
    sylbi
    adantl
    reximi
    sylbi
    syl
    ex
    syl
    com12
    jaoi
    sylbi
    com12
    syl5bi
    ralrimi
end
