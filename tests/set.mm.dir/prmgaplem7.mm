include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cprime.mm"
include "wnel.mm"
include "c1.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wrex.mm"
include "cmap.mm"
include "wf.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "wa.mm"
include "c3.mm"
include "cuz.mm"
include "simpr.mm"
include "elnnuz.mm"
include "sylib.mm"
include "1z.mm"
include "2z.mm"
include "eluzaddi.mm"
include "1p2e3.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "prmgaplem5.mm"
include "anim1i.mm"
include "ancomd.mm"
include "nnaddcl.mm"
include "prmgaplem6.mm"
include "reeanv.mm"
include "simprll.mm"
include "simprrl.mm"
include "wo.mm"
include "wi.mm"
include "cz.mm"
include "nnz.mm"
include "adantl.mm"
include "a1i.mm"
include "zaddcld.mm"
include "ad2antrr.mm"
include "fzospliti.mm"
include "ex.mm"
include "neleq1.mm"
include "rspcv.mm"
include "adantld.mm"
include "adantrd.mm"
include "a1d.mm"
include "nnzd.mm"
include "peano2zd.mm"
include "cgcd.mm"
include "cfz.mm"
include "cmin.mm"
include "wsbc.mm"
include "wb.mm"
include "adantr.mm"
include "fzshftral.mm"
include "syl3anc.mm"
include "cc.mm"
include "wceq.mm"
include "2cnd.mm"
include "nncn.mm"
include "addcom.mm"
include "syl2an.mm"
include "nncnd.mm"
include "oveq12d.mm"
include "csb.mm"
include "cvv.mm"
include "ovex.mm"
include "sbcbr2g.mm"
include "mp1i.mm"
include "csbov12g.mm"
include "csbov2g.mm"
include "csbvarg.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "bitrd.mm"
include "raleqbidv.mm"
include "fzval3.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "weq.mm"
include "oveq1.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "pncan3.mm"
include "oveq1d.mm"
include "zsubcl.mm"
include "syl2anr.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "cc0.mm"
include "elfzo2.mm"
include "cle.mm"
include "eluz2.mm"
include "2pos.mm"
include "cr.mm"
include "2re.mm"
include "nnre.mm"
include "ltaddpos.mm"
include "mpbid.mm"
include "ad2antll.mm"
include "readdcld.mm"
include "zre.mm"
include "ltletr.mm"
include "mpand.mm"
include "impancom.mm"
include "3adant1.mm"
include "sylbi.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "zred.mm"
include "posdif.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "nngt0.mm"
include "addgt0d.mm"
include "0red.mm"
include "ltsubpos.mm"
include "ncoprmlnprm.mm"
include "sylbid.mm"
include "syld.mm"
include "com23.mm"
include "mpid.mm"
include "imp.mm"
include "jaoi.mm"
include "com12.mm"
include "syldc.mm"
include "imp31.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "reximdva.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "mpdan.mm"

theorem prmgaplem7
  let wph: wff ph
  let vz: setvar z
  let vi: setvar i
  let cF: class F
  let cN: class N
  let vq: setvar q
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vj: setvar j
  assume prmgaplem7.n: |- ( ph -> N e. NN )
  assume prmgaplem7.f: |- ( ph -> F e. ( NN ^m NN ) )
  assume prmgaplem7.i: |- ( ph -> A. i e. ( 2 ... N ) 1 < ( ( ( F ` N ) + i ) gcd i ) )

  disjoint F p
  disjoint F q
  disjoint F z
  disjoint p q
  disjoint p z
  disjoint q z
  disjoint F i
  disjoint N p
  disjoint N q
  disjoint N z
  disjoint N i
  disjoint p ph
  disjoint ph q
  disjoint ph z
  disjoint F r
  disjoint F s
  disjoint p r
  disjoint p s
  disjoint q r
  disjoint q s
  disjoint r s
  disjoint r z
  disjoint s z
  disjoint F j
  disjoint i j
  disjoint N r
  disjoint N s
  disjoint N j
  disjoint j ph
  disjoint j p
  disjoint j q
  disjoint j z
  assert |- ( ph -> E. p e. Prime E. q e. Prime ( p < ( ( F ` N ) + 2 ) /\ ( ( F ` N ) + N ) < q /\ A. z e. ( ( p + 1 ) ..^ q ) z e/ Prime ) )

  proof
    wph
    cN
    cF
    cfv
    #
    cn
    wcel
    #
    vp
    cv
    #
    @0
    c2
    caddc
    co
    #
    clt
    wbr
    #
    @0
    cN
    caddc
    co
    #
    vq
    cv
    #
    clt
    wbr
    #
    vz
    cv
    #
    cprime
    wnel
    #
    vz
    @2
    c1
    caddc
    co
    #
    @6
    cfzo
    co
    #
    wral
    #
    w3a
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wph
    cn
    cn
    cN
    cF
    wph
    cF
    cn
    cn
    cmap
    co
    wcel
    cn
    cn
    cF
    wf
    prmgaplem7.f
    cF
    cn
    cn
    elmapi
    syl
    prmgaplem7.n
    ffvelrnd
    wph
    @1
    wa
    #
    @4
    vr
    cv
    #
    cprime
    wnel
    #
    vr
    @10
    @3
    cfzo
    co
    #
    wral
    #
    wa
    #
    vp
    cprime
    wrex
    #
    @7
    vs
    cv
    #
    cprime
    wnel
    #
    vs
    @5
    c1
    caddc
    co
    #
    @6
    cfzo
    co
    #
    wral
    #
    wa
    #
    vq
    cprime
    wrex
    #
    @15
    @16
    @3
    c3
    cuz
    cfv
    #
    wcel
    @22
    @16
    @3
    c1
    c2
    caddc
    co
    #
    cuz
    cfv
    #
    @30
    @16
    @0
    c1
    cuz
    cfv
    wcel
    #
    @3
    @32
    wcel
    @16
    @1
    @33
    wph
    @1
    simpr
    @0
    elnnuz
    sylib
    c2
    c1
    @0
    1z
    2z
    eluzaddi
    syl
    c3
    @31
    cuz
    @31
    c3
    1p2e3
    eqcomi
    fveq2i
    syl6eleqr
    vr
    @3
    vp
    prmgaplem5
    syl
    @16
    @5
    cn
    wcel
    #
    @29
    @16
    @1
    cN
    cn
    wcel
    #
    wa
    @34
    @16
    @35
    @1
    wph
    @35
    @1
    prmgaplem7.n
    anim1i
    ancomd
    @0
    cN
    nnaddcl
    syl
    #
    vs
    @5
    vq
    prmgaplem6
    syl
    @22
    @29
    wa
    @21
    @28
    wa
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    @16
    @15
    @21
    @28
    vp
    vq
    cprime
    cprime
    reeanv
    @16
    @38
    @14
    vp
    cprime
    @16
    @2
    cprime
    wcel
    #
    wa
    #
    @37
    @13
    vq
    cprime
    @40
    @6
    cprime
    wcel
    #
    wa
    #
    @37
    @13
    @42
    @37
    wa
    #
    @4
    @7
    @12
    @42
    @4
    @20
    @28
    simprll
    @42
    @21
    @7
    @27
    simprrl
    @43
    @9
    vz
    @11
    @42
    @37
    @8
    @11
    wcel
    #
    @9
    @42
    @44
    @37
    @9
    @42
    @44
    @8
    @19
    wcel
    #
    @8
    @3
    @6
    cfzo
    co
    wcel
    #
    wo
    #
    @37
    @9
    wi
    #
    @42
    @44
    @47
    @42
    @44
    wa
    #
    @44
    @3
    cz
    wcel
    #
    wa
    @47
    @49
    @50
    @44
    @42
    @50
    @44
    @16
    @50
    @39
    @41
    @16
    @0
    c2
    @1
    @0
    cz
    wcel
    #
    wph
    @0
    nnz
    adantl
    #
    c2
    cz
    wcel
    #
    @16
    2z
    a1i
    #
    zaddcld
    ad2antrr
    anim1i
    ancomd
    @8
    @10
    @6
    @3
    fzospliti
    syl
    ex
    @47
    @42
    @48
    @45
    @42
    @48
    wi
    #
    @46
    @45
    @48
    @42
    @45
    @21
    @9
    @28
    @45
    @20
    @9
    @4
    @18
    @9
    vr
    @8
    @19
    @17
    @8
    cprime
    neleq1
    rspcv
    adantld
    adantrd
    a1d
    @42
    @46
    @8
    @3
    @25
    cfzo
    co
    #
    wcel
    #
    @8
    @26
    wcel
    #
    wo
    #
    @48
    @42
    @46
    @59
    @42
    @46
    wa
    #
    @46
    @25
    cz
    wcel
    #
    wa
    @59
    @60
    @61
    @46
    @42
    @61
    @46
    @16
    @61
    @39
    @41
    @16
    @5
    @16
    @5
    @36
    nnzd
    #
    peano2zd
    ad2antrr
    anim1i
    ancomd
    @8
    @3
    @6
    @25
    fzospliti
    syl
    ex
    @59
    @42
    @48
    @57
    @55
    @58
    @57
    @42
    @48
    @57
    @42
    wa
    @9
    @37
    @42
    @57
    @9
    @16
    @57
    @9
    wi
    #
    @39
    @41
    wph
    @1
    @63
    wph
    @1
    c1
    @0
    vi
    cv
    #
    caddc
    co
    #
    @64
    cgcd
    co
    #
    clt
    wbr
    #
    vi
    c2
    cN
    cfz
    co
    wral
    #
    @63
    prmgaplem7.i
    wph
    @1
    @68
    @63
    wi
    @16
    @68
    @67
    vi
    vj
    cv
    #
    @0
    cmin
    co
    #
    wsbc
    #
    vj
    c2
    @0
    caddc
    co
    #
    cN
    @0
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    @63
    @16
    @53
    cN
    cz
    wcel
    #
    @51
    @68
    @75
    wb
    @54
    wph
    @76
    @1
    wph
    cN
    prmgaplem7.n
    nnzd
    adantr
    @52
    @67
    vi
    vj
    @0
    c2
    cN
    fzshftral
    syl3anc
    @16
    @75
    c1
    @0
    @70
    caddc
    co
    #
    @70
    cgcd
    co
    #
    clt
    wbr
    #
    vj
    @3
    @5
    cfz
    co
    #
    wral
    #
    @63
    @16
    @71
    @79
    vj
    @74
    @80
    @16
    @72
    @3
    @73
    @5
    cfz
    wph
    c2
    cc
    wcel
    @0
    cc
    wcel
    #
    @72
    @3
    wceq
    @1
    wph
    2cnd
    @0
    nncn
    #
    c2
    @0
    addcom
    syl2an
    wph
    cN
    cc
    wcel
    @82
    @73
    @5
    wceq
    @1
    wph
    cN
    prmgaplem7.n
    nncnd
    @83
    cN
    @0
    addcom
    syl2an
    oveq12d
    @16
    @71
    c1
    vi
    @70
    @66
    csb
    #
    clt
    wbr
    #
    @79
    @70
    cvv
    wcel
    #
    @71
    @85
    wb
    @16
    @69
    @0
    cmin
    ovex
    #
    vi
    @70
    c1
    @66
    clt
    cvv
    sbcbr2g
    mp1i
    @16
    @84
    @78
    c1
    clt
    @16
    @84
    vi
    @70
    @65
    csb
    #
    vi
    @70
    @64
    csb
    #
    cgcd
    co
    #
    @78
    @86
    @84
    @90
    wceq
    @16
    @87
    vi
    @70
    @65
    @64
    cgcd
    cvv
    csbov12g
    mp1i
    @16
    @88
    @77
    @89
    @70
    cgcd
    @16
    @88
    @0
    @89
    caddc
    co
    #
    @77
    @86
    @88
    @91
    wceq
    @16
    @87
    vi
    @70
    @0
    @64
    caddc
    cvv
    csbov2g
    mp1i
    @86
    @91
    @77
    wceq
    @16
    @87
    @86
    @89
    @70
    @0
    caddc
    vi
    @70
    cvv
    csbvarg
    #
    oveq2d
    mp1i
    eqtrd
    @86
    @89
    @70
    wceq
    @16
    @87
    @92
    mp1i
    oveq12d
    eqtrd
    breq2d
    bitrd
    raleqbidv
    @16
    @57
    @81
    @9
    @16
    @57
    @81
    @9
    wi
    @16
    @57
    wa
    #
    @81
    c1
    @0
    @8
    @0
    cmin
    co
    #
    caddc
    co
    #
    @94
    cgcd
    co
    #
    clt
    wbr
    #
    @9
    @93
    @8
    @80
    wcel
    #
    @81
    @97
    wi
    @16
    @57
    @98
    @16
    @56
    @80
    @8
    @16
    @5
    cz
    wcel
    #
    @56
    @80
    wceq
    @62
    @99
    @80
    @56
    @3
    @5
    fzval3
    eqcomd
    syl
    eleq2d
    biimpa
    @79
    @97
    vj
    @8
    @80
    vj
    vz
    weq
    #
    @78
    @96
    c1
    clt
    @100
    @77
    @95
    @70
    @94
    cgcd
    @100
    @70
    @94
    @0
    caddc
    @69
    @8
    @0
    cmin
    oveq1
    #
    oveq2d
    @101
    oveq12d
    breq2d
    rspcv
    syl
    @93
    @97
    c1
    @94
    @8
    cgcd
    co
    #
    clt
    wbr
    #
    @9
    @93
    @96
    @102
    c1
    clt
    @93
    @96
    @8
    @94
    cgcd
    co
    #
    @102
    @93
    @95
    @8
    @94
    cgcd
    @16
    @82
    @8
    cc
    wcel
    @95
    @8
    wceq
    @57
    @1
    @82
    wph
    @83
    adantl
    @57
    @8
    @8
    @3
    @25
    elfzoelz
    #
    zcnd
    @0
    @8
    pncan3
    syl2an
    oveq1d
    @93
    @8
    cz
    wcel
    #
    @94
    cz
    wcel
    #
    @104
    @102
    wceq
    @57
    @106
    @16
    @105
    adantl
    #
    @57
    @106
    @51
    @107
    @16
    @105
    @52
    @8
    @0
    zsubcl
    syl2anr
    #
    @8
    @94
    gcdcom
    syl2anc
    eqtrd
    breq2d
    @93
    @94
    cn
    wcel
    #
    @8
    cn
    wcel
    #
    @94
    @8
    clt
    wbr
    #
    @103
    @9
    wi
    @93
    @107
    cc0
    @94
    clt
    wbr
    #
    @110
    @109
    @93
    @0
    @8
    clt
    wbr
    #
    @113
    @57
    @16
    @114
    @57
    @8
    @3
    cuz
    cfv
    wcel
    #
    @61
    @8
    @25
    clt
    wbr
    #
    w3a
    #
    @16
    @114
    wi
    #
    @8
    @3
    @25
    elfzo2
    #
    @115
    @61
    @118
    @116
    @115
    @50
    @106
    @3
    @8
    cle
    wbr
    #
    w3a
    #
    @118
    @3
    @8
    eluz2
    #
    @106
    @120
    @118
    @50
    @106
    @16
    @120
    @114
    @106
    @16
    wa
    #
    @0
    @3
    clt
    wbr
    #
    @120
    @114
    @123
    cc0
    c2
    clt
    wbr
    #
    @124
    @125
    @123
    2pos
    a1i
    #
    @106
    c2
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @125
    @124
    wb
    @16
    @127
    @106
    2re
    a1i
    @1
    @128
    wph
    @0
    nnre
    #
    adantl
    #
    c2
    @0
    ltaddpos
    syl2an
    mpbid
    @123
    @128
    @3
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @124
    @120
    wa
    @114
    wi
    @1
    @128
    @106
    wph
    @129
    ad2antll
    #
    @1
    @131
    @106
    wph
    @1
    @0
    c2
    @129
    @127
    @1
    2re
    a1i
    readdcld
    ad2antll
    #
    @106
    @132
    @16
    @8
    zre
    adantr
    #
    @0
    @3
    @8
    ltletr
    syl3anc
    mpand
    impancom
    3adant1
    sylbi
    3ad2ant1
    sylbi
    impcom
    @16
    @128
    @132
    @114
    @113
    wb
    @57
    @130
    @57
    @8
    @105
    zred
    #
    @0
    @8
    posdif
    syl2an
    mpbid
    @94
    elnnz
    sylanbrc
    @93
    @106
    cc0
    @8
    clt
    wbr
    #
    @111
    @108
    @57
    @16
    @137
    @57
    @117
    @16
    @137
    wi
    #
    @119
    @115
    @61
    @138
    @116
    @115
    @121
    @138
    @122
    @106
    @120
    @138
    @50
    @106
    @16
    @120
    @137
    @123
    cc0
    @3
    clt
    wbr
    #
    @120
    @137
    @123
    @0
    c2
    @133
    @127
    @123
    2re
    a1i
    @1
    cc0
    @0
    clt
    wbr
    #
    @106
    wph
    @0
    nngt0
    #
    ad2antll
    @126
    addgt0d
    @123
    cc0
    cr
    wcel
    @131
    @132
    @139
    @120
    wa
    @137
    wi
    @123
    0red
    @134
    @135
    cc0
    @3
    @8
    ltletr
    syl3anc
    mpand
    impancom
    3adant1
    sylbi
    3ad2ant1
    sylbi
    impcom
    @8
    elnnz
    sylanbrc
    @93
    @140
    @112
    @16
    @140
    @57
    @1
    @140
    wph
    @141
    adantl
    adantr
    @16
    @128
    @132
    @140
    @112
    wb
    @57
    @130
    @136
    @0
    @8
    ltsubpos
    syl2an
    mpbid
    @94
    @8
    ncoprmlnprm
    syl3anc
    sylbid
    syld
    ex
    com23
    sylbid
    sylbid
    ex
    mpid
    imp
    ad2antrr
    impcom
    a1d
    ex
    @58
    @48
    @42
    @58
    @28
    @9
    @21
    @58
    @27
    @9
    @7
    @24
    @9
    vs
    @8
    @26
    @23
    @8
    cprime
    neleq1
    rspcv
    adantld
    adantld
    a1d
    jaoi
    com12
    syldc
    jaoi
    com12
    syld
    com23
    imp31
    ralrimiva
    3jca
    ex
    reximdva
    reximdva
    syl5bir
    mp2and
    mpdan
end
