include "crn.mm"
include "cfv.mm"
include "cbs.mm"
include "casa.mm"
include "wcel.mm"
include "wss.mm"
include "psrassa.mm"
include "eqid.mm"
include "mplbasss.mm"
include "a1i.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "wral.mm"
include "ccrg.mm"
include "crg.mm"
include "crngring.mm"
include "syl.mm"
include "mvrf.mm"
include "ffnd.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "mvrcl.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "frn.mm"
include "aspss.mm"
include "syl3anc.mm"
include "csubrg.mm"
include "clss.mm"
include "wceq.mm"
include "mplsubrg.mm"
include "mpllss.mm"
include "aspid.mm"
include "sseqtrd.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt.mm"
include "cvsca.mm"
include "cgsu.mm"
include "mplcoe1.mm"
include "cvv.mm"
include "cabl.mm"
include "mplring.mm"
include "syl2anc.mm"
include "ringabl.mm"
include "ovex.mm"
include "rabex.mm"
include "csubg.mm"
include "syl6ss.mm"
include "aspsubrg.mm"
include "wb.mm"
include "mplval2.mm"
include "subsubrg.mm"
include "mpbir2and.mm"
include "subrgsubg.mm"
include "clmod.mm"
include "csca.mm"
include "mpllmod.mm"
include "ad2antrr.mm"
include "asplss.mm"
include "psrlmod.mm"
include "lsslss.mm"
include "mplelf.mm"
include "ffvelrnda.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "cmgp.mm"
include "cmg.mm"
include "mplcoe2.mm"
include "ringidval.mm"
include "ccmn.mm"
include "mplcrng.mm"
include "crngmgp.mm"
include "csubmnd.mm"
include "subrgsubm.mm"
include "simplll.mm"
include "psrbag.mm"
include "biimpa.mm"
include "simpld.mm"
include "aspssid.mm"
include "ad3antrrr.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "sseldd.mm"
include "cmulr.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "subrgmcl.mm"
include "syl3an1.mm"
include "subrg1cl.mm"
include "mulgnn0subcl.mm"
include "fmptd.mm"
include "wfun.mm"
include "csupp.mm"
include "cfsupp.mm"
include "wbr.mm"
include "mptexg.mm"
include "funmpt.mm"
include "fvexd.mm"
include "simprd.mm"
include "cdif.mm"
include "cc0.mm"
include "elrabi.mm"
include "elmapi.mm"
include "adantl.mm"
include "frnnn0supp.mm"
include "eqimss.mm"
include "c0ex.mm"
include "suppssr.mm"
include "sylanl2.mm"
include "oveq1d.mm"
include "eldifi.mm"
include "mulg0.mm"
include "eqtrd.mm"
include "suppss2.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "gsumsubmcl.mm"
include "eqeltrd.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "w3a.mm"
include "mptrabex.mm"
include "fvex.mm"
include "3pm3.2i.mm"
include "mplelbas.mm"
include "simprbi.mm"
include "fsuppimpd.mm"
include "ssid.mm"
include "mplmon.mm"
include "lmod0vs.mm"
include "sylan2.mm"
include "syl12anc.mm"
include "gsumsubgcl.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem mplbas2
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  let vf: setvar f
  assume mplbas2.p: |- P = ( I mPoly R )
  assume mplbas2.s: |- S = ( I mPwSer R )
  assume mplbas2.v: |- V = ( I mVar R )
  assume mplbas2.a: |- A = ( AlgSpan ` S )
  assume mplbas2.i: |- ( ph -> I e. W )
  assume mplbas2.r: |- ( ph -> R e. CRing )


  assert |- ( ph -> ( A ` ran V ) = ( Base ` P ) )

  proof
    wph
    cV
    crn
    #
    cA
    cfv
    #
    cP
    cbs
    cfv
    #
    wph
    @1
    @2
    cA
    cfv
    #
    @2
    wph
    cS
    casa
    wcel
    #
    @2
    cS
    cbs
    cfv
    #
    wss
    #
    @0
    @2
    wss
    #
    @1
    @3
    wss
    wph
    cR
    cS
    cI
    cW
    mplbas2.s
    mplbas2.i
    mplbas2.r
    psrassa
    #
    @6
    wph
    @5
    cP
    cR
    cS
    @2
    cI
    mplbas2.p
    mplbas2.s
    @2
    eqid
    #
    @5
    eqid
    #
    mplbasss
    #
    a1i
    wph
    cI
    @2
    cV
    wf
    #
    @7
    wph
    cV
    cI
    wfn
    #
    vx
    cv
    #
    cV
    cfv
    @2
    wcel
    #
    vx
    cI
    wral
    @12
    wph
    cI
    @5
    cV
    wph
    @5
    cR
    cS
    cI
    cV
    cW
    mplbas2.s
    mplbas2.v
    @10
    mplbas2.i
    wph
    cR
    ccrg
    wcel
    #
    cR
    crg
    wcel
    #
    mplbas2.r
    cR
    crngring
    syl
    #
    mvrf
    ffnd
    #
    wph
    @15
    vx
    cI
    wph
    @14
    cI
    wcel
    #
    wa
    @2
    cP
    cR
    cI
    cV
    cW
    @14
    mplbas2.p
    mplbas2.v
    @9
    wph
    cI
    cW
    wcel
    #
    @20
    mplbas2.i
    adantr
    wph
    @17
    @20
    @18
    adantr
    wph
    @20
    simpr
    mvrcl
    ralrimiva
    vx
    cI
    @2
    cV
    ffnfv
    sylanbrc
    cI
    @2
    cV
    frn
    syl
    #
    cA
    @2
    @0
    @5
    cS
    mplbas2.a
    @10
    aspss
    syl3anc
    wph
    @4
    @2
    cS
    csubrg
    cfv
    #
    wcel
    #
    @2
    cS
    clss
    cfv
    #
    wcel
    #
    @3
    @2
    wceq
    @8
    wph
    cP
    cR
    cS
    @2
    cI
    cW
    mplbas2.s
    mplbas2.p
    @9
    mplbas2.i
    @18
    mplsubrg
    #
    wph
    cP
    cR
    cS
    @2
    cI
    cW
    mplbas2.s
    mplbas2.p
    @9
    mplbas2.i
    @18
    mpllss
    #
    cA
    @2
    @25
    @5
    cS
    mplbas2.a
    @10
    @25
    eqid
    #
    aspid
    syl3anc
    sseqtrd
    #
    wph
    vx
    @2
    @1
    wph
    @14
    @2
    wcel
    #
    @14
    @1
    wcel
    wph
    @31
    wa
    #
    @14
    cP
    vk
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vf
    cn0
    cI
    cmap
    co
    #
    crab
    #
    vk
    cv
    #
    @14
    cfv
    #
    vy
    @35
    vy
    cv
    @36
    wceq
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    cmpt
    #
    cP
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    @1
    @32
    vy
    @2
    @35
    cP
    cR
    @41
    @38
    vf
    vk
    cI
    cW
    @14
    @39
    mplbas2.p
    @35
    eqid
    #
    @39
    eqid
    #
    @38
    eqid
    #
    wph
    @21
    @31
    mplbas2.i
    adantr
    #
    @9
    @41
    eqid
    #
    wph
    @17
    @31
    @18
    adantr
    #
    wph
    @31
    simpr
    #
    mplcoe1
    @32
    @35
    @1
    @43
    cP
    cvv
    cP
    c0g
    cfv
    #
    @51
    eqid
    #
    wph
    cP
    cabl
    wcel
    #
    @31
    wph
    cP
    crg
    wcel
    #
    @53
    wph
    @21
    @17
    @54
    mplbas2.i
    @18
    cP
    cR
    cI
    cW
    mplbas2.p
    mplring
    syl2anc
    cP
    ringabl
    syl
    adantr
    @35
    cvv
    wcel
    @32
    @33
    vf
    @34
    cn0
    cI
    cmap
    ovex
    #
    rabex
    a1i
    #
    wph
    @1
    cP
    csubg
    cfv
    wcel
    #
    @31
    wph
    @1
    cP
    csubrg
    cfv
    wcel
    #
    @57
    wph
    @58
    @1
    @23
    wcel
    #
    @1
    @2
    wss
    #
    wph
    @4
    @0
    @5
    wss
    #
    @59
    @8
    wph
    @0
    @2
    @5
    @22
    @11
    syl6ss
    #
    cA
    @0
    @5
    cS
    mplbas2.a
    @10
    aspsubrg
    syl2anc
    @30
    wph
    @24
    @58
    @59
    @60
    wa
    wb
    @27
    @2
    @1
    cS
    cP
    cP
    cR
    cS
    @2
    cI
    mplbas2.p
    mplbas2.s
    @9
    mplval2
    #
    subsubrg
    syl
    mpbir2and
    #
    @1
    cP
    subrgsubg
    syl
    adantr
    @32
    vk
    @35
    @42
    @1
    @43
    @32
    @36
    @35
    wcel
    #
    wa
    #
    cP
    clmod
    wcel
    #
    @1
    cP
    clss
    cfv
    #
    wcel
    #
    @37
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @40
    @1
    wcel
    @42
    @1
    wcel
    wph
    @67
    @31
    @65
    wph
    @21
    @17
    @67
    mplbas2.i
    @18
    cP
    cR
    cI
    cW
    mplbas2.p
    mpllmod
    syl2anc
    ad2antrr
    #
    wph
    @69
    @31
    @65
    wph
    @69
    @1
    @25
    wcel
    #
    @60
    wph
    @4
    @61
    @73
    @8
    @62
    cA
    @0
    @25
    @5
    cS
    mplbas2.a
    @10
    @29
    asplss
    syl2anc
    @30
    wph
    cS
    clmod
    wcel
    @26
    @69
    @73
    @60
    wa
    wb
    wph
    cR
    cS
    cI
    cW
    mplbas2.s
    mplbas2.i
    @18
    psrlmod
    @28
    @25
    @68
    @2
    @1
    cS
    cP
    @63
    @29
    @68
    eqid
    #
    lsslss
    syl2anc
    mpbir2and
    ad2antrr
    @66
    @37
    cR
    cbs
    cfv
    #
    @71
    @32
    @35
    @75
    @36
    @14
    @32
    @2
    @35
    cP
    cR
    vf
    cI
    @75
    @14
    mplbas2.p
    @75
    eqid
    @9
    @44
    @50
    mplelf
    #
    ffvelrnda
    @66
    cR
    @70
    cbs
    @32
    cR
    @70
    wceq
    @65
    @32
    cP
    cR
    cI
    cW
    crg
    mplbas2.p
    @47
    @49
    mplsca
    #
    adantr
    fveq2d
    eleqtrd
    @66
    @40
    cP
    cmgp
    cfv
    #
    vz
    cI
    vz
    cv
    #
    @36
    cfv
    #
    @79
    cV
    cfv
    #
    @78
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    @1
    @66
    vy
    @35
    cP
    cR
    @38
    vf
    vz
    @82
    @78
    cI
    cV
    cW
    @36
    @39
    mplbas2.p
    @44
    @45
    @46
    wph
    @21
    @31
    @65
    mplbas2.i
    ad2antrr
    #
    @78
    eqid
    #
    @82
    eqid
    #
    mplbas2.v
    wph
    @16
    @31
    @65
    mplbas2.r
    ad2antrr
    @32
    @65
    simpr
    #
    mplcoe2
    @66
    cI
    @1
    @84
    @78
    cW
    cP
    cur
    cfv
    #
    cP
    @89
    @78
    @86
    @89
    eqid
    #
    ringidval
    #
    wph
    @78
    ccmn
    wcel
    #
    @31
    @65
    wph
    cP
    ccrg
    wcel
    #
    @92
    wph
    @21
    @16
    @93
    mplbas2.i
    mplbas2.r
    cP
    cR
    cI
    cW
    mplbas2.p
    mplcrng
    syl2anc
    cP
    @78
    @86
    crngmgp
    syl
    #
    ad2antrr
    @85
    @66
    @58
    @1
    @78
    csubmnd
    cfv
    wcel
    wph
    @58
    @31
    @65
    @64
    ad2antrr
    @1
    cP
    @78
    @86
    subrgsubm
    syl
    @66
    vz
    cI
    @83
    @1
    @84
    @66
    @79
    cI
    wcel
    #
    wa
    #
    wph
    @80
    cn0
    wcel
    @81
    @1
    wcel
    @83
    @1
    wcel
    wph
    @31
    @65
    @95
    simplll
    @66
    cI
    cn0
    @79
    @36
    @66
    cI
    cn0
    @36
    wf
    #
    @36
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @32
    @65
    @97
    @99
    wa
    #
    @32
    @21
    @65
    @100
    wb
    @47
    @35
    vf
    @36
    cI
    cW
    @44
    psrbag
    syl
    biimpa
    #
    simpld
    ffvelrnda
    @96
    @0
    @1
    @81
    wph
    @0
    @1
    wss
    #
    @31
    @65
    @95
    wph
    @4
    @61
    @102
    @8
    @62
    cA
    @0
    @5
    cS
    mplbas2.a
    @10
    aspssid
    syl2anc
    ad3antrrr
    @66
    @13
    @95
    @81
    @0
    wcel
    wph
    @13
    @31
    @65
    @19
    ad2antrr
    cI
    @79
    cV
    fnfvelrn
    sylan
    sseldd
    wph
    vu
    vv
    @2
    cP
    cmulr
    cfv
    #
    @1
    @82
    @78
    @80
    ccmn
    @81
    @89
    @2
    cP
    @78
    @86
    @9
    mgpbas
    #
    @87
    cP
    @103
    @78
    @86
    @103
    eqid
    #
    mgpplusg
    @94
    @30
    wph
    @58
    vu
    cv
    #
    @1
    wcel
    vv
    cv
    #
    @1
    wcel
    @106
    @107
    @103
    co
    @1
    wcel
    @64
    @1
    cP
    @103
    @106
    @107
    @105
    subrgmcl
    syl3an1
    @91
    wph
    @58
    @89
    @1
    wcel
    @64
    @1
    cP
    @89
    @90
    subrg1cl
    syl
    mulgnn0subcl
    syl3anc
    @84
    eqid
    fmptd
    @66
    @84
    cvv
    wcel
    #
    @84
    wfun
    #
    @89
    cvv
    wcel
    @99
    @84
    @89
    csupp
    co
    @98
    wss
    @84
    @89
    cfsupp
    wbr
    wph
    @108
    @31
    @65
    wph
    @21
    @108
    mplbas2.i
    vz
    cI
    @83
    cW
    mptexg
    syl
    ad2antrr
    @109
    @66
    vz
    cI
    @83
    funmpt
    a1i
    @66
    cP
    cur
    fvexd
    @66
    @97
    @99
    @101
    simprd
    @66
    cI
    @83
    vz
    cW
    @98
    @89
    @66
    @79
    cI
    @98
    cdif
    wcel
    #
    wa
    #
    @83
    cc0
    @81
    @82
    co
    #
    @89
    @111
    @80
    cc0
    @81
    @82
    @65
    @32
    @36
    @34
    wcel
    #
    @110
    @80
    cc0
    wceq
    @33
    vf
    @36
    @34
    elrabi
    @32
    @113
    wa
    #
    cI
    cn0
    cvv
    @36
    cW
    @98
    @79
    cc0
    @113
    @97
    @32
    @36
    cn0
    cI
    elmapi
    adantl
    #
    @114
    @36
    cc0
    csupp
    co
    #
    @98
    wceq
    #
    @116
    @98
    wss
    @114
    @21
    @97
    @117
    wph
    @21
    @31
    @113
    mplbas2.i
    ad2antrr
    #
    @115
    @36
    cI
    cW
    frnnn0supp
    syl2anc
    @116
    @98
    eqimss
    syl
    @118
    cc0
    cvv
    wcel
    @114
    c0ex
    a1i
    suppssr
    sylanl2
    oveq1d
    @111
    @81
    @2
    wcel
    @112
    @89
    wceq
    @111
    @2
    cP
    cR
    cI
    cV
    cW
    @79
    mplbas2.p
    mplbas2.v
    @9
    wph
    @21
    @31
    @65
    @110
    mplbas2.i
    ad3antrrr
    wph
    @17
    @31
    @65
    @110
    @18
    ad3antrrr
    @110
    @95
    @66
    @79
    cI
    @98
    eldifi
    adantl
    mvrcl
    @2
    @82
    @78
    @81
    @89
    @104
    @91
    @87
    mulg0
    syl
    eqtrd
    @85
    suppss2
    @98
    @84
    cvv
    cvv
    @89
    suppssfifsupp
    syl32anc
    gsumsubmcl
    eqeltrd
    @71
    @68
    @41
    @1
    @70
    cP
    @37
    @40
    @70
    eqid
    #
    @48
    @71
    eqid
    @74
    lssvscl
    syl22anc
    @43
    eqid
    fmptd
    @32
    @43
    cvv
    wcel
    #
    @43
    wfun
    #
    @51
    cvv
    wcel
    #
    w3a
    #
    @14
    @39
    csupp
    co
    #
    cfn
    wcel
    @43
    @51
    csupp
    co
    @124
    wss
    @43
    @51
    cfsupp
    wbr
    @123
    @32
    @120
    @121
    @122
    @33
    vk
    vf
    @34
    @42
    @55
    mptrabex
    vk
    @35
    @42
    funmpt
    cP
    c0g
    fvex
    3pm3.2i
    a1i
    @32
    @14
    @39
    @31
    @14
    @39
    cfsupp
    wbr
    #
    wph
    @31
    @14
    @5
    wcel
    @125
    @5
    cP
    cR
    cS
    @2
    cI
    @14
    @39
    mplbas2.p
    mplbas2.s
    @10
    @45
    @9
    mplelbas
    simprbi
    adantl
    fsuppimpd
    @32
    @35
    @42
    vk
    cvv
    @124
    @51
    @32
    @36
    @35
    @124
    cdif
    wcel
    #
    wa
    #
    @42
    @70
    c0g
    cfv
    #
    @40
    @41
    co
    #
    @51
    @127
    @37
    @128
    @40
    @41
    @127
    @37
    @39
    @128
    @32
    @35
    @75
    cvv
    @14
    cvv
    @124
    @36
    @39
    @76
    @124
    @124
    wss
    @32
    @124
    ssid
    a1i
    @56
    @32
    cR
    c0g
    fvexd
    suppssr
    @32
    @39
    @128
    wceq
    @126
    @32
    cR
    @70
    c0g
    @77
    fveq2d
    adantr
    eqtrd
    oveq1d
    @126
    @32
    @65
    @129
    @51
    wceq
    #
    @36
    @35
    @124
    eldifi
    @66
    @67
    @40
    @2
    wcel
    @130
    @72
    @66
    vy
    @2
    @35
    cP
    cR
    @38
    vf
    cI
    cW
    @36
    @39
    mplbas2.p
    @9
    @45
    @46
    @44
    @85
    wph
    @17
    @31
    @65
    @18
    ad2antrr
    @88
    mplmon
    @41
    @70
    @128
    @2
    cP
    @40
    @51
    @9
    @119
    @48
    @128
    eqid
    @52
    lmod0vs
    syl2anc
    sylan2
    eqtrd
    @56
    suppss2
    @124
    @43
    cvv
    cvv
    @51
    suppssfifsupp
    syl12anc
    gsumsubgcl
    eqeltrd
    ex
    ssrdv
    eqssd
end
