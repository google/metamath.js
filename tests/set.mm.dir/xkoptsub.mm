include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "crest.mm"
include "cuni.mm"
include "cmap.mm"
include "csn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "cmpt2.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "ctg.mm"
include "cxko.mm"
include "cxp.mm"
include "cpt.mm"
include "wfn.mm"
include "wral.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wex.mm"
include "cab.mm"
include "topopn.mm"
include "adantr.mm"
include "wf.mm"
include "fconstg.mm"
include "adantl.mm"
include "ffn.mm"
include "syl.mm"
include "eqid.mm"
include "ptval.mm"
include "syl2anc.mm"
include "simpr.mm"
include "snssd.mm"
include "fssd.mm"
include "ptbasfi.mm"
include "fvconst2g.mm"
include "adantll.mm"
include "unieqd.mm"
include "ixpeq2dva.mm"
include "ixpconstg.mm"
include "syl2an.mm"
include "eqtrd.mm"
include "sneqd.mm"
include "mpteq1d.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "ralrimivw.mm"
include "jca.mm"
include "ralrimiva.mm"
include "mpt2eq123.mm"
include "sylancr.mm"
include "rneqd.mm"
include "uneq12d.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "firest.mm"
include "fveq2i.mm"
include "cvv.mm"
include "fvex.mm"
include "ovex.mm"
include "tgrest.mm"
include "mp2an.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "wss.mm"
include "xkotop.mm"
include "cin.mm"
include "snex.mm"
include "mpt2exga.mm"
include "sylan.mm"
include "rnexg.mm"
include "unexg.mm"
include "restval.mm"
include "sylancl.mm"
include "wo.mm"
include "elun.mm"
include "cnf.mm"
include "wb.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "syl5ibr.mm"
include "ssrdv.mm"
include "elsni.mm"
include "sseqtr4d.mm"
include "sseqin2.mm"
include "sylib.mm"
include "xkouni.mm"
include "eqeltrd.mm"
include "rnmpt2.mm"
include "abeq2i.mm"
include "crab.mm"
include "cres.mm"
include "cnvresima.mm"
include "resmptd.mm"
include "syl5eqr.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "elpreima.mm"
include "fveq1.mm"
include "fvmpt.mm"
include "eleq1d.mm"
include "snss.mm"
include "sselda.mm"
include "elmapi.mm"
include "3syl.mm"
include "simplrl.mm"
include "fnsnfv.mm"
include "sseq1d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "simpll.mm"
include "simprl.mm"
include "cpw.mm"
include "ccmp.mm"
include "ctopon.mm"
include "toptopon.mm"
include "restsn2.mm"
include "snfi.mm"
include "discmp.mm"
include "mpbi.mm"
include "syl6eqel.mm"
include "simprr.mm"
include "xkoopn.mm"
include "ineq1.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "imp.mm"
include "sylan2b.mm"
include "jaodan.mm"
include "fmptd.mm"
include "frn.mm"
include "eqsstrd.mm"
include "tgfiss.mm"

theorem xkoptsub
  let cR: class R
  let cS: class S
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xkoptsub.x: |- X = U. R
  assume xkoptsub.j: |- J = ( Xt_ ` ( X X. { S } ) )


  assert |- ( ( R e. Top /\ S e. Top ) -> ( J |`t ( R Cn S ) ) C_ ( S ^ko R ) )

  proof
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    wa
    #
    cJ
    cR
    cS
    ccn
    co
    #
    crest
    co
    #
    cS
    cuni
    #
    cX
    cmap
    co
    #
    csn
    #
    vk
    vu
    cX
    cS
    vw
    @6
    vk
    cv
    #
    vw
    cv
    #
    cfv
    #
    cmpt
    #
    ccnv
    #
    vu
    cv
    #
    cima
    #
    cmpt2
    #
    crn
    #
    cun
    #
    @3
    crest
    co
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    cS
    cR
    cxko
    co
    #
    @2
    @4
    @17
    cfi
    cfv
    #
    ctg
    cfv
    #
    @3
    crest
    co
    #
    @20
    @2
    cJ
    @23
    @3
    crest
    @2
    cJ
    cX
    cS
    csn
    #
    cxp
    #
    cpt
    cfv
    #
    @23
    xkoptsub.j
    @2
    @27
    vg
    cv
    #
    cX
    wfn
    vy
    cv
    #
    @28
    cfv
    #
    @29
    @26
    cfv
    #
    wcel
    vy
    cX
    wral
    @30
    @31
    cuni
    wceq
    vy
    cX
    vz
    cv
    cdif
    wral
    vz
    cfn
    wrex
    w3a
    vx
    cv
    #
    vy
    cX
    @30
    cixp
    wceq
    wa
    vg
    wex
    vx
    cab
    #
    ctg
    cfv
    #
    @23
    @2
    cX
    cR
    wcel
    #
    @26
    cX
    wfn
    #
    @27
    @34
    wceq
    @0
    @35
    @1
    cR
    cX
    xkoptsub.x
    topopn
    #
    adantr
    #
    @2
    cX
    @25
    @26
    wf
    #
    @36
    @1
    @39
    @0
    cX
    cS
    ctop
    fconstg
    adantl
    #
    cX
    @25
    @26
    ffn
    syl
    vx
    vy
    vz
    cX
    @33
    vg
    @26
    cR
    @33
    eqid
    #
    ptval
    syl2anc
    @2
    @33
    @22
    ctg
    @2
    @33
    vn
    cX
    vn
    cv
    #
    @26
    cfv
    #
    cuni
    #
    cixp
    #
    csn
    #
    vk
    vu
    cX
    @8
    @26
    cfv
    #
    vw
    @45
    @10
    cmpt
    #
    ccnv
    #
    @13
    cima
    #
    cmpt2
    #
    crn
    #
    cun
    #
    cfi
    cfv
    #
    @22
    @2
    @35
    cX
    ctop
    @26
    wf
    @33
    @54
    wceq
    @38
    @2
    cX
    @25
    ctop
    @26
    @40
    @2
    cS
    ctop
    @0
    @1
    simpr
    #
    snssd
    fssd
    vx
    vy
    vz
    vw
    vu
    cX
    @33
    vg
    vk
    vn
    @26
    cR
    @45
    @41
    @45
    eqid
    ptbasfi
    syl2anc
    @2
    @53
    @17
    cfi
    @2
    @46
    @7
    @52
    @16
    @2
    @45
    @6
    @2
    @45
    vn
    cX
    @5
    cixp
    #
    @6
    @2
    vn
    cX
    @44
    @5
    @2
    @42
    cX
    wcel
    #
    wa
    @43
    cS
    @1
    @57
    @43
    cS
    wceq
    @0
    cX
    cS
    @42
    ctop
    fvconst2g
    adantll
    unieqd
    ixpeq2dva
    @0
    @35
    @5
    cS
    wcel
    #
    @56
    @6
    wceq
    @1
    @37
    cS
    @5
    @5
    eqid
    #
    topopn
    #
    vn
    cX
    @5
    cR
    cS
    ixpconstg
    syl2an
    eqtrd
    #
    sneqd
    @2
    @51
    @15
    @2
    cX
    cX
    wceq
    @47
    cS
    wceq
    #
    @50
    @14
    wceq
    #
    vu
    @47
    wral
    #
    wa
    #
    vk
    cX
    wral
    @51
    @15
    wceq
    cX
    eqid
    @2
    @65
    vk
    cX
    @2
    @8
    cX
    wcel
    #
    wa
    #
    @62
    @64
    @1
    @66
    @62
    @0
    cX
    cS
    @8
    ctop
    fvconst2g
    adantll
    @67
    @63
    vu
    @47
    @67
    @49
    @12
    @13
    @67
    @48
    @11
    @67
    vw
    @45
    @6
    @10
    @2
    @45
    @6
    wceq
    @66
    @61
    adantr
    mpteq1d
    cnveqd
    imaeq1d
    ralrimivw
    jca
    ralrimiva
    vk
    vu
    cX
    @47
    @50
    cX
    cS
    @14
    mpt2eq123
    sylancr
    rneqd
    uneq12d
    fveq2d
    eqtrd
    fveq2d
    eqtrd
    syl5eq
    oveq1d
    @20
    @22
    @3
    crest
    co
    #
    ctg
    cfv
    #
    @24
    @19
    @68
    ctg
    @3
    @17
    firest
    fveq2i
    @22
    cvv
    wcel
    @3
    cvv
    wcel
    #
    @69
    @24
    wceq
    @17
    cfi
    fvex
    cR
    cS
    ccn
    ovex
    #
    @3
    @22
    cvv
    cvv
    tgrest
    mp2an
    eqtri
    syl6eqr
    @2
    @21
    ctop
    wcel
    #
    @18
    @21
    wss
    @20
    @21
    wss
    cR
    cS
    xkotop
    #
    @2
    @18
    vx
    @17
    @32
    @3
    cin
    #
    cmpt
    #
    crn
    #
    @21
    @2
    @17
    cvv
    wcel
    #
    @70
    @18
    @76
    wceq
    @2
    @7
    cvv
    wcel
    @16
    cvv
    wcel
    #
    @77
    @6
    snex
    @2
    @15
    cvv
    wcel
    #
    @78
    @0
    @35
    @1
    @79
    @37
    vk
    vu
    cX
    cS
    @14
    cR
    ctop
    mpt2exga
    sylan
    @15
    cvv
    rnexg
    syl
    @7
    @16
    cvv
    cvv
    unexg
    sylancr
    @71
    vx
    @3
    @17
    cvv
    cvv
    restval
    sylancl
    @2
    @17
    @21
    @75
    wf
    @76
    @21
    wss
    @2
    vx
    @17
    @74
    @21
    @75
    @32
    @17
    wcel
    @2
    @32
    @7
    wcel
    #
    @32
    @16
    wcel
    #
    wo
    @74
    @21
    wcel
    #
    @32
    @7
    @16
    elun
    @2
    @80
    @82
    @81
    @2
    @80
    wa
    #
    @74
    @3
    @21
    @83
    @3
    @32
    wss
    @74
    @3
    wceq
    @83
    @3
    @6
    @32
    @2
    @3
    @6
    wss
    #
    @80
    @2
    vx
    @3
    @6
    @32
    @3
    wcel
    @32
    @6
    wcel
    #
    @2
    cX
    @5
    @32
    wf
    #
    @32
    cR
    cS
    cX
    @5
    xkoptsub.x
    @59
    cnf
    @1
    @58
    @35
    @85
    @86
    wb
    @0
    @60
    @37
    @5
    cX
    @32
    cS
    cR
    elmapg
    syl2anr
    syl5ibr
    ssrdv
    #
    adantr
    @80
    @32
    @6
    wceq
    @2
    @32
    @6
    elsni
    adantl
    sseqtr4d
    @3
    @32
    sseqin2
    sylib
    @2
    @3
    @21
    wcel
    @80
    @2
    @3
    @21
    cuni
    #
    @21
    cR
    cS
    @21
    @21
    eqid
    xkouni
    @2
    @72
    @88
    @21
    wcel
    @73
    @21
    @88
    @88
    eqid
    topopn
    syl
    eqeltrd
    adantr
    eqeltrd
    @81
    @2
    @32
    @14
    wceq
    #
    vu
    cS
    wrex
    vk
    cX
    wrex
    #
    @82
    @90
    vx
    @16
    vk
    vu
    vx
    cX
    cS
    @14
    @15
    @15
    eqid
    rnmpt2
    abeq2i
    @2
    @90
    @82
    @2
    @89
    @82
    vk
    vu
    cX
    cS
    @2
    @66
    @13
    cS
    wcel
    #
    wa
    #
    wa
    #
    @82
    @89
    @14
    @3
    cin
    #
    @21
    wcel
    @93
    @94
    vf
    cv
    #
    @8
    csn
    #
    cima
    #
    @13
    wss
    #
    vf
    @3
    crab
    #
    @21
    @93
    @94
    vw
    @3
    @10
    cmpt
    #
    ccnv
    #
    @13
    cima
    #
    @99
    @93
    @94
    @11
    @3
    cres
    #
    ccnv
    #
    @13
    cima
    @102
    @3
    @13
    @11
    cnvresima
    @93
    @104
    @101
    @13
    @93
    @103
    @100
    @93
    vw
    @6
    @3
    @10
    @2
    @84
    @92
    @87
    adantr
    #
    resmptd
    cnveqd
    imaeq1d
    syl5eqr
    @93
    @102
    @95
    @3
    wcel
    #
    @98
    wa
    #
    vf
    cab
    @99
    @93
    @107
    vf
    @102
    @93
    @95
    @102
    wcel
    #
    @106
    @95
    @100
    cfv
    #
    @13
    wcel
    #
    wa
    #
    @107
    @93
    @100
    @3
    wfn
    #
    @108
    @111
    wb
    @10
    cvv
    wcel
    #
    vw
    @3
    wral
    @112
    @93
    @113
    vw
    @3
    @8
    @9
    fvex
    rgenw
    vw
    @3
    @10
    @100
    cvv
    @100
    eqid
    #
    fnmpt
    mp1i
    @3
    @95
    @13
    @100
    elpreima
    syl
    @93
    @106
    @110
    @98
    @93
    @106
    wa
    #
    @110
    @8
    @95
    cfv
    #
    @13
    wcel
    #
    @98
    @115
    @109
    @116
    @13
    @106
    @109
    @116
    wceq
    @93
    vw
    @95
    @10
    @116
    @3
    @100
    @8
    @9
    @95
    fveq1
    @114
    @8
    @95
    fvex
    #
    fvmpt
    adantl
    eleq1d
    @117
    @116
    csn
    #
    @13
    wss
    @115
    @98
    @116
    @13
    @118
    snss
    @115
    @119
    @97
    @13
    @115
    @95
    cX
    wfn
    #
    @66
    @119
    @97
    wceq
    @115
    @95
    @6
    wcel
    cX
    @5
    @95
    wf
    @120
    @93
    @3
    @6
    @95
    @105
    sselda
    @95
    @5
    cX
    elmapi
    cX
    @5
    @95
    ffn
    3syl
    @2
    @66
    @91
    @106
    simplrl
    cX
    @8
    @95
    fnsnfv
    syl2anc
    sseq1d
    syl5bb
    bitrd
    pm5.32da
    bitrd
    abbi2dv
    @98
    vf
    @3
    df-rab
    syl6eqr
    eqtrd
    @93
    @96
    cR
    cS
    @13
    vf
    cX
    xkoptsub.x
    @0
    @1
    @92
    simpll
    #
    @2
    @1
    @92
    @55
    adantr
    @93
    @8
    cX
    @2
    @66
    @91
    simprl
    #
    snssd
    @93
    cR
    @96
    crest
    co
    #
    @96
    cpw
    #
    ccmp
    @93
    cR
    cX
    ctopon
    cfv
    wcel
    #
    @66
    @123
    @124
    wceq
    @93
    @0
    @125
    @121
    cR
    cX
    xkoptsub.x
    toptopon
    sylib
    @122
    @8
    cR
    cX
    restsn2
    syl2anc
    @96
    cfn
    wcel
    @124
    ccmp
    wcel
    @8
    snfi
    @96
    discmp
    mpbi
    syl6eqel
    @2
    @66
    @91
    simprr
    xkoopn
    eqeltrd
    @89
    @74
    @94
    @21
    @32
    @14
    @3
    ineq1
    eleq1d
    syl5ibrcom
    rexlimdvva
    imp
    sylan2b
    jaodan
    sylan2b
    @75
    eqid
    fmptd
    @17
    @21
    @75
    frn
    syl
    eqsstrd
    @18
    @21
    tgfiss
    syl2anc
    eqsstrd
end
