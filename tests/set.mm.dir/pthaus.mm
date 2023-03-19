include "wcel.mm"
include "cha.mm"
include "wf.mm"
include "wa.mm"
include "cpt.mm"
include "cfv.mm"
include "ctop.mm"
include "cv.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "cuni.mm"
include "wral.mm"
include "wss.mm"
include "haustop.mm"
include "ssriv.mm"
include "fss.mm"
include "mpan2.mm"
include "pttop.mm"
include "sylan2.mm"
include "wn.mm"
include "wfn.mm"
include "weq.mm"
include "wb.mm"
include "cixp.mm"
include "simprl.mm"
include "eqid.mm"
include "ptuni.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "ixpfn.mm"
include "syl.mm"
include "simprr.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "necon3abid.mm"
include "rexnal.mm"
include "df-ne.mm"
include "simpllr.mm"
include "ffvelrnd.mm"
include "vex.mm"
include "elixp.mm"
include "simprbi.mm"
include "r19.21bi.mm"
include "adantrr.mm"
include "hausnei.mm"
include "syl13anc.mm"
include "crab.mm"
include "cmpt.mm"
include "ccn.mm"
include "co.mm"
include "simp-4l.mm"
include "ad4antlr.mm"
include "ptpjcn.mm"
include "syl3anc.mm"
include "simprll.mm"
include "ccnv.mm"
include "cima.mm"
include "mptpreima.mm"
include "cnima.mm"
include "syl5eqelr.mm"
include "simprlr.mm"
include "ad2antrr.mm"
include "simprr1.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "simprr2.mm"
include "inrab.mm"
include "simprr3.mm"
include "inelcm.mm"
include "necon2bi.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "eleq2.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "ineq2.mm"
include "3anbi23d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "syl5bir.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "ishaus.mm"

theorem pthaus
  let cA: class A
  let cF: class F
  let cV: class V
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vv: setvar v


  assert |- ( ( A e. V /\ F : A --> Haus ) -> ( Xt_ ` F ) e. Haus )

  proof
    cA
    cV
    wcel
    #
    cA
    cha
    cF
    wf
    #
    wa
    #
    cF
    cpt
    cfv
    #
    ctop
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @5
    vu
    cv
    #
    wcel
    #
    @6
    vv
    cv
    #
    wcel
    #
    @8
    @10
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vv
    @3
    wrex
    vu
    @3
    wrex
    #
    wi
    #
    vy
    @3
    cuni
    #
    wral
    vx
    @17
    wral
    @3
    cha
    wcel
    @1
    @0
    cA
    ctop
    cF
    wf
    #
    @4
    @1
    cha
    ctop
    wss
    @18
    vx
    cha
    ctop
    @5
    haustop
    ssriv
    cA
    cha
    ctop
    cF
    fss
    mpan2
    #
    cA
    cF
    cV
    pttop
    sylan2
    @2
    @16
    vx
    vy
    @17
    @17
    @2
    @5
    @17
    wcel
    #
    @6
    @17
    wcel
    #
    wa
    #
    wa
    #
    @7
    vk
    cv
    #
    @5
    cfv
    #
    @24
    @6
    cfv
    #
    wceq
    #
    vk
    cA
    wral
    #
    wn
    #
    @15
    @23
    @28
    @5
    @6
    @23
    @5
    cA
    wfn
    #
    @6
    cA
    wfn
    #
    vx
    vy
    weq
    @28
    wb
    @23
    @5
    vk
    cA
    @24
    cF
    cfv
    #
    cuni
    #
    cixp
    #
    wcel
    #
    @30
    @23
    @5
    @17
    @34
    @2
    @20
    @21
    simprl
    #
    @2
    @34
    @17
    wceq
    #
    @22
    @1
    @0
    @18
    @37
    @19
    vk
    cA
    cF
    @3
    cV
    @3
    eqid
    #
    ptuni
    sylan2
    adantr
    #
    eleqtrrd
    #
    vk
    cA
    @33
    @5
    ixpfn
    syl
    @23
    @6
    @34
    wcel
    #
    @31
    @23
    @6
    @17
    @34
    @2
    @20
    @21
    simprr
    #
    @39
    eleqtrrd
    #
    vk
    cA
    @33
    @6
    ixpfn
    syl
    vk
    cA
    @5
    @6
    eqfnfv
    syl2anc
    necon3abid
    @29
    @27
    wn
    #
    vk
    cA
    wrex
    @23
    @15
    @27
    vk
    cA
    rexnal
    @23
    @44
    @15
    vk
    cA
    @44
    @25
    @26
    wne
    #
    @23
    @24
    cA
    wcel
    #
    wa
    @15
    @25
    @26
    df-ne
    @23
    @46
    @45
    @15
    @23
    @46
    @45
    wa
    #
    wa
    #
    @25
    vm
    cv
    #
    wcel
    #
    @26
    vn
    cv
    #
    wcel
    #
    @49
    @51
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vn
    @32
    wrex
    vm
    @32
    wrex
    #
    @15
    @48
    @32
    cha
    wcel
    @25
    @33
    wcel
    #
    @26
    @33
    wcel
    #
    @45
    @56
    @48
    cA
    cha
    @24
    cF
    @0
    @1
    @22
    @47
    simpllr
    @23
    @46
    @45
    simprl
    #
    ffvelrnd
    @23
    @46
    @57
    @45
    @23
    @57
    vk
    cA
    @23
    @35
    @57
    vk
    cA
    wral
    #
    @40
    @35
    @30
    @60
    vk
    cA
    @33
    @5
    vx
    vex
    elixp
    simprbi
    syl
    r19.21bi
    adantrr
    @23
    @46
    @58
    @45
    @23
    @58
    vk
    cA
    @23
    @41
    @58
    vk
    cA
    wral
    #
    @43
    @41
    @31
    @61
    vk
    cA
    @33
    @6
    vy
    vex
    elixp
    simprbi
    syl
    r19.21bi
    adantrr
    @23
    @46
    @45
    simprr
    @25
    @26
    vn
    vm
    @32
    @33
    @33
    eqid
    hausnei
    syl13anc
    @48
    @55
    @15
    vm
    vn
    @32
    @32
    @48
    @49
    @32
    wcel
    #
    @51
    @32
    wcel
    #
    wa
    #
    @55
    @15
    @48
    @64
    @55
    wa
    #
    wa
    #
    @24
    vz
    cv
    #
    cfv
    #
    @49
    wcel
    #
    vz
    @17
    crab
    #
    @3
    wcel
    #
    @68
    @51
    wcel
    #
    vz
    @17
    crab
    #
    @3
    wcel
    #
    @5
    @70
    wcel
    #
    @6
    @73
    wcel
    #
    @70
    @73
    cin
    #
    c0
    wceq
    #
    @15
    @66
    vz
    @17
    @68
    cmpt
    #
    @3
    @32
    ccn
    co
    wcel
    #
    @62
    @71
    @66
    @0
    @18
    @46
    @80
    @0
    @1
    @22
    @47
    @65
    simp-4l
    @1
    @18
    @0
    @22
    @47
    @65
    @19
    ad4antlr
    @48
    @46
    @65
    @59
    adantr
    vz
    cA
    cF
    @24
    @3
    cV
    @17
    @17
    eqid
    #
    @38
    ptpjcn
    syl3anc
    #
    @48
    @62
    @63
    @55
    simprll
    @80
    @62
    wa
    @70
    @79
    ccnv
    #
    @49
    cima
    @3
    vz
    @17
    @68
    @49
    @79
    @79
    eqid
    #
    mptpreima
    @49
    @79
    @3
    @32
    cnima
    syl5eqelr
    syl2anc
    @66
    @80
    @63
    @74
    @82
    @48
    @62
    @63
    @55
    simprlr
    @80
    @63
    wa
    @73
    @83
    @51
    cima
    @3
    vz
    @17
    @68
    @51
    @79
    @84
    mptpreima
    @51
    @79
    @3
    @32
    cnima
    syl5eqelr
    syl2anc
    @66
    @20
    @50
    @75
    @23
    @20
    @47
    @65
    @36
    ad2antrr
    @50
    @52
    @54
    @64
    @48
    simprr1
    @69
    @50
    vz
    @5
    @17
    vz
    vx
    weq
    @68
    @25
    @49
    @24
    @67
    @5
    fveq1
    eleq1d
    elrab
    sylanbrc
    @66
    @21
    @52
    @76
    @23
    @21
    @47
    @65
    @42
    ad2antrr
    @50
    @52
    @54
    @64
    @48
    simprr2
    @72
    @52
    vz
    @6
    @17
    vz
    vy
    weq
    @68
    @26
    @51
    @24
    @67
    @6
    fveq1
    eleq1d
    elrab
    sylanbrc
    @66
    @77
    @69
    @72
    wa
    #
    vz
    @17
    crab
    #
    c0
    @69
    @72
    vz
    @17
    inrab
    @66
    @85
    wn
    #
    vz
    @17
    wral
    @86
    c0
    wceq
    @66
    @87
    vz
    @17
    @66
    @54
    @87
    @50
    @52
    @54
    @64
    @48
    simprr3
    @85
    @53
    c0
    @68
    @49
    @51
    inelcm
    necon2bi
    syl
    ralrimivw
    @85
    vz
    @17
    rabeq0
    sylibr
    syl5eq
    @14
    @75
    @76
    @78
    w3a
    @75
    @11
    @70
    @10
    cin
    #
    c0
    wceq
    #
    w3a
    vu
    vv
    @70
    @73
    @3
    @3
    @8
    @70
    wceq
    #
    @9
    @75
    @13
    @89
    @11
    @8
    @70
    @5
    eleq2
    @90
    @12
    @88
    c0
    @8
    @70
    @10
    ineq1
    eqeq1d
    3anbi13d
    @10
    @73
    wceq
    #
    @11
    @76
    @89
    @78
    @75
    @10
    @73
    @6
    eleq2
    @91
    @88
    @77
    c0
    @10
    @73
    @70
    ineq2
    eqeq1d
    3anbi23d
    rspc2ev
    syl113anc
    expr
    rexlimdvva
    mpd
    expr
    syl5bir
    rexlimdva
    syl5bir
    sylbid
    ralrimivva
    vx
    vy
    vv
    vu
    @3
    @17
    @81
    ishaus
    sylanbrc
end
