include "cr.mm"
include "wf.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "ccnp.mm"
include "ccnv.mm"
include "cep.mm"
include "ccom.mm"
include "csn.mm"
include "cima.mm"
include "cdif.mm"
include "covol.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "cmbf.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wel.mm"
include "wss.mm"
include "wrex.mm"
include "crab.mm"
include "wn.mm"
include "cun.mm"
include "cmpt.mm"
include "id.mm"
include "feqmptd.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "ad2antrr.mm"
include "wo.mm"
include "exmid.mm"
include "biantrur.mm"
include "andir.mm"
include "bitri.mm"
include "ctb.mm"
include "retopbas.mm"
include "bastg.mm"
include "ax-mp.mm"
include "sseli.mm"
include "ad2antlr.mm"
include "cnpimaex.mm"
include "3com12.mm"
include "3expa.mm"
include "sylanl1.mm"
include "ex.mm"
include "wi.mm"
include "simprrr.mm"
include "wfn.mm"
include "ffn.mm"
include "adantr.mm"
include "cpw.mm"
include "restsspw.mm"
include "elpwid.mm"
include "simpl.mm"
include "fnfvima.mm"
include "syl3an.mm"
include "3expb.mm"
include "sseldd.mm"
include "rexlimdvaa.mm"
include "ad3antrrr.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "r19.42v.mm"
include "syl6bbr.mm"
include "orbi1d.mm"
include "syl5bb.mm"
include "rabbidva.mm"
include "eqid.mm"
include "mptpreima.mm"
include "unrab.mm"
include "3eqtr4g.mm"
include "eqtrd.mm"
include "3adantl3.mm"
include "ciun.mm"
include "cin.mm"
include "incom.mm"
include "dfin4.mm"
include "inrab.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "iunin2.mm"
include "iunrab.mm"
include "3eqtr3i.mm"
include "c0.mm"
include "cif.mm"
include "eqeq2.mm"
include "cab.mm"
include "simprrl.mm"
include "sselda.mm"
include "pm3.22.mm"
include "adantll.mm"
include "jca.mm"
include "impbida.mm"
include "abbidv.mm"
include "df-rab.mm"
include "cvjust.mm"
include "simpr.mm"
include "con3i.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "adantl.mm"
include "ifbothda.mm"
include "ctop.mm"
include "retop.mm"
include "resttop.mm"
include "mpan.mm"
include "0opn.mm"
include "syl.mm"
include "ifcl.mm"
include "ancoms.mm"
include "sylan.mm"
include "ralrimiva.mm"
include "iunopn.mm"
include "syl2anc.mm"
include "subopnmbl.mm"
include "mpdan.mm"
include "syl5eqel.mm"
include "difss.mm"
include "ssrab2.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"
include "sstri.mm"
include "mblss.mm"
include "syl5ss.mm"
include "ssdif.mm"
include "wb.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex.mm"
include "fnmpti.mm"
include "ctopon.mm"
include "retopon.mm"
include "resttopon.mm"
include "sylancr.mm"
include "cnpfval.mm"
include "sylancl.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "elpreima.mm"
include "wbr.mm"
include "wrel.mm"
include "rele.mm"
include "elrelimasn.mm"
include "fvex.mm"
include "epelc.mm"
include "bitr2i.mm"
include "anbi2i.mm"
include "syl6rbbr.mm"
include "imaco.mm"
include "abid2.mm"
include "eqtr4i.mm"
include "difeq2d.mm"
include "syl5sseq.mm"
include "ovolssnul.mm"
include "nulmbl.mm"
include "difmbl.mm"
include "syl5eqelr.mm"
include "eleq2i.mm"
include "ibar.mm"
include "syl5rbb.mm"
include "sylan9bb.mm"
include "notbid.mm"
include "biimpd.mm"
include "adantrd.mm"
include "ss2rabdv.mm"
include "dfdif2.mm"
include "syl6sseqr.mm"
include "unmbl.mm"
include "3adant1.mm"
include "eqeltrd.mm"
include "ismbf.mm"
include "3ad2ant1.mm"
include "mpbird.mm"

theorem cnambfre
  let cA: class A
  let cF: class F
  let vb: setvar b
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : A --> RR /\ A e. dom vol /\ ( vol* ` ( A \ ( ( `' ( ( ( topGen ` ran (,) ) |`t A ) CnP ( topGen ` ran (,) ) ) o. _E ) " { F } ) ) ) = 0 ) -> F e. MblFn )

  proof
    cA
    cr
    cF
    wf
    #
    cA
    cvol
    cdm
    #
    wcel
    #
    cA
    cioo
    crn
    #
    ctg
    cfv
    #
    cA
    crest
    co
    #
    @4
    ccnp
    co
    #
    ccnv
    #
    cep
    ccom
    cF
    csn
    #
    cima
    #
    cdif
    #
    covol
    cfv
    cc0
    wceq
    #
    w3a
    #
    cF
    cmbf
    wcel
    #
    cF
    ccnv
    #
    vb
    cv
    #
    cima
    #
    @1
    wcel
    #
    vb
    @3
    wral
    #
    @12
    @17
    vb
    @3
    @12
    @15
    @3
    wcel
    #
    wa
    @16
    cF
    vx
    cv
    #
    @6
    cfv
    #
    wcel
    #
    vx
    vy
    wel
    #
    cF
    vy
    cv
    #
    cima
    #
    @15
    wss
    #
    wa
    #
    wa
    #
    vy
    @5
    wrex
    #
    vx
    cA
    crab
    #
    @22
    wn
    #
    @20
    cF
    cfv
    #
    @15
    wcel
    #
    wa
    #
    vx
    cA
    crab
    #
    cun
    #
    @1
    @0
    @2
    @19
    @16
    @36
    wceq
    @11
    @0
    @2
    wa
    #
    @19
    wa
    #
    @16
    vx
    cA
    @32
    cmpt
    #
    ccnv
    #
    @15
    cima
    #
    @36
    @0
    @16
    @41
    wceq
    @2
    @19
    @0
    @14
    @40
    @15
    @0
    cF
    @39
    @0
    vx
    cA
    cr
    cF
    @0
    id
    feqmptd
    cnveqd
    imaeq1d
    ad2antrr
    @38
    @33
    vx
    cA
    crab
    @29
    @34
    wo
    #
    vx
    cA
    crab
    @41
    @36
    @38
    @33
    @42
    vx
    cA
    @33
    @22
    @33
    wa
    #
    @34
    wo
    #
    @38
    @20
    cA
    wcel
    #
    wa
    #
    @42
    @33
    @22
    @31
    wo
    #
    @33
    wa
    @44
    @47
    @33
    @22
    exmid
    biantrur
    @22
    @31
    @33
    andir
    bitri
    @46
    @43
    @29
    @34
    @46
    @43
    @22
    @27
    vy
    @5
    wrex
    #
    wa
    @29
    @46
    @22
    @33
    @48
    @46
    @22
    wa
    #
    @33
    @48
    @49
    @33
    @48
    @46
    @15
    @4
    wcel
    #
    @22
    @33
    @48
    @19
    @50
    @37
    @45
    @3
    @4
    @15
    @3
    ctb
    wcel
    @3
    @4
    wss
    retopbas
    @3
    ctb
    bastg
    ax-mp
    sseli
    ad2antlr
    @50
    @22
    @33
    @48
    @22
    @50
    @33
    @48
    vy
    @15
    @20
    cF
    @5
    @4
    cnpimaex
    3com12
    3expa
    sylanl1
    ex
    @37
    @48
    @33
    wi
    @19
    @45
    @22
    @37
    @27
    @33
    vy
    @5
    @37
    @24
    @5
    wcel
    #
    @27
    wa
    wa
    @25
    @15
    @32
    @37
    @51
    @23
    @26
    simprrr
    @37
    @51
    @27
    @32
    @25
    wcel
    #
    @37
    cF
    cA
    wfn
    #
    @51
    @24
    cA
    wss
    #
    @27
    @23
    @52
    @0
    @53
    @2
    cA
    cr
    cF
    ffn
    adantr
    @51
    @24
    cA
    @5
    cA
    cpw
    @24
    cA
    @4
    restsspw
    sseli
    elpwid
    #
    @23
    @26
    simpl
    cA
    @24
    cF
    @20
    fnfvima
    syl3an
    3expb
    sseldd
    rexlimdvaa
    ad3antrrr
    impbid
    pm5.32da
    @22
    @27
    vy
    @5
    r19.42v
    syl6bbr
    orbi1d
    syl5bb
    rabbidva
    vx
    cA
    @32
    @15
    @39
    @39
    eqid
    mptpreima
    @29
    @34
    vx
    cA
    unrab
    3eqtr4g
    eqtrd
    3adantl3
    @12
    @36
    @1
    wcel
    #
    @19
    @2
    @11
    @56
    @0
    @2
    @11
    wa
    #
    @30
    @1
    wcel
    @35
    @1
    wcel
    #
    @56
    @57
    @30
    vy
    @5
    @27
    vx
    cA
    crab
    #
    ciun
    #
    @60
    @22
    vx
    cA
    crab
    #
    cdif
    #
    cdif
    #
    @1
    @60
    @61
    cin
    @61
    @60
    cin
    #
    @63
    @30
    @60
    @61
    incom
    @60
    @61
    dfin4
    vy
    @5
    @61
    @59
    cin
    #
    ciun
    vy
    @5
    @28
    vx
    cA
    crab
    #
    ciun
    @64
    @30
    vy
    @5
    @65
    @66
    @65
    @66
    wceq
    @51
    @22
    @27
    vx
    cA
    inrab
    a1i
    iuneq2i
    vy
    @5
    @61
    @59
    iunin2
    @28
    vy
    vx
    @5
    cA
    iunrab
    3eqtr3i
    3eqtr3i
    @57
    @60
    @1
    wcel
    #
    @62
    @1
    wcel
    #
    @63
    @1
    wcel
    @2
    @67
    @11
    @2
    @60
    vy
    @5
    @26
    @24
    c0
    cif
    #
    ciun
    #
    @1
    vy
    @5
    @59
    @69
    @26
    @59
    @24
    wceq
    @59
    c0
    wceq
    #
    @59
    @69
    wceq
    @51
    @24
    c0
    @24
    @69
    @59
    eqeq2
    c0
    @69
    @59
    eqeq2
    @51
    @26
    wa
    #
    @45
    @27
    wa
    #
    vx
    cab
    @23
    vx
    cab
    @59
    @24
    @72
    @73
    @23
    vx
    @72
    @73
    @23
    @72
    @45
    @23
    @26
    simprrl
    @72
    @23
    wa
    @45
    @27
    @72
    @24
    cA
    @20
    @51
    @54
    @26
    @55
    adantr
    sselda
    @26
    @23
    @27
    @51
    @26
    @23
    pm3.22
    adantll
    jca
    impbida
    abbidv
    @27
    vx
    cA
    df-rab
    vy
    vx
    cvjust
    3eqtr4g
    @26
    wn
    #
    @71
    @51
    @74
    @27
    wn
    #
    vx
    cA
    wral
    @71
    @74
    @75
    vx
    cA
    @27
    @26
    @23
    @26
    simpr
    con3i
    ralrimivw
    @27
    vx
    cA
    rabeq0
    sylibr
    adantl
    ifbothda
    iuneq2i
    @2
    @70
    @5
    wcel
    #
    @70
    @1
    wcel
    @2
    @5
    ctop
    wcel
    #
    @69
    @5
    wcel
    #
    vy
    @5
    wral
    @76
    @4
    ctop
    wcel
    @2
    @77
    retop
    cA
    @4
    @1
    resttop
    mpan
    #
    @2
    @78
    vy
    @5
    @2
    c0
    @5
    wcel
    #
    @51
    @78
    @2
    @77
    @80
    @79
    @5
    0opn
    syl
    @51
    @80
    @78
    @26
    @24
    c0
    @5
    ifcl
    ancoms
    sylan
    ralrimiva
    vy
    @5
    @69
    @5
    iunopn
    syl2anc
    cA
    @70
    @5
    @5
    eqid
    subopnmbl
    mpdan
    syl5eqel
    adantr
    @57
    @62
    cr
    wss
    #
    @62
    covol
    cfv
    cc0
    wceq
    #
    @68
    @2
    @81
    @11
    @2
    @62
    cA
    cr
    @62
    @60
    cA
    @60
    @61
    difss
    @60
    cA
    wss
    #
    @59
    cA
    wss
    #
    vy
    @5
    wral
    @84
    vy
    @5
    @27
    vx
    cA
    ssrab2
    rgenw
    vy
    @5
    @59
    cA
    iunss
    mpbir
    #
    sstri
    cA
    mblss
    #
    syl5ss
    adantr
    @2
    @62
    @10
    wss
    #
    @10
    cr
    wss
    #
    wa
    @11
    @82
    @2
    @87
    @88
    @2
    cA
    @61
    cdif
    #
    @62
    @10
    @83
    @62
    @89
    wss
    @85
    @60
    cA
    @61
    ssdif
    ax-mp
    @2
    @61
    @9
    cA
    @2
    @45
    @22
    wa
    #
    vx
    cab
    @20
    @7
    cep
    @8
    cima
    #
    cima
    #
    wcel
    #
    vx
    cab
    #
    @61
    @9
    @2
    @90
    @93
    vx
    @2
    @93
    @45
    @21
    @91
    wcel
    #
    wa
    #
    @90
    @2
    @6
    cA
    wfn
    #
    @93
    @96
    wb
    @2
    @97
    vx
    cA
    @20
    vf
    cv
    #
    cfv
    @15
    wcel
    @23
    @98
    @24
    cima
    @15
    wss
    wa
    vy
    @5
    wrex
    wi
    vb
    @4
    wral
    #
    vf
    cr
    cA
    cmap
    co
    #
    crab
    #
    cmpt
    #
    cA
    wfn
    vx
    cA
    @101
    @102
    @99
    vf
    @100
    cr
    cA
    cmap
    ovex
    rabex
    @102
    eqid
    fnmpti
    @2
    cA
    @6
    @102
    @2
    @5
    cA
    ctopon
    cfv
    wcel
    #
    @4
    cr
    ctopon
    cfv
    wcel
    #
    @6
    @102
    wceq
    @2
    @104
    cA
    cr
    wss
    @103
    retopon
    @86
    cA
    @4
    cr
    resttopon
    sylancr
    retopon
    vx
    vb
    vy
    vf
    @5
    @4
    cA
    cr
    cnpfval
    sylancl
    fneq1d
    mpbiri
    cA
    @20
    @91
    @6
    elpreima
    syl
    #
    @22
    @95
    @45
    @95
    cF
    @21
    cep
    wbr
    #
    @22
    cep
    wrel
    @95
    @106
    wb
    rele
    cF
    @21
    cep
    elrelimasn
    ax-mp
    cF
    @21
    @20
    @6
    fvex
    epelc
    bitr2i
    #
    anbi2i
    syl6rbbr
    abbidv
    @22
    vx
    cA
    df-rab
    @9
    @92
    @94
    @7
    cep
    @8
    imaco
    #
    vx
    @92
    abid2
    eqtr4i
    3eqtr4g
    difeq2d
    syl5sseq
    @2
    @10
    cA
    cr
    cA
    @9
    difss
    @86
    syl5ss
    #
    jca
    @87
    @88
    @11
    @82
    @62
    @10
    ovolssnul
    3expa
    sylan
    @62
    nulmbl
    syl2anc
    @60
    @62
    difmbl
    syl2anc
    syl5eqelr
    @57
    @35
    cr
    wss
    #
    @35
    covol
    cfv
    cc0
    wceq
    #
    @58
    @2
    @110
    @11
    @2
    @35
    cA
    cr
    @34
    vx
    cA
    ssrab2
    @86
    syl5ss
    adantr
    @2
    @35
    @10
    wss
    #
    @88
    wa
    @11
    @111
    @2
    @112
    @88
    @2
    @35
    @20
    @9
    wcel
    #
    wn
    #
    vx
    cA
    crab
    @10
    @2
    @34
    @114
    vx
    cA
    @2
    @45
    wa
    #
    @31
    @114
    @33
    @115
    @31
    @114
    @115
    @22
    @113
    @113
    @93
    @115
    @22
    @9
    @92
    @20
    @108
    eleq2i
    @2
    @93
    @96
    @45
    @22
    @105
    @22
    @95
    @45
    @96
    @107
    @45
    @95
    ibar
    syl5rbb
    sylan9bb
    syl5rbb
    notbid
    biimpd
    adantrd
    ss2rabdv
    vx
    cA
    @9
    dfdif2
    syl6sseqr
    @109
    jca
    @112
    @88
    @11
    @111
    @35
    @10
    ovolssnul
    3expa
    sylan
    @35
    nulmbl
    syl2anc
    @30
    @35
    unmbl
    syl2anc
    3adant1
    adantr
    eqeltrd
    ralrimiva
    @0
    @2
    @13
    @18
    wb
    @11
    vb
    cA
    cF
    ismbf
    3ad2ant1
    mpbird
end
