include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cxko.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cpt.mm"
include "cfv.mm"
include "cv.mm"
include "crest.mm"
include "ccmp.mm"
include "crab.mm"
include "cima.mm"
include "wss.mm"
include "ccn.mm"
include "cmpt2.mm"
include "crn.mm"
include "cfi.mm"
include "ctg.mm"
include "wceq.mm"
include "distop.mm"
include "adantl.mm"
include "simpl.mm"
include "cuni.mm"
include "unipw.mm"
include "eqcomi.mm"
include "eqid.mm"
include "xkoval.mm"
include "syl2anc.mm"
include "wf.mm"
include "simpr.mm"
include "fconst6g.mm"
include "adantr.mm"
include "pttop.mm"
include "cmap.mm"
include "wrex.mm"
include "cfn.mm"
include "cin.mm"
include "cab.mm"
include "elpwi.mm"
include "restdis.mm"
include "sylan2.mm"
include "adantll.mm"
include "eleq1d.mm"
include "discmp.mm"
include "syl6bbr.mm"
include "rabbidva.mm"
include "dfin5.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "ctopon.mm"
include "toptopon.mm"
include "cndis.mm"
include "ancoms.mm"
include "sylanb.mm"
include "rabeq.mm"
include "syl.mm"
include "mpt2eq123dv.mm"
include "rneqd.mm"
include "rnmpt2.mm"
include "syl6eq.mm"
include "cif.mm"
include "cixp.mm"
include "wb.mm"
include "elmapi.mm"
include "wral.mm"
include "wi.mm"
include "eleq2.mm"
include "imbi2d.mm"
include "bibi1d.mm"
include "inss1.mm"
include "simprl.mm"
include "sseldi.mm"
include "elpwid.mm"
include "sselda.mm"
include "2thd.mm"
include "imbi1d.mm"
include "wn.mm"
include "ffvelrn.mm"
include "ex.mm"
include "pm2.21.mm"
include "ifbothda.mm"
include "ralbidv2.mm"
include "wfn.mm"
include "ffn.mm"
include "vex.mm"
include "elixp.mm"
include "baib.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "3bitr4d.mm"
include "rabbi2dva.mm"
include "elssuni.mm"
include "ad2antll.mm"
include "ssid.mm"
include "sseq1.mm"
include "ifboth.mm"
include "sylancl.mm"
include "ralrimivw.mm"
include "ss2ixp.mm"
include "cvv.mm"
include "simplr.mm"
include "uniexg.mm"
include "ad2antrr.mm"
include "ixpconstg.mm"
include "sseqtrd.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqtr3d.mm"
include "inss2.mm"
include "simplrr.mm"
include "topopn.mm"
include "ad3antrrr.mm"
include "ifcld.mm"
include "simpll.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "eleqtrrd.mm"
include "cdif.mm"
include "eldifn.mm"
include "iffalsed.mm"
include "eldifi.mm"
include "unieqd.mm"
include "eqtr4d.mm"
include "ptopn.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "abssdv.mm"
include "eqsstrd.mm"
include "tgfiss.mm"
include "ptuniconst.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "restid.mm"
include "xkoptsub.mm"
include "eqsstr3d.mm"
include "eqssd.mm"

theorem xkopt
  let cA: class A
  let cR: class R
  let cV: class V
  let vf: setvar f
  let vk: setvar k
  let vv: setvar v
  let vx: setvar x


  assert |- ( ( R e. Top /\ A e. V ) -> ( R ^ko ~P A ) = ( Xt_ ` ( A X. { R } ) ) )

  proof
    cR
    ctop
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cR
    cA
    cpw
    #
    cxko
    co
    #
    cA
    cR
    csn
    cxp
    #
    cpt
    cfv
    #
    @2
    @4
    vk
    vv
    @3
    vx
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    vx
    @3
    crab
    #
    cR
    vf
    cv
    #
    vk
    cv
    #
    cima
    vv
    cv
    #
    wss
    #
    vf
    @3
    cR
    ccn
    co
    #
    crab
    #
    cmpt2
    #
    crn
    #
    cfi
    cfv
    ctg
    cfv
    #
    @6
    @2
    @3
    ctop
    wcel
    #
    @0
    @4
    @19
    wceq
    @1
    @20
    @0
    cA
    cV
    distop
    adantl
    #
    @0
    @1
    simpl
    #
    vx
    vv
    @3
    cR
    @17
    vf
    vk
    @10
    cA
    @3
    cuni
    cA
    cA
    unipw
    eqcomi
    #
    @10
    eqid
    @17
    eqid
    xkoval
    syl2anc
    @2
    @6
    ctop
    wcel
    #
    @18
    @6
    wss
    @19
    @6
    wss
    @2
    @1
    cA
    ctop
    @5
    wf
    #
    @24
    @0
    @1
    simpr
    @0
    @25
    @1
    cA
    cR
    ctop
    fconst6g
    #
    adantr
    cA
    @5
    cV
    pttop
    syl2anc
    #
    @2
    @18
    @7
    @14
    vf
    cR
    cuni
    #
    cA
    cmap
    co
    #
    crab
    #
    wceq
    #
    vv
    cR
    wrex
    vk
    @3
    cfn
    cin
    #
    wrex
    #
    vx
    cab
    #
    @6
    @2
    @18
    vk
    vv
    @32
    cR
    @30
    cmpt2
    #
    crn
    @34
    @2
    @17
    @35
    @2
    vk
    vv
    @10
    cR
    @16
    @32
    cR
    @30
    @2
    @10
    @7
    cfn
    wcel
    #
    vx
    @3
    crab
    @32
    @2
    @9
    @36
    vx
    @3
    @2
    @7
    @3
    wcel
    #
    wa
    #
    @9
    @7
    cpw
    #
    ccmp
    wcel
    @36
    @38
    @8
    @39
    ccmp
    @1
    @37
    @8
    @39
    wceq
    #
    @0
    @37
    @1
    @7
    cA
    wss
    @40
    @7
    cA
    elpwi
    cA
    @7
    cV
    restdis
    sylan2
    adantll
    eleq1d
    @7
    discmp
    syl6bbr
    rabbidva
    vx
    @3
    cfn
    dfin5
    syl6eqr
    @2
    cR
    eqidd
    @2
    @15
    @29
    wceq
    #
    @16
    @30
    wceq
    @0
    cR
    @28
    ctopon
    cfv
    wcel
    #
    @1
    @41
    cR
    @28
    @28
    eqid
    #
    toptopon
    @1
    @42
    @41
    cA
    cR
    cV
    @28
    cndis
    ancoms
    sylanb
    #
    @14
    vf
    @15
    @29
    rabeq
    syl
    mpt2eq123dv
    rneqd
    vk
    vv
    vx
    @32
    cR
    @30
    @35
    @35
    eqid
    rnmpt2
    syl6eq
    @2
    @33
    vx
    @6
    @2
    @31
    @7
    @6
    wcel
    #
    vk
    vv
    @32
    cR
    @2
    @12
    @32
    wcel
    #
    @13
    cR
    wcel
    #
    wa
    #
    wa
    #
    @45
    @31
    @30
    @6
    wcel
    @49
    @30
    vx
    cA
    @7
    @12
    wcel
    #
    @13
    @28
    cif
    #
    cixp
    #
    @6
    @49
    @29
    @52
    cin
    #
    @30
    @52
    @49
    @14
    vf
    @29
    @52
    @11
    @29
    wcel
    @49
    cA
    @28
    @11
    wf
    #
    @11
    @52
    wcel
    #
    @14
    wb
    @11
    @28
    cA
    elmapi
    @49
    @54
    wa
    #
    @7
    @11
    cfv
    #
    @51
    wcel
    #
    vx
    cA
    wral
    #
    @57
    @13
    wcel
    #
    vx
    @12
    wral
    #
    @55
    @14
    @56
    @58
    @60
    vx
    cA
    @12
    @50
    @7
    cA
    wcel
    #
    @60
    wi
    #
    @50
    @60
    wi
    #
    wb
    @62
    @57
    @28
    wcel
    #
    wi
    #
    @64
    wb
    @62
    @58
    wi
    #
    @64
    wb
    @56
    @13
    @28
    @13
    @51
    wceq
    #
    @63
    @67
    @64
    @68
    @60
    @58
    @62
    @13
    @51
    @57
    eleq2
    imbi2d
    bibi1d
    @28
    @51
    wceq
    #
    @66
    @67
    @64
    @69
    @65
    @58
    @62
    @28
    @51
    @57
    eleq2
    imbi2d
    bibi1d
    @56
    @50
    wa
    #
    @62
    @50
    @60
    @70
    @62
    @50
    @56
    @12
    cA
    @7
    @49
    @12
    cA
    wss
    @54
    @49
    @12
    cA
    @49
    @32
    @3
    @12
    @3
    cfn
    inss1
    @2
    @46
    @47
    simprl
    #
    sseldi
    elpwid
    adantr
    #
    sselda
    @56
    @50
    simpr
    2thd
    imbi1d
    @56
    @50
    wn
    #
    wa
    @66
    @64
    @56
    @66
    @73
    @54
    @66
    @49
    @54
    @62
    @65
    cA
    @28
    @7
    @11
    ffvelrn
    ex
    adantl
    adantr
    @73
    @64
    @56
    @50
    @60
    pm2.21
    adantl
    2thd
    ifbothda
    ralbidv2
    @56
    @11
    cA
    wfn
    #
    @55
    @59
    wb
    @54
    @74
    @49
    cA
    @28
    @11
    ffn
    adantl
    @55
    @74
    @59
    vx
    cA
    @51
    @11
    vf
    vex
    elixp
    baib
    syl
    @56
    @11
    wfun
    #
    @12
    @11
    cdm
    #
    wss
    @14
    @61
    wb
    @54
    @75
    @49
    cA
    @28
    @11
    ffun
    adantl
    @56
    @12
    cA
    @76
    @72
    @54
    @76
    cA
    wceq
    @49
    cA
    @28
    @11
    fdm
    adantl
    sseqtr4d
    vx
    @12
    @13
    @11
    funimass4
    syl2anc
    3bitr4d
    sylan2
    rabbi2dva
    @49
    @52
    @29
    wss
    @53
    @52
    wceq
    @49
    @52
    vx
    cA
    @28
    cixp
    #
    @29
    @49
    @51
    @28
    wss
    #
    vx
    cA
    wral
    @52
    @77
    wss
    @49
    @78
    vx
    cA
    @49
    @13
    @28
    wss
    #
    @28
    @28
    wss
    #
    @78
    @47
    @79
    @2
    @46
    @13
    cR
    elssuni
    ad2antll
    @28
    ssid
    @50
    @79
    @80
    @78
    @13
    @28
    @13
    @51
    @28
    sseq1
    @28
    @51
    @28
    sseq1
    ifboth
    sylancl
    ralrimivw
    vx
    cA
    @51
    @28
    ss2ixp
    syl
    @49
    @1
    @28
    cvv
    wcel
    #
    @77
    @29
    wceq
    @0
    @1
    @48
    simplr
    #
    @0
    @81
    @1
    @48
    cR
    ctop
    uniexg
    ad2antrr
    vx
    cA
    @28
    cV
    cvv
    ixpconstg
    syl2anc
    sseqtrd
    @52
    @29
    sseqin2
    sylib
    eqtr3d
    @49
    cA
    @51
    vx
    @5
    cV
    @12
    @82
    @0
    @25
    @1
    @48
    @26
    ad2antrr
    @49
    @32
    cfn
    @12
    @3
    cfn
    inss2
    @71
    sseldi
    @49
    @62
    wa
    #
    @51
    cR
    @7
    @5
    cfv
    #
    @83
    @50
    @13
    @28
    cR
    @2
    @46
    @47
    @62
    simplrr
    @0
    @28
    cR
    wcel
    @1
    @48
    @62
    cR
    @28
    @43
    topopn
    ad3antrrr
    ifcld
    @49
    @0
    @62
    @84
    cR
    wceq
    #
    @0
    @1
    @48
    simpll
    cA
    cR
    @7
    ctop
    fvconst2g
    sylan
    #
    eleqtrrd
    @49
    @7
    cA
    @12
    cdif
    wcel
    #
    wa
    #
    @51
    @28
    @84
    cuni
    @87
    @51
    @28
    wceq
    @49
    @87
    @50
    @13
    @28
    @7
    cA
    @12
    eldifn
    iffalsed
    adantl
    @88
    @84
    cR
    @87
    @49
    @62
    @85
    @7
    cA
    @12
    eldifi
    @86
    sylan2
    unieqd
    eqtr4d
    ptopn
    eqeltrd
    @7
    @30
    @6
    eleq1
    syl5ibrcom
    rexlimdvva
    abssdv
    eqsstrd
    @18
    @6
    tgfiss
    syl2anc
    eqsstrd
    @2
    @6
    @6
    @15
    crest
    co
    #
    @4
    @2
    @89
    @6
    @6
    cuni
    #
    crest
    co
    #
    @6
    @2
    @15
    @90
    @6
    crest
    @2
    @15
    @29
    @90
    @44
    @1
    @0
    @29
    @90
    wceq
    cA
    cR
    @6
    cV
    @28
    @6
    eqid
    #
    @43
    ptuniconst
    ancoms
    eqtrd
    oveq2d
    @2
    @24
    @91
    @6
    wceq
    @27
    @6
    ctop
    @90
    @90
    eqid
    restid
    syl
    eqtrd
    @2
    @20
    @0
    @89
    @4
    wss
    @21
    @22
    @3
    cR
    @6
    cA
    @23
    @92
    xkoptsub
    syl2anc
    eqsstr3d
    eqssd
end
