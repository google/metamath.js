include "cmnd.mm"
include "wcel.mm"
include "ctps.mm"
include "cplusf.mm"
include "cfv.mm"
include "ctopn.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "ctmd.mm"
include "wf.mm"
include "wss.mm"
include "cv.mm"
include "tmdmnd.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "prdsmndd.mm"
include "tmdtps.mm"
include "prdstps.mm"
include "ccom.mm"
include "cpt.mm"
include "cbs.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cplusg.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "w3a.mm"
include "eqid.mm"
include "3ad2ant1.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "simp2.mm"
include "simp3.mm"
include "prdsplusgval.mm"
include "mpt2eq3dva.mm"
include "plusffval.mm"
include "cop.mm"
include "wceq.mm"
include "vex.mm"
include "op1std.mm"
include "fveq1d.mm"
include "op2ndd.mm"
include "oveq12d.mm"
include "mpteq2dv.mm"
include "mpt2mpt.mm"
include "3eqtr4g.mm"
include "ctopon.mm"
include "istps.mm"
include "sylib.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "ctop.mm"
include "cres.mm"
include "wral.mm"
include "cvv.mm"
include "topnfn.mm"
include "ssv.mm"
include "fnssres.mm"
include "mp2an.mm"
include "fvres.mm"
include "tpstop.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "fco2.mm"
include "sylancr.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "cnmpt1st.mm"
include "cuni.mm"
include "prdstopn.mm"
include "eqeltrrd.mm"
include "toponuni.mm"
include "mpteq1d.mm"
include "simpr.mm"
include "ptpjcn.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "fvco3.mm"
include "sylan.mm"
include "eleqtrd.mm"
include "fveq1.mm"
include "cnmpt21.mm"
include "cnmpt2nd.mm"
include "cnmpt2plusg.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "syl5eqel.mm"
include "ptcn.mm"
include "istmd.mm"
include "syl3anbrc.mm"

theorem prdstmdd
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  let vz: setvar z
  assume prdstmdd.y: |- Y = ( S Xs_ R )
  assume prdstmdd.i: |- ( ph -> I e. W )
  assume prdstmdd.s: |- ( ph -> S e. V )
  assume prdstmdd.r: |- ( ph -> R : I --> TopMnd )


  assert |- ( ph -> Y e. TopMnd )

  proof
    wph
    cY
    cmnd
    wcel
    cY
    ctps
    wcel
    #
    cY
    cplusf
    cfv
    #
    cY
    ctopn
    cfv
    #
    @2
    ctx
    co
    #
    @2
    ccn
    co
    #
    wcel
    cY
    ctmd
    wcel
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdstmdd.y
    prdstmdd.i
    prdstmdd.s
    wph
    cI
    ctmd
    cR
    wf
    #
    ctmd
    cmnd
    wss
    cI
    cmnd
    cR
    wf
    prdstmdd.r
    vx
    ctmd
    cmnd
    vx
    cv
    #
    tmdmnd
    ssriv
    cI
    ctmd
    cmnd
    cR
    fss
    sylancl
    prdsmndd
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdstmdd.y
    prdstmdd.s
    prdstmdd.i
    wph
    @5
    ctmd
    ctps
    wss
    cI
    ctps
    cR
    wf
    #
    prdstmdd.r
    vx
    ctmd
    ctps
    @6
    tmdtps
    ssriv
    cI
    ctmd
    ctps
    cR
    fss
    sylancl
    #
    prdstps
    #
    wph
    @1
    @3
    ctopn
    cR
    ccom
    #
    cpt
    cfv
    #
    ccn
    co
    #
    @4
    wph
    @1
    vz
    cY
    cbs
    cfv
    #
    @13
    cxp
    #
    vk
    cI
    vk
    cv
    #
    vz
    cv
    #
    c1st
    cfv
    #
    cfv
    #
    @15
    @16
    c2nd
    cfv
    #
    cfv
    #
    @15
    cR
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    cmpt
    #
    @12
    wph
    vf
    vg
    @13
    @13
    vf
    cv
    #
    vg
    cv
    #
    cY
    cplusg
    cfv
    #
    co
    #
    cmpt2
    vf
    vg
    @13
    @13
    vk
    cI
    @15
    @26
    cfv
    #
    @15
    @27
    cfv
    #
    @22
    co
    #
    cmpt
    #
    cmpt2
    @1
    @25
    wph
    vf
    vg
    @13
    @13
    @29
    @33
    wph
    @26
    @13
    wcel
    #
    @27
    @13
    wcel
    #
    w3a
    vk
    @13
    @28
    cR
    cS
    @26
    @27
    cI
    cV
    cW
    cY
    prdstmdd.y
    @13
    eqid
    #
    wph
    @34
    cS
    cV
    wcel
    @35
    prdstmdd.s
    3ad2ant1
    wph
    @34
    cI
    cW
    wcel
    #
    @35
    prdstmdd.i
    3ad2ant1
    wph
    @34
    cR
    cI
    wfn
    #
    @35
    wph
    @5
    @38
    prdstmdd.r
    cI
    ctmd
    cR
    ffn
    syl
    #
    3ad2ant1
    wph
    @34
    @35
    simp2
    wph
    @34
    @35
    simp3
    @28
    eqid
    #
    prdsplusgval
    mpt2eq3dva
    vf
    vg
    @13
    @28
    @1
    cY
    @36
    @40
    @1
    eqid
    #
    plusffval
    vf
    vg
    vz
    @13
    @13
    @24
    @33
    @16
    @26
    @27
    cop
    wceq
    #
    vk
    cI
    @23
    @32
    @42
    @18
    @30
    @20
    @31
    @22
    @42
    @15
    @17
    @26
    @26
    @27
    @16
    vf
    vex
    #
    vg
    vex
    #
    op1std
    fveq1d
    @42
    @15
    @19
    @27
    @26
    @27
    @16
    @43
    @44
    op2ndd
    fveq1d
    oveq12d
    #
    mpteq2dv
    mpt2mpt
    3eqtr4g
    wph
    vz
    @23
    vk
    @10
    cI
    @3
    @11
    cW
    @14
    @11
    eqid
    #
    wph
    @2
    @13
    ctopon
    cfv
    #
    wcel
    #
    @48
    @3
    @14
    ctopon
    cfv
    wcel
    wph
    @0
    @48
    @9
    @13
    @2
    cY
    @36
    @2
    eqid
    #
    istps
    sylib
    #
    @50
    @2
    @2
    @13
    @13
    txtopon
    syl2anc
    prdstmdd.i
    wph
    ctps
    ctop
    ctopn
    ctps
    cres
    #
    wf
    #
    @7
    cI
    ctop
    @10
    wf
    #
    @52
    @51
    ctps
    wfn
    #
    @6
    @51
    cfv
    #
    ctop
    wcel
    #
    vx
    ctps
    wral
    ctopn
    cvv
    wfn
    ctps
    cvv
    wss
    @54
    topnfn
    ctps
    ssv
    cvv
    ctps
    ctopn
    fnssres
    mp2an
    @56
    vx
    ctps
    @6
    ctps
    wcel
    @55
    @6
    ctopn
    cfv
    #
    ctop
    @6
    ctps
    ctopn
    fvres
    @57
    @6
    @57
    eqid
    tpstop
    eqeltrd
    rgen
    vx
    ctps
    ctop
    @51
    ffnfv
    mpbir2an
    @8
    cI
    ctps
    ctop
    ctopn
    cR
    fco2
    sylancr
    #
    wph
    @15
    cI
    wcel
    #
    wa
    #
    vz
    @14
    @23
    cmpt
    vf
    vg
    @13
    @13
    @32
    cmpt2
    #
    @3
    @15
    @10
    cfv
    #
    ccn
    co
    #
    vf
    vg
    vz
    @13
    @13
    @23
    @32
    @45
    mpt2mpt
    @60
    @61
    @3
    @21
    ctopn
    cfv
    #
    ccn
    co
    @63
    @60
    vf
    vg
    @30
    @31
    @22
    @21
    @64
    @2
    @2
    @13
    @13
    @64
    eqid
    @22
    eqid
    wph
    cI
    ctmd
    @15
    cR
    prdstmdd.r
    ffvelrnda
    wph
    @48
    @59
    @50
    adantr
    #
    @65
    @60
    vf
    vg
    vx
    @26
    @15
    @6
    cfv
    #
    @30
    @2
    @2
    @2
    @64
    @13
    @13
    @13
    @65
    @65
    @60
    vf
    vg
    @2
    @2
    @13
    @13
    @65
    @65
    cnmpt1st
    @65
    @60
    vx
    @13
    @66
    cmpt
    #
    @11
    @62
    ccn
    co
    #
    @2
    @64
    ccn
    co
    @60
    @67
    vx
    @11
    cuni
    #
    @66
    cmpt
    #
    @68
    @60
    vx
    @13
    @69
    @66
    @60
    @11
    @47
    wcel
    @13
    @69
    wceq
    @60
    @2
    @11
    @47
    wph
    @2
    @11
    wceq
    @59
    wph
    cR
    cS
    cI
    @2
    cV
    cW
    cY
    prdstmdd.y
    prdstmdd.s
    prdstmdd.i
    @39
    @49
    prdstopn
    #
    adantr
    #
    @65
    eqeltrrd
    @13
    @11
    toponuni
    syl
    mpteq1d
    @60
    @37
    @53
    @59
    @70
    @68
    wcel
    wph
    @37
    @59
    prdstmdd.i
    adantr
    wph
    @53
    @59
    @58
    adantr
    wph
    @59
    simpr
    vx
    cI
    @10
    @15
    @11
    cW
    @69
    @69
    eqid
    @46
    ptpjcn
    syl3anc
    eqeltrd
    @60
    @11
    @2
    @62
    @64
    ccn
    @60
    @2
    @11
    @72
    eqcomd
    wph
    @5
    @59
    @62
    @64
    wceq
    prdstmdd.r
    cI
    ctmd
    @15
    ctopn
    cR
    fvco3
    sylan
    #
    oveq12d
    eleqtrd
    #
    @15
    @6
    @26
    fveq1
    cnmpt21
    @60
    vf
    vg
    vx
    @27
    @66
    @31
    @2
    @2
    @2
    @64
    @13
    @13
    @13
    @65
    @65
    @60
    vf
    vg
    @2
    @2
    @13
    @13
    @65
    @65
    cnmpt2nd
    @65
    @74
    @15
    @6
    @27
    fveq1
    cnmpt21
    cnmpt2plusg
    @60
    @62
    @64
    @3
    ccn
    @73
    oveq2d
    eleqtrrd
    syl5eqel
    ptcn
    eqeltrd
    wph
    @2
    @11
    @3
    ccn
    @71
    oveq2d
    eleqtrrd
    @1
    cY
    @2
    @41
    @49
    istmd
    syl3anbrc
end
