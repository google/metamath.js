include "ccph.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "cc.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "csca.mm"
include "cphl.mm"
include "cphphl.mm"
include "eqid.mm"
include "phlipf.mm"
include "syl.mm"
include "cclm.mm"
include "wss.mm"
include "cphclm.mm"
include "clmsscn.mm"
include "fssd.mm"
include "cip.mm"
include "c2.mm"
include "cdiv.mm"
include "cnm.mm"
include "c1.mm"
include "caddc.mm"
include "simpll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "ipcnlem1.mm"
include "ralrimiva.mm"
include "simprl.mm"
include "ovresd.mm"
include "breq1d.mm"
include "simprr.mm"
include "anbi12d.mm"
include "wceq.mm"
include "ad2antrr.mm"
include "fovrnd.mm"
include "cnmetdval.mm"
include "syl2anc.mm"
include "ipfval.mm"
include "adantl.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "imbi12d.mm"
include "2ralbidva.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "ralrimivva.mm"
include "cxmt.mm"
include "wb.mm"
include "cxme.mm"
include "cmt.mm"
include "cngp.mm"
include "cphngp.mm"
include "ngpms.mm"
include "msxms.mm"
include "xmsxmet.mm"
include "cnxmet.mm"
include "a1i.mm"
include "cnfldtopn.mm"
include "txmetcn.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "mstopn.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"

theorem ipcn
  let c.xi: class .,
  let cJ: class J
  let cK: class K
  let cW: class W
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ipcn.f: |- ., = ( .if ` W )
  assume ipcn.j: |- J = ( TopOpen ` W )
  assume ipcn.k: |- K = ( TopOpen ` CCfld )


  assert |- ( W e. CPreHil -> ., e. ( ( J tX J ) Cn K ) )

  proof
    cW
    ccph
    wcel
    #
    c.xi
    cW
    cds
    cfv
    #
    cW
    cbs
    cfv
    #
    @2
    cxp
    #
    cres
    #
    cmopn
    cfv
    #
    @5
    ctx
    co
    #
    cK
    ccn
    co
    #
    cJ
    cJ
    ctx
    co
    #
    cK
    ccn
    co
    @0
    c.xi
    @7
    wcel
    #
    @3
    cc
    c.xi
    wf
    #
    vx
    cv
    #
    vz
    cv
    #
    @4
    co
    #
    vs
    cv
    #
    clt
    wbr
    #
    vy
    cv
    #
    vw
    cv
    #
    @4
    co
    #
    @14
    clt
    wbr
    #
    wa
    #
    @11
    @16
    c.xi
    co
    #
    @12
    @17
    c.xi
    co
    #
    cabs
    cmin
    ccom
    #
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    @2
    wral
    vz
    @2
    wral
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    #
    vy
    @2
    wral
    vx
    @2
    wral
    #
    @0
    @3
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cc
    c.xi
    @0
    cW
    cphl
    wcel
    @3
    @33
    c.xi
    wf
    cW
    cphphl
    @32
    c.xi
    @33
    @2
    cW
    @2
    eqid
    #
    ipcn.f
    @32
    eqid
    #
    @33
    eqid
    #
    phlipf
    syl
    @0
    cW
    cclm
    wcel
    @33
    cc
    wss
    cW
    cphclm
    @32
    @33
    cW
    @35
    @36
    clmsscn
    syl
    fssd
    #
    @0
    @30
    vx
    vy
    @2
    @2
    @0
    @11
    @2
    wcel
    #
    @16
    @2
    wcel
    #
    wa
    #
    wa
    #
    @30
    @11
    @12
    @1
    co
    #
    @14
    clt
    wbr
    #
    @16
    @17
    @1
    co
    #
    @14
    clt
    wbr
    #
    wa
    #
    @11
    @16
    cW
    cip
    cfv
    #
    co
    #
    @12
    @17
    @47
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @25
    clt
    wbr
    #
    wi
    #
    vw
    @2
    wral
    vz
    @2
    wral
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    @41
    @55
    vr
    crp
    @41
    @25
    crp
    wcel
    #
    wa
    vz
    vw
    @11
    @16
    @1
    @25
    @25
    c2
    cdiv
    co
    #
    @11
    cW
    cnm
    cfv
    #
    cfv
    c1
    caddc
    co
    cdiv
    co
    #
    @57
    @16
    @58
    cfv
    @59
    caddc
    co
    cdiv
    co
    #
    @47
    @58
    @2
    cW
    vs
    @34
    @47
    eqid
    #
    @1
    eqid
    @58
    eqid
    @59
    eqid
    @60
    eqid
    @0
    @40
    @56
    simpll
    @0
    @38
    @39
    @56
    simplrl
    @0
    @38
    @39
    @56
    simplrr
    @41
    @56
    simpr
    ipcnlem1
    ralrimiva
    @41
    @29
    @55
    vr
    crp
    @41
    @28
    @54
    vs
    crp
    @41
    @27
    @53
    vz
    vw
    @2
    @2
    @41
    @12
    @2
    wcel
    #
    @17
    @2
    wcel
    #
    wa
    #
    wa
    #
    @20
    @46
    @26
    @52
    @65
    @15
    @43
    @19
    @45
    @65
    @13
    @42
    @14
    clt
    @65
    @11
    @12
    @1
    @2
    @0
    @38
    @39
    @64
    simplrl
    #
    @41
    @62
    @63
    simprl
    #
    ovresd
    breq1d
    @65
    @18
    @44
    @14
    clt
    @65
    @16
    @17
    @1
    @2
    @0
    @38
    @39
    @64
    simplrr
    #
    @41
    @62
    @63
    simprr
    #
    ovresd
    breq1d
    anbi12d
    @65
    @24
    @51
    @25
    clt
    @65
    @24
    @21
    @22
    cmin
    co
    #
    cabs
    cfv
    #
    @51
    @65
    @21
    cc
    wcel
    @22
    cc
    wcel
    @24
    @71
    wceq
    @65
    @11
    @16
    cc
    @2
    @2
    c.xi
    @0
    @10
    @40
    @64
    @37
    ad2antrr
    #
    @66
    @68
    fovrnd
    @65
    @12
    @17
    cc
    @2
    @2
    c.xi
    @72
    @67
    @69
    fovrnd
    @21
    @22
    @23
    @23
    eqid
    cnmetdval
    syl2anc
    @65
    @70
    @50
    cabs
    @65
    @21
    @48
    @22
    @49
    cmin
    @65
    @38
    @39
    @21
    @48
    wceq
    @66
    @68
    c.xi
    @47
    @2
    cW
    @11
    @16
    @34
    @61
    ipcn.f
    ipfval
    syl2anc
    @64
    @22
    @49
    wceq
    @41
    c.xi
    @47
    @2
    cW
    @12
    @17
    @34
    @61
    ipcn.f
    ipfval
    adantl
    oveq12d
    fveq2d
    eqtrd
    breq1d
    imbi12d
    2ralbidva
    rexbidv
    ralbidv
    mpbird
    ralrimivva
    @0
    @4
    @2
    cxmt
    cfv
    wcel
    #
    @73
    @23
    cc
    cxmt
    cfv
    wcel
    #
    @9
    @10
    @31
    wa
    wb
    @0
    cW
    cxme
    wcel
    #
    @73
    @0
    cW
    cmt
    wcel
    #
    @75
    @0
    cW
    cngp
    wcel
    @76
    cW
    cphngp
    cW
    ngpms
    syl
    #
    cW
    msxms
    syl
    @4
    cW
    @2
    @34
    @4
    eqid
    #
    xmsxmet
    syl
    #
    @79
    @74
    @0
    cnxmet
    a1i
    vx
    vy
    vr
    vs
    vw
    vz
    @4
    @4
    @23
    c.xi
    @5
    @5
    cK
    @2
    @2
    cc
    @5
    eqid
    #
    @80
    cK
    ipcn.k
    cnfldtopn
    txmetcn
    syl3anc
    mpbir2and
    @0
    @8
    @6
    cK
    ccn
    @0
    cJ
    @5
    cJ
    @5
    ctx
    @0
    @76
    cJ
    @5
    wceq
    @77
    @4
    cJ
    cW
    @2
    ipcn.j
    @34
    @78
    mstopn
    syl
    #
    @81
    oveq12d
    oveq1d
    eleqtrrd
end
