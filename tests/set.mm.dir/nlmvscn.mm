include "cnlm.mm"
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
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "eqid.mm"
include "lmodscaf.mm"
include "syl.mm"
include "cvsca.mm"
include "cnm.mm"
include "c2.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "simpll.mm"
include "simpr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "nlmvscnlem1.mm"
include "ralrimiva.mm"
include "simprl.mm"
include "ovresd.mm"
include "breq1d.mm"
include "simprr.mm"
include "anbi12d.mm"
include "wceq.mm"
include "scafval.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "oveq12d.mm"
include "ad2antrr.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "imbi12d.mm"
include "2ralbidva.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "ralrimivva.mm"
include "cxmt.mm"
include "wb.mm"
include "cmt.mm"
include "cxme.mm"
include "cngp.mm"
include "nlmngp2.mm"
include "ngpms.mm"
include "msxms.mm"
include "xmsxmet.mm"
include "3syl.mm"
include "nlmngp.mm"
include "txmetcn.mm"
include "mpbir2and.mm"
include "mstopn.mm"
include "eleqtrrd.mm"

theorem nlmvscn
  let c.x: class .x.
  let cF: class F
  let cJ: class J
  let cK: class K
  let cW: class W
  let cB: class B
  let vr: setvar r
  let cD: class D
  let cE: class E
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph
  let cT: class T
  let cU: class U
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let cR: class R
  let cV: class V
  let cX: class X
  assume nlmvscn.f: |- F = ( Scalar ` W )
  assume nlmvscn.sf: |- .x. = ( .sf ` W )
  assume nlmvscn.j: |- J = ( TopOpen ` W )
  assume nlmvscn.kf: |- K = ( TopOpen ` F )


  assert |- ( W e. NrmMod -> .x. e. ( ( K tX J ) Cn J ) )

  proof
    cW
    cnlm
    wcel
    #
    c.x
    cF
    cds
    cfv
    #
    cF
    cbs
    cfv
    #
    @2
    cxp
    cres
    #
    cmopn
    cfv
    #
    cW
    cds
    cfv
    #
    cW
    cbs
    cfv
    #
    @6
    cxp
    cres
    #
    cmopn
    cfv
    #
    ctx
    co
    #
    @8
    ccn
    co
    #
    cK
    cJ
    ctx
    co
    #
    cJ
    ccn
    co
    @0
    c.x
    @10
    wcel
    #
    @2
    @6
    cxp
    @6
    c.x
    wf
    #
    vx
    cv
    #
    vz
    cv
    #
    @3
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
    @7
    co
    #
    @17
    clt
    wbr
    #
    wa
    #
    @14
    @19
    c.x
    co
    #
    @15
    @20
    c.x
    co
    #
    @7
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
    @6
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
    @6
    wral
    vx
    @2
    wral
    #
    @0
    cW
    clmod
    wcel
    #
    @13
    cW
    nlmlmod
    #
    @6
    c.x
    cF
    @2
    cW
    @6
    eqid
    #
    nlmvscn.f
    @2
    eqid
    #
    nlmvscn.sf
    lmodscaf
    syl
    @0
    @32
    vx
    vy
    @2
    @6
    @0
    @14
    @2
    wcel
    #
    @19
    @6
    wcel
    #
    wa
    #
    wa
    #
    @32
    @14
    @15
    @1
    co
    #
    @17
    clt
    wbr
    #
    @19
    @20
    @5
    co
    #
    @17
    clt
    wbr
    #
    wa
    #
    @14
    @19
    cW
    cvsca
    cfv
    #
    co
    #
    @15
    @20
    @47
    co
    #
    @5
    co
    #
    @27
    clt
    wbr
    #
    wi
    #
    vw
    @6
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
    @54
    vr
    crp
    @41
    @27
    crp
    wcel
    #
    wa
    vz
    vw
    cF
    cnm
    cfv
    #
    @14
    @5
    @27
    @27
    c2
    cdiv
    co
    #
    @14
    @56
    cfv
    c1
    caddc
    co
    cdiv
    co
    #
    @47
    @57
    @19
    cW
    cnm
    cfv
    #
    cfv
    @58
    caddc
    co
    cdiv
    co
    #
    @1
    cF
    @2
    @59
    @6
    cW
    @19
    vs
    nlmvscn.f
    @36
    @37
    @5
    eqid
    @1
    eqid
    @59
    eqid
    @56
    eqid
    @47
    eqid
    #
    @58
    eqid
    @60
    eqid
    @0
    @40
    @55
    simpll
    @41
    @55
    simpr
    @0
    @38
    @39
    @55
    simplrl
    @0
    @38
    @39
    @55
    simplrr
    nlmvscnlem1
    ralrimiva
    @41
    @31
    @54
    vr
    crp
    @41
    @30
    @53
    vs
    crp
    @41
    @29
    @52
    vz
    vw
    @2
    @6
    @41
    @15
    @2
    wcel
    #
    @20
    @6
    wcel
    #
    wa
    #
    wa
    #
    @23
    @46
    @28
    @51
    @65
    @18
    @43
    @22
    @45
    @65
    @16
    @42
    @17
    clt
    @65
    @14
    @15
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
    @21
    @44
    @17
    clt
    @65
    @19
    @20
    @5
    @6
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
    @26
    @50
    @27
    clt
    @65
    @26
    @48
    @49
    @7
    co
    @50
    @65
    @24
    @48
    @25
    @49
    @7
    @40
    @24
    @48
    wceq
    @0
    @64
    @6
    c.x
    @47
    cF
    @2
    cW
    @14
    @19
    @36
    nlmvscn.f
    @37
    nlmvscn.sf
    @61
    scafval
    ad2antlr
    @64
    @25
    @49
    wceq
    @41
    @6
    c.x
    @47
    cF
    @2
    cW
    @15
    @20
    @36
    nlmvscn.f
    @37
    nlmvscn.sf
    @61
    scafval
    adantl
    oveq12d
    @65
    @48
    @49
    @5
    @6
    @65
    @34
    @38
    @39
    @48
    @6
    wcel
    @0
    @34
    @40
    @64
    @35
    ad2antrr
    #
    @66
    @68
    @14
    @47
    cF
    @2
    @6
    cW
    @19
    @36
    nlmvscn.f
    @61
    @37
    lmodvscl
    syl3anc
    @65
    @34
    @62
    @63
    @49
    @6
    wcel
    @70
    @67
    @69
    @15
    @47
    cF
    @2
    @6
    cW
    @20
    @36
    nlmvscn.f
    @61
    @37
    lmodvscl
    syl3anc
    ovresd
    eqtrd
    breq1d
    imbi12d
    2ralbidva
    rexbidv
    ralbidv
    mpbird
    ralrimivva
    @0
    @3
    @2
    cxmt
    cfv
    wcel
    #
    @7
    @6
    cxmt
    cfv
    wcel
    #
    @72
    @12
    @13
    @33
    wa
    wb
    @0
    cF
    cmt
    wcel
    #
    cF
    cxme
    wcel
    @71
    @0
    cF
    cngp
    wcel
    @73
    cF
    cW
    nlmvscn.f
    nlmngp2
    cF
    ngpms
    syl
    #
    cF
    msxms
    @3
    cF
    @2
    @37
    @3
    eqid
    #
    xmsxmet
    3syl
    @0
    cW
    cmt
    wcel
    #
    cW
    cxme
    wcel
    @72
    @0
    cW
    cngp
    wcel
    @76
    cW
    nlmngp
    cW
    ngpms
    syl
    #
    cW
    msxms
    @7
    cW
    @6
    @36
    @7
    eqid
    #
    xmsxmet
    3syl
    #
    @79
    vx
    vy
    vr
    vs
    vw
    vz
    @3
    @7
    @7
    c.x
    @4
    @8
    @8
    @2
    @6
    @6
    @4
    eqid
    @8
    eqid
    #
    @80
    txmetcn
    syl3anc
    mpbir2and
    @0
    @11
    @9
    cJ
    @8
    ccn
    @0
    cK
    @4
    cJ
    @8
    ctx
    @0
    @73
    cK
    @4
    wceq
    @74
    @3
    cK
    cF
    @2
    nlmvscn.kf
    @37
    @75
    mstopn
    syl
    @0
    @76
    cJ
    @8
    wceq
    @77
    @7
    cJ
    cW
    @6
    nlmvscn.j
    @36
    @78
    mstopn
    syl
    #
    oveq12d
    @81
    oveq12d
    eleqtrrd
end
