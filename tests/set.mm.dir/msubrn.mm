include "crn.mm"
include "cmap.mm"
include "co.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "cpm.mm"
include "cmex.mm"
include "cfv.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmrsub.mm"
include "cop.mm"
include "cmpt.mm"
include "eqid.mm"
include "msubffval.mm"
include "rneqd.mm"
include "wf.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "wfun.mm"
include "mrsubff.mm"
include "adantr.mm"
include "ffun.mm"
include "syl.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "mrsubrn.mm"
include "syl6eleq.mm"
include "fvelima.mm"
include "syl2anc.mm"
include "elmapi.mm"
include "adantl.mm"
include "ssid.mm"
include "msubfval.mm"
include "sylancl.mm"
include "fvex.mm"
include "mptex.mm"
include "fnmpti.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "mapsspm.mm"
include "a1i.mm"
include "simpr.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "adantlr.mm"
include "fveq1.mm"
include "opeq2d.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "fmptd.mm"
include "frn.mm"
include "eqsstrd.mm"
include "wn.mm"
include "c0.mm"
include "cmsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "rn0.mm"
include "syl6eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"
include "imassrn.mm"
include "eqssi.mm"

theorem msubrn
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let ve: setvar e
  let vf: setvar f
  let cE: class E
  let vg: setvar g
  let cW: class W
  assume msubff.v: |- V = ( mVR ` T )
  assume msubff.r: |- R = ( mREx ` T )
  assume msubff.s: |- S = ( mSubst ` T )


  assert |- ran S = ( S " ( R ^m V ) )

  proof
    cS
    crn
    #
    cS
    cR
    cV
    cmap
    co
    #
    cima
    #
    cT
    cvv
    wcel
    #
    @0
    @2
    wss
    @3
    @0
    vf
    cR
    cV
    cpm
    co
    #
    ve
    cT
    cmex
    cfv
    #
    ve
    cv
    #
    c1st
    cfv
    #
    @6
    c2nd
    cfv
    #
    vf
    cv
    #
    cT
    cmrsub
    cfv
    #
    cfv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    cmpt
    #
    crn
    #
    @2
    @3
    cS
    @15
    cR
    cS
    cT
    ve
    vf
    @5
    @10
    cV
    cvv
    msubff.v
    msubff.r
    msubff.s
    @5
    eqid
    #
    @10
    eqid
    #
    msubffval
    #
    rneqd
    @3
    @4
    @2
    @15
    wf
    @16
    @2
    wss
    @3
    vf
    @4
    @14
    @2
    @15
    @3
    @9
    @4
    wcel
    #
    wa
    #
    vg
    cv
    #
    @10
    cfv
    #
    @11
    wceq
    #
    vg
    @1
    wrex
    #
    @14
    @2
    wcel
    #
    @21
    @10
    wfun
    #
    @11
    @10
    @1
    cima
    #
    wcel
    @25
    @21
    @4
    cR
    cR
    cmap
    co
    #
    @10
    wf
    #
    @27
    @3
    @30
    @20
    cR
    @10
    cT
    cV
    cvv
    msubff.v
    msubff.r
    @18
    mrsubff
    #
    adantr
    @4
    @29
    @10
    ffun
    syl
    @21
    @11
    @10
    crn
    #
    @28
    @3
    @10
    @4
    wfn
    #
    @20
    @11
    @32
    wcel
    @3
    @30
    @33
    @31
    @4
    @29
    @10
    ffn
    syl
    @4
    @9
    @10
    fnfvelrn
    sylan
    cR
    @10
    cT
    cV
    msubff.v
    msubff.r
    @18
    mrsubrn
    syl6eleq
    vg
    @11
    @1
    @10
    fvelima
    syl2anc
    @21
    @24
    @26
    vg
    @1
    @21
    @22
    @1
    wcel
    #
    wa
    ve
    @5
    @7
    @8
    @23
    cfv
    #
    cop
    #
    cmpt
    #
    @2
    wcel
    #
    @24
    @26
    @3
    @34
    @38
    @20
    @3
    @34
    wa
    #
    @22
    cS
    cfv
    #
    @37
    @2
    @39
    cV
    cR
    @22
    wf
    #
    cV
    cV
    wss
    @40
    @37
    wceq
    @34
    @41
    @3
    @22
    cR
    cV
    elmapi
    adantl
    cV
    ssid
    cV
    cR
    cS
    cT
    ve
    @5
    @22
    @10
    cV
    msubff.v
    msubff.r
    msubff.s
    @17
    @18
    msubfval
    sylancl
    @39
    cS
    @4
    wfn
    #
    @1
    @4
    wss
    #
    @34
    @40
    @2
    wcel
    @3
    @42
    @34
    @3
    @42
    @15
    @4
    wfn
    vf
    @4
    @14
    @15
    ve
    @5
    @13
    cT
    cmex
    fvex
    mptex
    @15
    eqid
    #
    fnmpti
    @3
    @4
    cS
    @15
    @19
    fneq1d
    mpbiri
    adantr
    @43
    @39
    cR
    cV
    mapsspm
    a1i
    @3
    @34
    simpr
    @4
    @1
    cS
    @22
    fnfvima
    syl3anc
    eqeltrrd
    adantlr
    @24
    @37
    @14
    @2
    @24
    ve
    @5
    @36
    @13
    @24
    @35
    @12
    @7
    @8
    @23
    @11
    fveq1
    opeq2d
    mpteq2dv
    eleq1d
    syl5ibcom
    rexlimdva
    mpd
    @44
    fmptd
    @4
    @2
    @15
    frn
    syl
    eqsstrd
    @3
    wn
    #
    @0
    c0
    @2
    @45
    @0
    c0
    crn
    c0
    @45
    cS
    c0
    @45
    cS
    cT
    cmsub
    cfv
    c0
    msubff.s
    cT
    cmsub
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    @2
    0ss
    syl6eqss
    pm2.61i
    cS
    @1
    imassrn
    eqssi
end
