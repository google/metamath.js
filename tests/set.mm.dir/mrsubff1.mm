include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "cpm.mm"
include "mrsubff.mm"
include "wss.mm"
include "mapsspm.mm"
include "a1i.mm"
include "fssresd.mm"
include "wa.mm"
include "cs1.mm"
include "fveq1.mm"
include "simplrl.mm"
include "elmapi.mm"
include "syl.mm"
include "ssid.mm"
include "simpr.mm"
include "mrsubvr.mm"
include "syl3anc.mm"
include "simplrr.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "ralrimdva.mm"
include "wb.mm"
include "fvres.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "wfn.mm"
include "ffn.mm"
include "eqfnfv.mm"
include "syl2an.mm"
include "3imtr4d.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem mrsubff1
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  assume mrsubvr.v: |- V = ( mVR ` T )
  assume mrsubvr.r: |- R = ( mREx ` T )
  assume mrsubvr.s: |- S = ( mRSubst ` T )


  assert |- ( T e. W -> ( S |` ( R ^m V ) ) : ( R ^m V ) -1-1-> ( R ^m R ) )

  proof
    cT
    cW
    wcel
    #
    cR
    cV
    cmap
    co
    #
    cR
    cR
    cmap
    co
    #
    cS
    @1
    cres
    #
    wf
    vf
    cv
    #
    @3
    cfv
    #
    vg
    cv
    #
    @3
    cfv
    #
    wceq
    #
    @4
    @6
    wceq
    #
    wi
    #
    vg
    @1
    wral
    vf
    @1
    wral
    @1
    @2
    @3
    wf1
    @0
    cR
    cV
    cpm
    co
    #
    @2
    @1
    cS
    cR
    cS
    cT
    cV
    cW
    mrsubvr.v
    mrsubvr.r
    mrsubvr.s
    mrsubff
    @1
    @11
    wss
    @0
    cR
    cV
    mapsspm
    a1i
    fssresd
    @0
    @10
    vf
    vg
    @1
    @1
    @0
    @4
    @1
    wcel
    #
    @6
    @1
    wcel
    #
    wa
    #
    wa
    #
    @4
    cS
    cfv
    #
    @6
    cS
    cfv
    #
    wceq
    #
    vv
    cv
    #
    @4
    cfv
    #
    @19
    @6
    cfv
    #
    wceq
    #
    vv
    cV
    wral
    #
    @8
    @9
    @15
    @18
    @22
    vv
    cV
    @18
    @19
    cs1
    #
    @16
    cfv
    #
    @24
    @17
    cfv
    #
    wceq
    @15
    @19
    cV
    wcel
    #
    wa
    #
    @22
    @24
    @16
    @17
    fveq1
    @28
    @25
    @20
    @26
    @21
    @28
    cV
    cR
    @4
    wf
    #
    cV
    cV
    wss
    #
    @27
    @25
    @20
    wceq
    @28
    @12
    @29
    @0
    @12
    @13
    @27
    simplrl
    @4
    cR
    cV
    elmapi
    #
    syl
    @30
    @28
    cV
    ssid
    a1i
    #
    @15
    @27
    simpr
    #
    cV
    cR
    cS
    cT
    @4
    cV
    @19
    mrsubvr.v
    mrsubvr.r
    mrsubvr.s
    mrsubvr
    syl3anc
    @28
    cV
    cR
    @6
    wf
    #
    @30
    @27
    @26
    @21
    wceq
    @28
    @13
    @34
    @0
    @12
    @13
    @27
    simplrr
    @6
    cR
    cV
    elmapi
    #
    syl
    @32
    @33
    cV
    cR
    cS
    cT
    @6
    cV
    @19
    mrsubvr.v
    mrsubvr.r
    mrsubvr.s
    mrsubvr
    syl3anc
    eqeq12d
    syl5ib
    ralrimdva
    @14
    @8
    @18
    wb
    @0
    @12
    @13
    @5
    @16
    @7
    @17
    @4
    @1
    cS
    fvres
    @6
    @1
    cS
    fvres
    eqeqan12d
    adantl
    @14
    @9
    @23
    wb
    #
    @0
    @12
    @29
    @34
    @36
    @13
    @31
    @35
    @29
    @4
    cV
    wfn
    @6
    cV
    wfn
    @36
    @34
    cV
    cR
    @4
    ffn
    cV
    cR
    @6
    ffn
    vv
    cV
    @4
    @6
    eqfnfv
    syl2an
    syl2an
    adantl
    3imtr4d
    ralrimivva
    vf
    vg
    @1
    @2
    @3
    dff13
    sylanbrc
end
