include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cdif.mm"
include "cs1.mm"
include "wfun.mm"
include "cima.mm"
include "cvv.mm"
include "cpm.mm"
include "wf.mm"
include "c0.mm"
include "n0i.mm"
include "wn.mm"
include "cmrsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "mrsubff.mm"
include "ffun.mm"
include "3syl.mm"
include "mrsubrn.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "fvelima.mm"
include "syl2anc.mm"
include "wa.mm"
include "cif.mm"
include "wss.mm"
include "cun.mm"
include "elmapi.mm"
include "adantl.mm"
include "ssid.mm"
include "a1i.mm"
include "eldifi.mm"
include "elun1.mm"
include "syl.mm"
include "adantr.mm"
include "mrsubcv.mm"
include "syl3anc.mm"
include "eldifn.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpan9.mm"

theorem mrsubcn
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cV: class V
  let cX: class X
  let vc: setvar c
  let vf: setvar f
  let vr: setvar r
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cW: class W
  let cY: class Y
  assume mrsubccat.s: |- S = ( mRSubst ` T )
  assume mrsubccat.r: |- R = ( mREx ` T )
  assume mrsubcn.v: |- V = ( mVR ` T )
  assume mrsubcn.c: |- C = ( mCN ` T )


  assert |- ( ( F e. ran S /\ X e. ( C \ V ) ) -> ( F ` <" X "> ) = <" X "> )

  proof
    cF
    cS
    crn
    #
    wcel
    #
    vf
    cv
    #
    cS
    cfv
    #
    cF
    wceq
    #
    vf
    cR
    cV
    cmap
    co
    #
    wrex
    #
    cX
    cC
    cV
    cdif
    wcel
    #
    cX
    cs1
    #
    cF
    cfv
    #
    @8
    wceq
    #
    @1
    cS
    wfun
    #
    cF
    cS
    @5
    cima
    #
    wcel
    #
    @6
    @1
    cT
    cvv
    wcel
    #
    cR
    cV
    cpm
    co
    #
    cR
    cR
    cmap
    co
    #
    cS
    wf
    @11
    @1
    @0
    c0
    wceq
    @14
    @0
    cF
    n0i
    @14
    wn
    #
    @0
    c0
    crn
    c0
    @17
    cS
    c0
    @17
    cS
    cT
    cmrsub
    cfv
    c0
    mrsubccat.s
    cT
    cmrsub
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    nsyl2
    cR
    cS
    cT
    cV
    cvv
    mrsubcn.v
    mrsubccat.r
    mrsubccat.s
    mrsubff
    @15
    @16
    cS
    ffun
    3syl
    @1
    @13
    @0
    @12
    cF
    cR
    cS
    cT
    cV
    mrsubcn.v
    mrsubccat.r
    mrsubccat.s
    mrsubrn
    eleq2i
    biimpi
    vf
    cF
    @5
    cS
    fvelima
    syl2anc
    @7
    @4
    @10
    vf
    @5
    @7
    @2
    @5
    wcel
    #
    wa
    #
    @8
    @3
    cfv
    #
    @8
    wceq
    @4
    @10
    @19
    @20
    cX
    cV
    wcel
    #
    cX
    @2
    cfv
    #
    @8
    cif
    #
    @8
    @19
    cV
    cR
    @2
    wf
    #
    cV
    cV
    wss
    #
    cX
    cC
    cV
    cun
    wcel
    #
    @20
    @23
    wceq
    @18
    @24
    @7
    @2
    cR
    cV
    elmapi
    adantl
    @25
    @19
    cV
    ssid
    a1i
    @7
    @26
    @18
    @7
    cX
    cC
    wcel
    @26
    cX
    cC
    cV
    eldifi
    cX
    cC
    cV
    elun1
    syl
    adantr
    cV
    cC
    cR
    cS
    cT
    @2
    cV
    cX
    mrsubcn.c
    mrsubcn.v
    mrsubccat.r
    mrsubccat.s
    mrsubcv
    syl3anc
    @19
    @21
    @22
    @8
    @7
    @21
    wn
    @18
    cX
    cC
    cV
    eldifn
    adantr
    iffalsed
    eqtrd
    @4
    @20
    @9
    @8
    @8
    @3
    cF
    fveq1
    eqeq1d
    syl5ibcom
    rexlimdva
    mpan9
end
