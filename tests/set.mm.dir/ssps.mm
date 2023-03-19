include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wfun.mm"
include "wfn.mm"
include "wss.mm"
include "w3a.mm"
include "cba.mm"
include "cfv.mm"
include "wf.mm"
include "eqid.mm"
include "nvsf.mm"
include "ffun.mm"
include "syl.mm"
include "funres.mm"
include "adantr.mm"
include "sspnv.mm"
include "ffn.mm"
include "fnresdm.mm"
include "cpv.mm"
include "cnmcv.mm"
include "isssp.mm"
include "simplbda.mm"
include "simp2d.mm"
include "ssres.mm"
include "eqsstr3d.mm"
include "3jca.mm"
include "oprssov.mm"
include "sylan.mm"
include "eqcomd.mm"
include "ralrimivva.mm"
include "jctil.mm"
include "wb.mm"
include "ssid.mm"
include "sspba.mm"
include "xpss12.mm"
include "sylancr.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "eqfnov.mm"
include "mpbird.mm"

theorem ssps
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume ssps.y: |- Y = ( BaseSet ` W )
  assume ssps.s: |- S = ( .sOLD ` U )
  assume ssps.r: |- R = ( .sOLD ` W )
  assume ssps.h: |- H = ( SubSp ` U )


  assert |- ( ( U e. NrmCVec /\ W e. H ) -> R = ( S |` ( CC X. Y ) ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cR
    cS
    cc
    cY
    cxp
    #
    cres
    #
    wceq
    #
    @3
    @3
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    co
    #
    @7
    @8
    @4
    co
    #
    wceq
    #
    vy
    cY
    wral
    vx
    cc
    wral
    #
    wa
    #
    @2
    @12
    @6
    @2
    @11
    vx
    vy
    cc
    cY
    @2
    @7
    cc
    wcel
    @8
    cY
    wcel
    wa
    #
    wa
    @10
    @9
    @2
    @4
    wfun
    #
    cR
    @3
    wfn
    #
    cR
    @4
    wss
    #
    w3a
    @14
    @10
    @9
    wceq
    @2
    @15
    @16
    @17
    @0
    @15
    @1
    @0
    cS
    wfun
    #
    @15
    @0
    cc
    cU
    cba
    cfv
    #
    cxp
    #
    @19
    cS
    wf
    #
    @18
    cS
    cU
    @19
    @19
    eqid
    #
    ssps.s
    nvsf
    #
    @20
    @19
    cS
    ffun
    syl
    @3
    cS
    funres
    syl
    adantr
    @2
    @3
    cY
    cR
    wf
    #
    @16
    @2
    cW
    cnv
    wcel
    #
    @24
    cU
    cH
    cW
    ssps.h
    sspnv
    cR
    cW
    cY
    ssps.y
    ssps.r
    nvsf
    syl
    @3
    cY
    cR
    ffn
    syl
    #
    @2
    cR
    cR
    @3
    cres
    #
    @4
    @2
    @16
    @27
    cR
    wceq
    @26
    @3
    cR
    fnresdm
    syl
    @2
    cR
    cS
    wss
    #
    @27
    @4
    wss
    @2
    cW
    cpv
    cfv
    #
    cU
    cpv
    cfv
    #
    wss
    #
    @28
    cW
    cnmcv
    cfv
    #
    cU
    cnmcv
    cfv
    #
    wss
    #
    @0
    @1
    @25
    @31
    @28
    @34
    w3a
    cR
    cS
    cU
    @29
    @30
    cH
    @32
    @33
    cW
    @30
    eqid
    @29
    eqid
    ssps.s
    ssps.r
    @33
    eqid
    @32
    eqid
    ssps.h
    isssp
    simplbda
    simp2d
    cR
    cS
    @3
    ssres
    syl
    eqsstr3d
    3jca
    @7
    @8
    cc
    cY
    @4
    cR
    oprssov
    sylan
    eqcomd
    ralrimivva
    @3
    eqid
    jctil
    @2
    @16
    @4
    @3
    wfn
    #
    @5
    @13
    wb
    @26
    @2
    cS
    @20
    wfn
    #
    @3
    @20
    wss
    #
    @35
    @0
    @36
    @1
    @0
    @21
    @36
    @23
    @20
    @19
    cS
    ffn
    syl
    adantr
    @2
    cc
    cc
    wss
    cY
    @19
    wss
    @37
    cc
    ssid
    cU
    cH
    cW
    @19
    cY
    @22
    ssps.y
    ssps.h
    sspba
    cc
    cc
    cY
    @19
    xpss12
    sylancr
    @20
    @3
    cS
    fnssres
    syl2anc
    vx
    vy
    cc
    cY
    cc
    cY
    cR
    @4
    eqfnov
    syl2anc
    mpbird
end
