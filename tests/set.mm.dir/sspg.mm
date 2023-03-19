include "cnv.mm"
include "wcel.mm"
include "wa.mm"
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
include "nvgf.mm"
include "ffun.mm"
include "syl.mm"
include "funres.mm"
include "adantr.mm"
include "sspnv.mm"
include "ffn.mm"
include "fnresdm.mm"
include "cns.mm"
include "cnmcv.mm"
include "isssp.mm"
include "simplbda.mm"
include "simp1d.mm"
include "ssres.mm"
include "eqsstr3d.mm"
include "3jca.mm"
include "oprssov.mm"
include "sylan.mm"
include "eqcomd.mm"
include "ralrimivva.mm"
include "jctil.mm"
include "wb.mm"
include "sspba.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fnssres.mm"
include "eqfnov.mm"
include "mpbird.mm"

theorem sspg
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume sspg.y: |- Y = ( BaseSet ` W )
  assume sspg.g: |- G = ( +v ` U )
  assume sspg.f: |- F = ( +v ` W )
  assume sspg.h: |- H = ( SubSp ` U )


  assert |- ( ( U e. NrmCVec /\ W e. H ) -> F = ( G |` ( Y X. Y ) ) )

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
    cF
    cG
    cY
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
    cF
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
    cY
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
    cY
    cY
    @2
    @7
    cY
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
    cF
    @3
    wfn
    #
    cF
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
    cG
    wfun
    #
    @15
    @0
    cU
    cba
    cfv
    #
    @19
    cxp
    #
    @19
    cG
    wf
    #
    @18
    cU
    cG
    @19
    @19
    eqid
    #
    sspg.g
    nvgf
    #
    @20
    @19
    cG
    ffun
    syl
    @3
    cG
    funres
    syl
    adantr
    @2
    @3
    cY
    cF
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
    sspg.h
    sspnv
    cW
    cF
    cY
    sspg.y
    sspg.f
    nvgf
    syl
    @3
    cY
    cF
    ffn
    syl
    #
    @2
    cF
    cF
    @3
    cres
    #
    @4
    @2
    @16
    @27
    cF
    wceq
    @26
    @3
    cF
    fnresdm
    syl
    @2
    cF
    cG
    wss
    #
    @27
    @4
    wss
    @2
    @28
    cW
    cns
    cfv
    #
    cU
    cns
    cfv
    #
    wss
    #
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
    @28
    @31
    @34
    w3a
    @29
    @30
    cU
    cF
    cG
    cH
    @32
    @33
    cW
    sspg.g
    sspg.f
    @30
    eqid
    @29
    eqid
    @33
    eqid
    @32
    eqid
    sspg.h
    isssp
    simplbda
    simp1d
    cF
    cG
    @3
    ssres
    syl
    eqsstr3d
    3jca
    @7
    @8
    cY
    cY
    @4
    cF
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
    cG
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
    cG
    ffn
    syl
    adantr
    @2
    cY
    @19
    wss
    #
    @38
    @37
    cU
    cH
    cW
    @19
    cY
    @22
    sspg.y
    sspg.h
    sspba
    #
    @39
    cY
    @19
    cY
    @19
    xpss12
    syl2anc
    @20
    @3
    cG
    fnssres
    syl2anc
    vx
    vy
    cY
    cY
    cY
    cY
    cF
    @4
    eqfnov
    syl2anc
    mpbird
end
