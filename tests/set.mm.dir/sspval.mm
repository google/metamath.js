include "cnv.mm"
include "wcel.mm"
include "css.mm"
include "cfv.mm"
include "cv.mm"
include "cpv.mm"
include "wss.mm"
include "cns.mm"
include "cnmcv.mm"
include "w3a.mm"
include "crab.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sseq2d.mm"
include "3anbi123d.mm"
include "rabbidv.mm"
include "df-ssp.mm"
include "cpw.mm"
include "cxp.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "xpex.mm"
include "wi.mm"
include "rabss.mm"
include "cop.mm"
include "wa.mm"
include "elpw.mm"
include "opelxpi.mm"
include "syl2anbr.mm"
include "biimpri.mm"
include "syl2an.mm"
include "3impa.mm"
include "eqid.mm"
include "nvop.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "mprgbir.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl5eq.mm"

theorem sspval
  let vw: setvar w
  let cS: class S
  let cU: class U
  let cG: class G
  let cH: class H
  let cN: class N
  let vu: setvar u
  assume sspval.g: |- G = ( +v ` U )
  assume sspval.s: |- S = ( .sOLD ` U )
  assume sspval.n: |- N = ( normCV ` U )
  assume sspval.h: |- H = ( SubSp ` U )

  disjoint G w
  disjoint N w
  disjoint S w
  disjoint U w
  disjoint u w
  disjoint G u
  disjoint N u
  disjoint S u
  disjoint U u
  assert |- ( U e. NrmCVec -> H = { w e. NrmCVec | ( ( +v ` w ) C_ G /\ ( .sOLD ` w ) C_ S /\ ( normCV ` w ) C_ N ) } )

  proof
    cU
    cnv
    wcel
    cH
    cU
    css
    cfv
    vw
    cv
    #
    cpv
    cfv
    #
    cG
    wss
    #
    @0
    cns
    cfv
    #
    cS
    wss
    #
    @0
    cnmcv
    cfv
    #
    cN
    wss
    #
    w3a
    #
    vw
    cnv
    crab
    #
    sspval.h
    vu
    cU
    @1
    vu
    cv
    #
    cpv
    cfv
    #
    wss
    #
    @3
    @9
    cns
    cfv
    #
    wss
    #
    @5
    @9
    cnmcv
    cfv
    #
    wss
    #
    w3a
    #
    vw
    cnv
    crab
    @8
    cnv
    css
    @9
    cU
    wceq
    #
    @16
    @7
    vw
    cnv
    @17
    @11
    @2
    @13
    @4
    @15
    @6
    @17
    @10
    cG
    @1
    @17
    @10
    cU
    cpv
    cfv
    #
    cG
    @9
    cU
    cpv
    fveq2
    sspval.g
    syl6eqr
    sseq2d
    @17
    @12
    cS
    @3
    @17
    @12
    cU
    cns
    cfv
    #
    cS
    @9
    cU
    cns
    fveq2
    sspval.s
    syl6eqr
    sseq2d
    @17
    @14
    cN
    @5
    @17
    @14
    cU
    cnmcv
    cfv
    #
    cN
    @9
    cU
    cnmcv
    fveq2
    sspval.n
    syl6eqr
    sseq2d
    3anbi123d
    rabbidv
    vw
    vu
    df-ssp
    @8
    cG
    cpw
    #
    cS
    cpw
    #
    cxp
    #
    cN
    cpw
    #
    cxp
    #
    @23
    @24
    @21
    @22
    cG
    cG
    @18
    cvv
    sspval.g
    cU
    cpv
    fvex
    eqeltri
    pwex
    cS
    cS
    @19
    cvv
    sspval.s
    cU
    cns
    fvex
    eqeltri
    pwex
    xpex
    cN
    cN
    @20
    cvv
    sspval.n
    cU
    cnmcv
    fvex
    eqeltri
    pwex
    xpex
    @8
    @25
    wss
    @7
    @0
    @25
    wcel
    #
    wi
    vw
    cnv
    @7
    vw
    cnv
    @25
    rabss
    @7
    @26
    @0
    cnv
    wcel
    #
    @1
    @3
    cop
    #
    @5
    cop
    #
    @25
    wcel
    #
    @2
    @4
    @6
    @30
    @2
    @4
    wa
    @28
    @23
    wcel
    #
    @5
    @24
    wcel
    #
    @30
    @6
    @2
    @1
    @21
    wcel
    @3
    @22
    wcel
    @31
    @4
    @1
    cG
    @0
    cpv
    fvex
    elpw
    @3
    cS
    @0
    cns
    fvex
    elpw
    @1
    @3
    @21
    @22
    opelxpi
    syl2anbr
    @32
    @6
    @5
    cN
    @0
    cnmcv
    fvex
    elpw
    biimpri
    @28
    @5
    @23
    @24
    opelxpi
    syl2an
    3impa
    @27
    @0
    @29
    @25
    @3
    @0
    @1
    @5
    @1
    eqid
    @3
    eqid
    @5
    eqid
    nvop
    eleq1d
    syl5ibr
    mprgbir
    ssexi
    fvmpt
    syl5eq
end
