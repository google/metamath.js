include "cc.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "csqrt.mm"
include "cabs.mm"
include "df-abs.mm"
include "wcel.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "cr.mm"
include "absval.mm"
include "abscl.mm"
include "eqeltrrd.mm"
include "rexrd.mm"
include "cle.mm"
include "wbr.mm"
include "cjmulrcl.mm"
include "cjmulge0.mm"
include "sqrtge0.mm"
include "syl2anc.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "fmpti.mm"

theorem absfico
  let vx: setvar x


  assert |- abs : CC --> ( 0 [,) +oo )

  proof
    vx
    cc
    cc0
    cpnf
    cico
    co
    vx
    cv
    #
    @0
    ccj
    cfv
    cmul
    co
    #
    csqrt
    cfv
    #
    cabs
    vx
    df-abs
    @0
    cc
    wcel
    #
    cc0
    cpnf
    @2
    cc0
    cxr
    wcel
    @3
    0xr
    a1i
    cpnf
    cxr
    wcel
    @3
    pnfxr
    a1i
    @3
    @2
    @3
    @0
    cabs
    cfv
    @2
    cr
    @0
    absval
    @0
    abscl
    eqeltrrd
    #
    rexrd
    @3
    @1
    cr
    wcel
    cc0
    @1
    cle
    wbr
    cc0
    @2
    cle
    wbr
    @0
    cjmulrcl
    @0
    cjmulge0
    @1
    sqrtge0
    syl2anc
    @3
    @2
    @4
    ltpnfd
    elicod
    fmpti
end
