include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "cfn.mm"
include "csdm.mm"
include "wbr.mm"
include "cv.mm"
include "cen.mm"
include "wrex.mm"
include "isfi.mm"
include "wa.mm"
include "nnsdomg.mm"
include "sdomen1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "isfinite2.mm"
include "impbid1.mm"

theorem isfiniteg
  let cA: class A
  let vx: setvar x


  assert |- ( _om e. _V -> ( A e. Fin <-> A ~< _om ) )

  proof
    com
    cvv
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    com
    csdm
    wbr
    #
    @1
    cA
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    @0
    @2
    vx
    cA
    isfi
    @0
    @4
    @2
    vx
    com
    @0
    @3
    com
    wcel
    wa
    @2
    @4
    @3
    com
    csdm
    wbr
    @3
    nnsdomg
    cA
    @3
    com
    sdomen1
    syl5ibrcom
    rexlimdva
    syl5bi
    cA
    isfinite2
    impbid1
end
