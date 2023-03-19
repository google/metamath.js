include "cfin4.mm"
include "cfn.mm"
include "cv.mm"
include "com.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "wn.mm"
include "wcel.mm"
include "vex.mm"
include "domtriom.mm"
include "con2bii.mm"
include "isfinite.mm"
include "cvv.mm"
include "wb.mm"
include "isfin4-2.mm"
include "ax-mp.mm"
include "3bitr4ri.mm"
include "eqriv.mm"

theorem fin41
  let vx: setvar x


  assert |- Fin4 = Fin

  proof
    vx
    cfin4
    cfn
    vx
    cv
    #
    com
    csdm
    wbr
    #
    com
    @0
    cdom
    wbr
    #
    wn
    #
    @0
    cfn
    wcel
    @0
    cfin4
    wcel
    #
    @2
    @1
    @0
    vx
    vex
    #
    domtriom
    con2bii
    @0
    isfinite
    @0
    cvv
    wcel
    @4
    @3
    wb
    @5
    @0
    cvv
    isfin4-2
    ax-mp
    3bitr4ri
    eqriv
end
