include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "cfn.mm"
include "csdm.mm"
include "wbr.mm"
include "wb.mm"
include "omex.mm"
include "isfiniteg.mm"
include "ax-mp.mm"

theorem isfinite
  let cA: class A


  assert |- ( A e. Fin <-> A ~< _om )

  proof
    com
    cvv
    wcel
    cA
    cfn
    wcel
    cA
    com
    csdm
    wbr
    wb
    omex
    cA
    isfiniteg
    ax-mp
end
