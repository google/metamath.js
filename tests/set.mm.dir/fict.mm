include "cfn.mm"
include "wcel.mm"
include "com.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "isfinite.mm"
include "sdomdom.mm"
include "sylbi.mm"

theorem fict
  let cA: class A


  assert |- ( A e. Fin -> A ~<_ _om )

  proof
    cA
    cfn
    wcel
    cA
    com
    csdm
    wbr
    cA
    com
    cdom
    wbr
    cA
    isfinite
    cA
    com
    sdomdom
    sylbi
end
