include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "cpsmet.mm"
include "metxmet.mm"
include "xmetpsmet.mm"
include "syl.mm"

theorem metpsmet
  let cD: class D
  let cX: class X


  assert |- ( D e. ( Met ` X ) -> D e. ( PsMet ` X ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    cD
    cX
    cxmt
    cfv
    wcel
    cD
    cX
    cpsmet
    cfv
    wcel
    cD
    cX
    metxmet
    cD
    cX
    xmetpsmet
    syl
end
