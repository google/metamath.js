include "clo.mm"
include "ccop.mm"
include "cin.mm"
include "cbo.mm"
include "cv.mm"
include "lncnopbd.mm"
include "eqriv.mm"

theorem lncnbd
  let vt: setvar t


  assert |- ( LinOp i^i ContOp ) = BndLinOp

  proof
    vt
    clo
    ccop
    cin
    cbo
    vt
    cv
    lncnopbd
    eqriv
end
