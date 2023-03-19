include "cxr.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "letopon.mm"
include "topontopi.mm"

theorem letop



  assert |- ( ordTop ` <_ ) e. Top

  proof
    cxr
    cle
    cordt
    cfv
    letopon
    topontopi
end
