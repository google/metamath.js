include "clo.mm"
include "wcel.mm"
include "c0v.mm"
include "cfv.mm"
include "wceq.mm"
include "lnop0.mm"
include "ax-mp.mm"

theorem lnop0i
  let cT: class T
  assume lnopl.1: |- T e. LinOp


  assert |- ( T ` 0h ) = 0h

  proof
    cT
    clo
    wcel
    c0v
    cT
    cfv
    c0v
    wceq
    lnopl.1
    cT
    lnop0
    ax-mp
end
