include "clo.mm"
include "wcel.mm"
include "cnop.mm"
include "cfv.mm"
include "cc0.mm"
include "ch0o.mm"
include "nmlnop0.mm"
include "necon3bid.mm"

theorem nmlnopne0
  let cT: class T


  assert |- ( T e. LinOp -> ( ( normop ` T ) =/= 0 <-> T =/= 0hop ) )

  proof
    cT
    clo
    wcel
    cT
    cnop
    cfv
    cc0
    cT
    ch0o
    cT
    nmlnop0
    necon3bid
end
