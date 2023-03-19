include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "wceq.mm"
include "0re.mm"
include "reim0.mm"
include "ax-mp.mm"

theorem im0



  assert |- ( Im ` 0 ) = 0

  proof
    cc0
    cr
    wcel
    cc0
    cim
    cfv
    cc0
    wceq
    0re
    cc0
    reim0
    ax-mp
end
