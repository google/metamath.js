include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "1re.mm"
include "reim0.mm"
include "ax-mp.mm"

theorem im1



  assert |- ( Im ` 1 ) = 0

  proof
    c1
    cr
    wcel
    c1
    cim
    cfv
    cc0
    wceq
    1re
    c1
    reim0
    ax-mp
end
