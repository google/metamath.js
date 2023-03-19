include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "0re.mm"
include "cjre.mm"
include "ax-mp.mm"

theorem cj0



  assert |- ( * ` 0 ) = 0

  proof
    cc0
    cr
    wcel
    cc0
    ccj
    cfv
    cc0
    wceq
    0re
    cc0
    cjre
    ax-mp
end
