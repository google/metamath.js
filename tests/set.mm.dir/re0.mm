include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "0re.mm"
include "rere.mm"
include "ax-mp.mm"

theorem re0



  assert |- ( Re ` 0 ) = 0

  proof
    cc0
    cr
    wcel
    cc0
    cre
    cfv
    cc0
    wceq
    0re
    cc0
    rere
    ax-mp
end
