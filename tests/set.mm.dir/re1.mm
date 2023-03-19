include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "1re.mm"
include "rere.mm"
include "ax-mp.mm"

theorem re1



  assert |- ( Re ` 1 ) = 1

  proof
    c1
    cr
    wcel
    c1
    cre
    cfv
    c1
    wceq
    1re
    c1
    rere
    ax-mp
end
