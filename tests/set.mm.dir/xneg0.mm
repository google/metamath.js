include "cc0.mm"
include "cxne.mm"
include "cneg.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "0re.mm"
include "rexneg.mm"
include "ax-mp.mm"
include "neg0.mm"
include "eqtri.mm"

theorem xneg0



  assert |- -e 0 = 0

  proof
    cc0
    cxne
    #
    cc0
    cneg
    #
    cc0
    cc0
    cr
    wcel
    @0
    @1
    wceq
    0re
    cc0
    rexneg
    ax-mp
    neg0
    eqtri
end
