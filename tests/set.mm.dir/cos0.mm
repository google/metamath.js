include "cc0.mm"
include "ccos.mm"
include "cfv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cre.mm"
include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "0re.mm"
include "recosval.mm"
include "ax-mp.mm"
include "it0e0.mm"
include "fveq2i.mm"
include "ef0.mm"
include "eqtri.mm"
include "re1.mm"

theorem cos0



  assert |- ( cos ` 0 ) = 1

  proof
    cc0
    ccos
    cfv
    #
    ci
    cc0
    cmul
    co
    #
    ce
    cfv
    #
    cre
    cfv
    #
    c1
    cc0
    cr
    wcel
    @0
    @3
    wceq
    0re
    cc0
    recosval
    ax-mp
    @3
    c1
    cre
    cfv
    c1
    @2
    c1
    cre
    @2
    cc0
    ce
    cfv
    c1
    @1
    cc0
    ce
    it0e0
    fveq2i
    ef0
    eqtri
    fveq2i
    re1
    eqtri
    eqtri
end
