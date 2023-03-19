include "cr.mm"
include "cq.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cdom.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "nnexALT.mm"
include "qexALT.mm"
include "rpnnen1.mm"
include "reldom.mm"
include "brrelexi.mm"
include "ax-mp.mm"

theorem reexALT



  assert |- RR e. _V

  proof
    cr
    cq
    cn
    cmap
    co
    #
    cdom
    wbr
    cr
    cvv
    wcel
    nnexALT
    qexALT
    rpnnen1
    cr
    @0
    cdom
    reldom
    brrelexi
    ax-mp
end
