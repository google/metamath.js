include "cc.mm"
include "cxp.mm"
include "cmul.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "ax-mulf.mm"
include "cnex.mm"
include "xpex.mm"
include "fex2.mm"
include "mp3an.mm"

theorem mulex



  assert |- x. e. _V

  proof
    cc
    cc
    cxp
    #
    cc
    cmul
    wf
    @0
    cvv
    wcel
    cc
    cvv
    wcel
    cmul
    cvv
    wcel
    ax-mulf
    cc
    cc
    cnex
    cnex
    xpex
    cnex
    @0
    cc
    cmul
    cvv
    cvv
    fex2
    mp3an
end
