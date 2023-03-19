include "cc.mm"
include "cxp.mm"
include "caddc.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "ax-addf.mm"
include "cnex.mm"
include "xpex.mm"
include "fex2.mm"
include "mp3an.mm"

theorem addex



  assert |- + e. _V

  proof
    cc
    cc
    cxp
    #
    cc
    caddc
    wf
    @0
    cvv
    wcel
    cc
    cvv
    wcel
    caddc
    cvv
    wcel
    ax-addf
    cc
    cc
    cnex
    cnex
    xpex
    cnex
    @0
    cc
    caddc
    cvv
    cvv
    fex2
    mp3an
end
