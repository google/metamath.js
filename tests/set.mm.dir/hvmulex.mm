include "cc.mm"
include "chil.mm"
include "cxp.mm"
include "csm.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "ax-hfvmul.mm"
include "cnex.mm"
include "ax-hilex.mm"
include "xpex.mm"
include "fex.mm"
include "mp2an.mm"

theorem hvmulex



  assert |- .h e. _V

  proof
    cc
    chil
    cxp
    #
    chil
    csm
    wf
    @0
    cvv
    wcel
    csm
    cvv
    wcel
    ax-hfvmul
    cc
    chil
    cnex
    ax-hilex
    xpex
    @0
    chil
    cvv
    csm
    fex
    mp2an
end
