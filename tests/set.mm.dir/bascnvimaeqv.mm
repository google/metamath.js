include "cbs.mm"
include "cvv.mm"
include "wfn.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "c1.mm"
include "df-base.mm"
include "slotfn.mm"
include "fncnvimaeqv.mm"
include "ax-mp.mm"

theorem bascnvimaeqv



  assert |- ( `' Base " _V ) = _V

  proof
    cbs
    cvv
    wfn
    cbs
    ccnv
    cvv
    cima
    cvv
    wceq
    cbs
    c1
    df-base
    slotfn
    cbs
    fncnvimaeqv
    ax-mp
end
