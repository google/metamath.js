include "cr.mm"
include "cxr.mm"
include "wss.mm"
include "cxp.mm"
include "ressxr.mm"
include "xpss12.mm"
include "mp2an.mm"

theorem rexpssxrxp



  assert |- ( RR X. RR ) C_ ( RR* X. RR* )

  proof
    cr
    cxr
    wss
    #
    @0
    cr
    cr
    cxp
    cxr
    cxr
    cxp
    wss
    ressxr
    ressxr
    cr
    cxr
    cr
    cxr
    xpss12
    mp2an
end
