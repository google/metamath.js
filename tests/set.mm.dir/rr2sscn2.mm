include "cr.mm"
include "cc.mm"
include "wss.mm"
include "cxp.mm"
include "ax-resscn.mm"
include "xpss12.mm"
include "mp2an.mm"

theorem rr2sscn2



  assert |- ( RR X. RR ) C_ ( CC X. CC )

  proof
    cr
    cc
    wss
    #
    @0
    cr
    cr
    cxp
    cc
    cc
    cxp
    wss
    ax-resscn
    ax-resscn
    cr
    cc
    cr
    cc
    xpss12
    mp2an
end
