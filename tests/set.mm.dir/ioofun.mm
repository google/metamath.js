include "cxr.mm"
include "cxp.mm"
include "cr.mm"
include "cpw.mm"
include "cioo.mm"
include "wf.mm"
include "wfun.mm"
include "ioof.mm"
include "ffun.mm"
include "ax-mp.mm"

theorem ioofun



  assert |- Fun (,)

  proof
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    cioo
    wfun
    ioof
    @0
    @1
    cioo
    ffun
    ax-mp
end
