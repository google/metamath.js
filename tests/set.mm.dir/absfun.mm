include "cc.mm"
include "cr.mm"
include "cabs.mm"
include "wf.mm"
include "wfun.mm"
include "absf.mm"
include "ffun.mm"
include "ax-mp.mm"

theorem absfun



  assert |- Fun abs

  proof
    cc
    cr
    cabs
    wf
    cabs
    wfun
    absf
    cc
    cr
    cabs
    ffun
    ax-mp
end
