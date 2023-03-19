include "c0.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "cwlks.mm"
include "vtxval0.mm"
include "g0wlk0.mm"
include "ax-mp.mm"

theorem 0wlk0



  assert |- ( Walks ` (/) ) = (/)

  proof
    c0
    cvtx
    cfv
    c0
    wceq
    c0
    cwlks
    cfv
    c0
    wceq
    vtxval0
    c0
    g0wlk0
    ax-mp
end
