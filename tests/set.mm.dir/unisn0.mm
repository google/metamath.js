include "c0.mm"
include "csn.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "ssid.mm"
include "uni0b.mm"
include "mpbir.mm"

theorem unisn0



  assert |- U. { (/) } = (/)

  proof
    c0
    csn
    #
    cuni
    c0
    wceq
    @0
    @0
    wss
    @0
    ssid
    @0
    uni0b
    mpbir
end
