include "cpi.mm"
include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "picn.mm"
include "2halves.mm"
include "ax-mp.mm"

theorem pidiv2halves



  assert |- ( ( _pi / 2 ) + ( _pi / 2 ) ) = _pi

  proof
    cpi
    cc
    wcel
    cpi
    c2
    cdiv
    co
    #
    @0
    caddc
    co
    cpi
    wceq
    picn
    cpi
    2halves
    ax-mp
end
