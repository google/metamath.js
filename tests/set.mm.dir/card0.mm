include "c0.mm"
include "ccrd.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "con0.mm"
include "wcel.mm"
include "0elon.mm"
include "cardonle.mm"
include "ax-mp.mm"
include "ss0b.mm"
include "mpbi.mm"

theorem card0



  assert |- ( card ` (/) ) = (/)

  proof
    c0
    ccrd
    cfv
    #
    c0
    wss
    #
    @0
    c0
    wceq
    c0
    con0
    wcel
    @1
    0elon
    c0
    cardonle
    ax-mp
    @0
    ss0b
    mpbi
end
