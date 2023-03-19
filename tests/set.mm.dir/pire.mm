include "cpi.mm"
include "c2.mm"
include "c4.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "pilem3.mm"
include "simpli.mm"
include "elioore.mm"
include "ax-mp.mm"

theorem pire



  assert |- _pi e. RR

  proof
    cpi
    c2
    c4
    cioo
    co
    wcel
    #
    cpi
    cr
    wcel
    @0
    cpi
    csin
    cfv
    cc0
    wceq
    pilem3
    simpli
    cpi
    c2
    c4
    elioore
    ax-mp
end
