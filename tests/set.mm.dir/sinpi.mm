include "cpi.mm"
include "c2.mm"
include "c4.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "pilem3.mm"
include "simpri.mm"

theorem sinpi



  assert |- ( sin ` _pi ) = 0

  proof
    cpi
    c2
    c4
    cioo
    co
    wcel
    cpi
    csin
    cfv
    cc0
    wceq
    pilem3
    simpri
end
