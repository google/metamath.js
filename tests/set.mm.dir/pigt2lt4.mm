include "cpi.mm"
include "c2.mm"
include "c4.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "pilem3.mm"
include "simpli.mm"
include "eliooord.mm"
include "ax-mp.mm"

theorem pigt2lt4



  assert |- ( 2 < _pi /\ _pi < 4 )

  proof
    cpi
    c2
    c4
    cioo
    co
    wcel
    #
    c2
    cpi
    clt
    wbr
    cpi
    c4
    clt
    wbr
    wa
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
    eliooord
    ax-mp
end
