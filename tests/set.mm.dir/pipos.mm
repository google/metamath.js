include "cc0.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "cpi.mm"
include "2pos.mm"
include "c4.mm"
include "pigt2lt4.mm"
include "simpli.mm"
include "0re.mm"
include "2re.mm"
include "pire.mm"
include "lttri.mm"
include "mp2an.mm"

theorem pipos



  assert |- 0 < _pi

  proof
    cc0
    c2
    clt
    wbr
    c2
    cpi
    clt
    wbr
    #
    cc0
    cpi
    clt
    wbr
    2pos
    @0
    cpi
    c4
    clt
    wbr
    pigt2lt4
    simpli
    cc0
    c2
    cpi
    0re
    2re
    pire
    lttri
    mp2an
end
