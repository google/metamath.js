include "cc0.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "ceu.mm"
include "2pos.mm"
include "c3.mm"
include "egt2lt3.mm"
include "simpli.mm"
include "0re.mm"
include "2re.mm"
include "ere.mm"
include "lttri.mm"
include "mp2an.mm"

theorem epos



  assert |- 0 < _e

  proof
    cc0
    c2
    clt
    wbr
    c2
    ceu
    clt
    wbr
    #
    cc0
    ceu
    clt
    wbr
    2pos
    @0
    ceu
    c3
    clt
    wbr
    egt2lt3
    simpli
    cc0
    c2
    ceu
    0re
    2re
    ere
    lttri
    mp2an
end
