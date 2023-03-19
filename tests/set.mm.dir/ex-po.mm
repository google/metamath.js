include "cr.mm"
include "clt.mm"
include "wpo.mm"
include "cle.mm"
include "wn.mm"
include "wor.mm"
include "ltso.mm"
include "sopo.mm"
include "ax-mp.mm"
include "cc0.mm"
include "wbr.mm"
include "0le0.mm"
include "wcel.mm"
include "0re.mm"
include "poirr.mm"
include "mpan2.mm"
include "mt2.mm"
include "pm3.2i.mm"

theorem ex-po



  assert |- ( < Po RR /\ -. <_ Po RR )

  proof
    cr
    clt
    wpo
    #
    cr
    cle
    wpo
    #
    wn
    cr
    clt
    wor
    @0
    ltso
    cr
    clt
    sopo
    ax-mp
    @1
    cc0
    cc0
    cle
    wbr
    #
    0le0
    @1
    cc0
    cr
    wcel
    @2
    wn
    0re
    cr
    cc0
    cle
    poirr
    mpan2
    mt2
    pm3.2i
end
