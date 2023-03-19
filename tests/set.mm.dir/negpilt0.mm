include "cc0.mm"
include "cpi.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "pipos.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "pire.mm"
include "lt0neg2.mm"
include "ax-mp.mm"
include "mpbi.mm"

theorem negpilt0



  assert |- -u _pi < 0

  proof
    cc0
    cpi
    clt
    wbr
    #
    cpi
    cneg
    cc0
    clt
    wbr
    #
    pipos
    cpi
    cr
    wcel
    @0
    @1
    wb
    pire
    cpi
    lt0neg2
    ax-mp
    mpbi
end
