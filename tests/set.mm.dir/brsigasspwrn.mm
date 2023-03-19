include "cbrsiga.mm"
include "cr.mm"
include "csiga.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "brsigarn.mm"
include "sigasspw.mm"
include "ax-mp.mm"

theorem brsigasspwrn



  assert |- BrSiga C_ ~P RR

  proof
    cbrsiga
    cr
    csiga
    cfv
    wcel
    cbrsiga
    cr
    cpw
    wss
    brsigarn
    cr
    cbrsiga
    sigasspw
    ax-mp
end
