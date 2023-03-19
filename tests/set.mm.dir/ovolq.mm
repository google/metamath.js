include "cq.mm"
include "cr.mm"
include "wss.mm"
include "cn.mm"
include "cen.mm"
include "wbr.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "qssre.mm"
include "qnnen.mm"
include "ovolctb.mm"
include "mp2an.mm"

theorem ovolq



  assert |- ( vol* ` QQ ) = 0

  proof
    cq
    cr
    wss
    cq
    cn
    cen
    wbr
    cq
    covol
    cfv
    cc0
    wceq
    qssre
    qnnen
    cq
    ovolctb
    mp2an
end
