include "c0.mm"
include "cr.mm"
include "wss.mm"
include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "0ss.mm"
include "nnex.mm"
include "0dom.mm"
include "ovolctb2.mm"
include "mp2an.mm"

theorem ovol0



  assert |- ( vol* ` (/) ) = 0

  proof
    c0
    cr
    wss
    c0
    cn
    cdom
    wbr
    c0
    covol
    cfv
    cc0
    wceq
    cr
    0ss
    cn
    nnex
    0dom
    c0
    ovolctb2
    mp2an
end
