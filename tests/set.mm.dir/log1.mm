include "c1.mm"
include "clog.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "ce.mm"
include "ef0.mm"
include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "wb.mm"
include "1rp.mm"
include "0re.mm"
include "relogeftb.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem log1



  assert |- ( log ` 1 ) = 0

  proof
    c1
    clog
    cfv
    cc0
    wceq
    #
    cc0
    ce
    cfv
    c1
    wceq
    #
    ef0
    c1
    crp
    wcel
    cc0
    cr
    wcel
    @0
    @1
    wb
    1rp
    0re
    c1
    cc0
    relogeftb
    mp2an
    mpbir
end
