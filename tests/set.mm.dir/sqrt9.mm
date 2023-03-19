include "c3.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "c9.mm"
include "sq3.mm"
include "fveq2i.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "3re.mm"
include "0re.mm"
include "3pos.mm"
include "ltleii.mm"
include "sqrtsq.mm"
include "mp2an.mm"
include "eqtr3i.mm"

theorem sqrt9



  assert |- ( sqrt ` 9 ) = 3

  proof
    c3
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    c9
    csqrt
    cfv
    c3
    @0
    c9
    csqrt
    sq3
    fveq2i
    c3
    cr
    wcel
    cc0
    c3
    cle
    wbr
    @1
    c3
    wceq
    3re
    cc0
    c3
    0re
    3re
    3pos
    ltleii
    c3
    sqrtsq
    mp2an
    eqtr3i
end
