include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "sq1.mm"
include "fveq2i.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "1re.mm"
include "0le1.mm"
include "sqrtsq.mm"
include "mp2an.mm"
include "eqtr3i.mm"

theorem sqrt1



  assert |- ( sqrt ` 1 ) = 1

  proof
    c1
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    c1
    csqrt
    cfv
    c1
    @0
    c1
    csqrt
    sq1
    fveq2i
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @1
    c1
    wceq
    1re
    0le1
    c1
    sqrtsq
    mp2an
    eqtr3i
end
