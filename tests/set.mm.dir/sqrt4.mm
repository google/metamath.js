include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "c4.mm"
include "sq2.mm"
include "fveq2i.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "2re.mm"
include "0le2.mm"
include "sqrtsq.mm"
include "mp2an.mm"
include "eqtr3i.mm"

theorem sqrt4



  assert |- ( sqrt ` 4 ) = 2

  proof
    c2
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    c4
    csqrt
    cfv
    c2
    @0
    c4
    csqrt
    sq2
    fveq2i
    c2
    cr
    wcel
    cc0
    c2
    cle
    wbr
    @1
    c2
    wceq
    2re
    0le2
    c2
    sqrtsq
    mp2an
    eqtr3i
end
