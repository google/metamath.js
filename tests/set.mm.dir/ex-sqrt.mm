include "c5.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cdc.mm"
include "wceq.mm"
include "c3.mm"
include "cneg.mm"
include "c1.mm"
include "c9.mm"
include "cdiv.mm"
include "ex-exp.mm"
include "simpli.mm"
include "fveq2i.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "5re.mm"
include "0re.mm"
include "5pos.mm"
include "ltleii.mm"
include "sqrtsq.mm"
include "mp2an.mm"
include "eqtr3i.mm"

theorem ex-sqrt



  assert |- ( sqrt ` ; 2 5 ) = 5

  proof
    c5
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    c2
    c5
    cdc
    #
    csqrt
    cfv
    c5
    @0
    @2
    csqrt
    @0
    @2
    wceq
    c3
    cneg
    c2
    cneg
    cexp
    co
    c1
    c9
    cdiv
    co
    wceq
    ex-exp
    simpli
    fveq2i
    c5
    cr
    wcel
    cc0
    c5
    cle
    wbr
    @1
    c5
    wceq
    5re
    cc0
    c5
    0re
    5re
    5pos
    ltleii
    c5
    sqrtsq
    mp2an
    eqtr3i
end
