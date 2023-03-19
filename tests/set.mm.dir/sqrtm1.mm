include "c1.mm"
include "cneg.mm"
include "csqrt.mm"
include "cfv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "1re.mm"
include "0le1.mm"
include "sqrtneg.mm"
include "mp2an.mm"
include "sqrt1.mm"
include "oveq2i.mm"
include "ax-icn.mm"
include "mulid1i.mm"
include "3eqtrri.mm"

theorem sqrtm1



  assert |- _i = ( sqrt ` -u 1 )

  proof
    c1
    cneg
    csqrt
    cfv
    #
    ci
    c1
    csqrt
    cfv
    #
    cmul
    co
    #
    ci
    c1
    cmul
    co
    ci
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @0
    @2
    wceq
    1re
    0le1
    c1
    sqrtneg
    mp2an
    @1
    c1
    ci
    cmul
    sqrt1
    oveq2i
    ci
    ax-icn
    mulid1i
    3eqtrri
end
