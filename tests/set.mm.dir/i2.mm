include "ci.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "cneg.mm"
include "ax-icn.mm"
include "sqvali.mm"
include "ixi.mm"
include "eqtri.mm"

theorem i2



  assert |- ( _i ^ 2 ) = -u 1

  proof
    ci
    c2
    cexp
    co
    ci
    ci
    cmul
    co
    c1
    cneg
    ci
    ax-icn
    sqvali
    ixi
    eqtri
end
