include "cr.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wa.mm"
include "sinbnd.mm"
include "resincl.mm"
include "1red.mm"
include "absled.mm"
include "mpbird.mm"

theorem abssinbd
  let cA: class A


  assert |- ( A e. RR -> ( abs ` ( sin ` A ) ) <_ 1 )

  proof
    cA
    cr
    wcel
    #
    cA
    csin
    cfv
    #
    cabs
    cfv
    c1
    cle
    wbr
    c1
    cneg
    @1
    cle
    wbr
    @1
    c1
    cle
    wbr
    wa
    cA
    sinbnd
    @0
    @1
    c1
    cA
    resincl
    @0
    1red
    absled
    mpbird
end
