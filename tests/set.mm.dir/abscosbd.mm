include "cr.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wa.mm"
include "cosbnd.mm"
include "recoscl.mm"
include "1red.mm"
include "absled.mm"
include "mpbird.mm"

theorem abscosbd
  let cA: class A


  assert |- ( A e. RR -> ( abs ` ( cos ` A ) ) <_ 1 )

  proof
    cA
    cr
    wcel
    #
    cA
    ccos
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
    cosbnd
    @0
    @1
    c1
    cA
    recoscl
    @0
    1red
    absled
    mpbird
end
