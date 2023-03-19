include "cr.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cre.mm"
include "recosval.mm"
include "cc.mm"
include "ax-icn.mm"
include "recn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efcl.mm"
include "syl.mm"
include "recld.mm"
include "eqeltrd.mm"

theorem recoscl
  let cA: class A


  assert |- ( A e. RR -> ( cos ` A ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cA
    ccos
    cfv
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    cre
    cfv
    cr
    cA
    recosval
    @0
    @2
    @0
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    @0
    ci
    cc
    wcel
    cA
    cc
    wcel
    @3
    ax-icn
    cA
    recn
    ci
    cA
    mulcl
    sylancr
    @1
    efcl
    syl
    recld
    eqeltrd
end
