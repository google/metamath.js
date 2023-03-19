include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "cvv.mm"
include "wcel.mm"
include "brdomi.mm"
include "cdm.mm"
include "f1dm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "exlimiv.mm"
include "syl.mm"

theorem ctex
  let cA: class A
  let vf: setvar f


  assert |- ( A ~<_ _om -> A e. _V )

  proof
    cA
    com
    cdom
    wbr
    cA
    com
    vf
    cv
    #
    wf1
    #
    vf
    wex
    cA
    cvv
    wcel
    #
    cA
    com
    vf
    brdomi
    @1
    @2
    vf
    @1
    cA
    @0
    cdm
    cvv
    cA
    com
    @0
    f1dm
    @0
    vf
    vex
    dmex
    syl6eqelr
    exlimiv
    syl
end
