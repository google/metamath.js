include "cv.mm"
include "cfuns.mm"
include "wcel.mm"
include "wfun.mm"
include "eleq1.mm"
include "funeq.mm"
include "vex.mm"
include "elfuns.mm"
include "vtoclbg.mm"

theorem elfunsg
  let cF: class F
  let cV: class V
  let vf: setvar f


  assert |- ( F e. V -> ( F e. Funs <-> Fun F ) )

  proof
    vf
    cv
    #
    cfuns
    wcel
    @0
    wfun
    cF
    cfuns
    wcel
    cF
    wfun
    vf
    cF
    cV
    @0
    cF
    cfuns
    eleq1
    @0
    cF
    funeq
    @0
    vf
    vex
    elfuns
    vtoclbg
end
