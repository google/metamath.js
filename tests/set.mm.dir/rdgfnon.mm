include "crdg.mm"
include "cvv.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "wlim.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "df-rdg.mm"
include "tfr1.mm"

theorem rdgfnon
  let cA: class A
  let cF: class F
  let vg: setvar g


  assert |- rec ( F , A ) Fn On

  proof
    cF
    cA
    crdg
    vg
    cvv
    vg
    cv
    #
    c0
    wceq
    cA
    @0
    cdm
    #
    wlim
    @0
    crn
    cuni
    @1
    cuni
    @0
    cfv
    cF
    cfv
    cif
    cif
    cmpt
    vg
    cF
    cA
    df-rdg
    tfr1
end
