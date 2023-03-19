include "crdg.mm"
include "wfun.mm"
include "cdm.mm"
include "wlim.mm"
include "cvv.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "df-rdg.mm"
include "tfr1a.mm"
include "simpri.mm"

theorem rdgdmlim
  let cA: class A
  let cF: class F
  let vg: setvar g


  assert |- Lim dom rec ( F , A )

  proof
    cF
    cA
    crdg
    #
    wfun
    @0
    cdm
    wlim
    @0
    vg
    cvv
    vg
    cv
    #
    c0
    wceq
    cA
    @1
    cdm
    #
    wlim
    @1
    crn
    cuni
    @2
    cuni
    @1
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
    tfr1a
    simpri
end
