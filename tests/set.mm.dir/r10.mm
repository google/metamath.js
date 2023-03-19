include "c0.mm"
include "cr1.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "cpw.mm"
include "cmpt.mm"
include "crdg.mm"
include "df-r1.mm"
include "fveq1i.mm"
include "0ex.mm"
include "rdg0.mm"
include "eqtri.mm"

theorem r10
  let vx: setvar x


  assert |- ( R1 ` (/) ) = (/)

  proof
    c0
    cr1
    cfv
    c0
    vx
    cvv
    vx
    cv
    cpw
    cmpt
    #
    c0
    crdg
    #
    cfv
    c0
    c0
    cr1
    @1
    vx
    df-r1
    fveq1i
    c0
    @0
    0ex
    rdg0
    eqtri
end
