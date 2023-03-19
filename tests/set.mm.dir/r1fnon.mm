include "cr1.mm"
include "con0.mm"
include "wfn.mm"
include "cvv.mm"
include "cv.mm"
include "cpw.mm"
include "cmpt.mm"
include "c0.mm"
include "crdg.mm"
include "rdgfnon.mm"
include "df-r1.mm"
include "fneq1i.mm"
include "mpbir.mm"

theorem r1fnon
  let vx: setvar x


  assert |- R1 Fn On

  proof
    cr1
    con0
    wfn
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
    con0
    wfn
    c0
    @0
    rdgfnon
    con0
    cr1
    @1
    vx
    df-r1
    fneq1i
    mpbir
end
