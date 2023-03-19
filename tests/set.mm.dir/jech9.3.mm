include "con0.mm"
include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "ciun.mm"
include "crn.mm"
include "cuni.mm"
include "cima.mm"
include "cvv.mm"
include "wfn.mm"
include "wceq.mm"
include "r1fnon.mm"
include "fniunfv.mm"
include "ax-mp.mm"
include "cdm.mm"
include "fndm.mm"
include "imaeq2i.mm"
include "imadmrn.mm"
include "eqtr3i.mm"
include "unieqi.mm"
include "unir1.mm"
include "3eqtr2i.mm"

theorem jech9.3
  let vx: setvar x


  assert |- U_ x e. On ( R1 ` x ) = _V

  proof
    vx
    con0
    vx
    cv
    cr1
    cfv
    ciun
    #
    cr1
    crn
    #
    cuni
    #
    cr1
    con0
    cima
    #
    cuni
    cvv
    cr1
    con0
    wfn
    #
    @0
    @2
    wceq
    r1fnon
    vx
    con0
    cr1
    fniunfv
    ax-mp
    @3
    @1
    cr1
    cr1
    cdm
    #
    cima
    @3
    @1
    @5
    con0
    cr1
    @4
    @5
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    imaeq2i
    cr1
    imadmrn
    eqtr3i
    unieqi
    unir1
    3eqtr2i
end
