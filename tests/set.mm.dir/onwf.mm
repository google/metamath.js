include "con0.mm"
include "cr1.mm"
include "cdm.mm"
include "cima.mm"
include "cuni.mm"
include "wfn.mm"
include "wceq.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "cv.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "rankonidlem.mm"
include "simpld.mm"
include "ssriv.mm"
include "eqsstr3i.mm"

theorem onwf
  let vx: setvar x


  assert |- On C_ U. ( R1 " On )

  proof
    con0
    cr1
    cdm
    #
    cr1
    con0
    cima
    cuni
    #
    cr1
    con0
    wfn
    @0
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    vx
    @0
    @1
    vx
    cv
    #
    @0
    wcel
    @2
    @1
    wcel
    @2
    crnk
    cfv
    @2
    wceq
    @2
    rankonidlem
    simpld
    ssriv
    eqsstr3i
end
