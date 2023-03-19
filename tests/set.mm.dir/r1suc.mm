include "csuc.mm"
include "cr1.mm"
include "cfv.mm"
include "cpw.mm"
include "wceq.mm"
include "cdm.mm"
include "con0.mm"
include "r1sucg.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "eleq2s.mm"

theorem r1suc
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. On -> ( R1 ` suc A ) = ~P ( R1 ` A ) )

  proof
    cA
    csuc
    cr1
    cfv
    cA
    cr1
    cfv
    cpw
    wceq
    cA
    cr1
    cdm
    #
    con0
    cA
    r1sucg
    @0
    con0
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
    eqcomi
    eleq2s
end
