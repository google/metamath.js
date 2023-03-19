include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "wceq.mm"
include "pwss.mm"
include "setind.mm"
include "sylbi.mm"

theorem setind2
  let cA: class A
  let vx: setvar x


  assert |- ( ~P A C_ A -> A = _V )

  proof
    cA
    cpw
    cA
    wss
    vx
    cv
    #
    cA
    wss
    @0
    cA
    wcel
    wi
    vx
    wal
    cA
    cvv
    wceq
    vx
    cA
    cA
    pwss
    vx
    cA
    setind
    sylbi
end
