include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "csbconstg.mm"
include "ax-mp.mm"

theorem csbconstgi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume csbconstgi.1: |- A e. _V

  disjoint x y
  assert |- [_ A / x ]_ y = y

  proof
    cA
    cvv
    wcel
    vx
    cA
    vy
    cv
    #
    csb
    @0
    wceq
    csbconstgi.1
    vx
    cA
    @0
    cvv
    csbconstg
    ax-mp
end
