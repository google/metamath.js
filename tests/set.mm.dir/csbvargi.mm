include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "csbvarg.mm"
include "ax-mp.mm"

theorem csbvargi
  let vx: setvar x
  let cA: class A
  assume csbvargi.1: |- A e. _V


  assert |- [_ A / x ]_ x = A

  proof
    cA
    cvv
    wcel
    vx
    cA
    vx
    cv
    csb
    cA
    wceq
    csbvargi.1
    vx
    cA
    cvv
    csbvarg
    ax-mp
end
