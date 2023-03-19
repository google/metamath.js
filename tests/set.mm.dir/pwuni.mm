include "cuni.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "elssuni.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"

theorem pwuni
  let cA: class A
  let vx: setvar x


  assert |- A C_ ~P U. A

  proof
    vx
    cA
    cA
    cuni
    #
    cpw
    #
    vx
    cv
    #
    cA
    wcel
    @2
    @0
    wss
    @2
    @1
    wcel
    @2
    cA
    elssuni
    vx
    @0
    selpw
    sylibr
    ssriv
end
