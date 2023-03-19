include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "cpw.mm"
include "wcel.mm"
include "cvv.mm"
include "vex.mm"
include "elpwpw.mm"
include "mpbiran.mm"
include "abbi2i.mm"

theorem pwpwab
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ~P ~P A = { x | U. x C_ A }

  proof
    vx
    cv
    #
    cuni
    cA
    wss
    #
    vx
    cA
    cpw
    cpw
    #
    @0
    @2
    wcel
    @0
    cvv
    wcel
    @1
    vx
    vex
    @0
    cA
    elpwpw
    mpbiran
    abbi2i
end
