include "cv.mm"
include "wss.mm"
include "cvv.mm"
include "crab.mm"
include "cint.mm"
include "cab.mm"
include "rabab.mm"
include "inteqi.mm"
include "wcel.mm"
include "wceq.mm"
include "intmin.mm"
include "ax-mp.mm"
include "eqtr3i.mm"

theorem intmin2
  let vx: setvar x
  let cA: class A
  assume intmin2.1: |- A e. _V

  disjoint A x
  assert |- |^| { x | A C_ x } = A

  proof
    cA
    vx
    cv
    wss
    #
    vx
    cvv
    crab
    #
    cint
    #
    @0
    vx
    cab
    #
    cint
    cA
    @1
    @3
    @0
    vx
    rabab
    inteqi
    cA
    cvv
    wcel
    @2
    cA
    wceq
    intmin2.1
    vx
    cA
    cvv
    intmin
    ax-mp
    eqtr3i
end
